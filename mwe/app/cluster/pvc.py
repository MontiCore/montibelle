import yaml
import extensions
from kubernetes import client

from utils import get_random_string


class PersistentVolumeClaim():
  data = None

  def __init__(self, name):
    self.update_data(name)


  def update_data(self, name):
    self.data = extensions.coreClient.read_namespaced_persistent_volume_claim(
      name=name, namespace="default")


  def get_ownerid(self):
    return self.data.metadata.labels.get("ownerid")


  def get_name(self):
    return self.data.metadata.name


  def delete(self):
    try:
      extensions.coreClient.delete_namespaced_persistent_volume_claim(
        self.get_name(), "default")
    except client.exceptions.ApiException as ex:
      return None, ex.status


  @staticmethod
  def create(ownerid, stack=None):
    try:
      with open("res/k8s/userStorageClaim.yml") as file:
        data = yaml.safe_load(file)
        name = "code-server-pvc-" + get_random_string(5)
        data["metadata"]["name"] = name
        data["metadata"].setdefault("labels", {})
        data["metadata"]["labels"]["ownerid"] = str(ownerid)
        if stack:
          data["metadata"]["labels"]["stack"] = stack

        extensions.coreClient.create_namespaced_persistent_volume_claim(
          namespace="default", body=data)

        return PersistentVolumeClaim(name), 0

    except client.exceptions.ApiException as ex:
      return None, ex.status


  @staticmethod
  def get_all():
    try:
      raw_pvcs = extensions.coreClient.list_namespaced_persistent_volume_claim(
        "default").items

      pvcs = list(map(
        lambda raw_pvc: PersistentVolumeClaim(raw_pvc.metadata.name),
        raw_pvcs,
      ))

      return pvcs, 0
    except client.exceptions.ApiException as ex:
      return list(), ex.status


  @staticmethod
  def get_by_owner(ownerid):
    pvcs, code = PersistentVolumeClaim.get_all()
    if code:
      return list(), code

    pvcs = list(filter(lambda pvc: pvc.get_ownerid() == ownerid, pvcs))

    return pvcs, 0

  def get_stack(self):
    labels = self.data.metadata.labels if self.data and self.data.metadata else {}
    return labels.get("stack") if labels else None

  def is_terminating(self):
    return bool(
      self.data
      and self.data.metadata
      and self.data.metadata.deletion_timestamp
    )


  @staticmethod
  def get_by_owner_and_stack(ownerid, stack):
    pvcs, code = PersistentVolumeClaim.get_all()
    if code:
      return list(), code

    pvcs = list(filter(
      lambda pvc: (
        pvc.get_ownerid() == ownerid
        and pvc.get_stack() == stack
        and not pvc.is_terminating()
      ),
      pvcs,
    ))

    return pvcs, 0
