import yaml
import extensions
from kubernetes import client
from passlib.hash import argon2

from cluster.ingress import (
  create_instance_route,
  delete_instance_route,
)
from cluster.pvc import PersistentVolumeClaim
from cluster.service import create_instance_service, delete_instance_service
from utils import get_random_string


class CodeServerDeployment:
  __deploymentData = None


  def __init__(self, deployment_name):
    self.__deploymentData = extensions.appsClient.read_namespaced_deployment(
      namespace="default", name=deployment_name)


  def __update(self):
    try:
      self.__deploymentData = extensions.appsClient.read_namespaced_deployment(
        namespace="default", name=self.name())
      return True
    except BaseException:
      return False


  def status(self):
    for pod in extensions.coreClient.list_namespaced_pod("default").items:
      if not pod.metadata.name.startswith(self.name()):
        continue

      status = extensions.coreClient.read_namespaced_pod(
        namespace="default", name=pod.metadata.name)

      return status.status.phase


  def name(self):
    if not self.__deploymentData:
      self.__update()
    return self.__deploymentData.metadata.name


  def labels(self):
    self.__update()
    return self.__deploymentData.metadata.labels


  def set_label(self, key, value):
    patches = list()
    labels = self.__deploymentData.metadata.labels
    labels[key] = value

    patch = dict()
    patch["op"] = "replace"
    patch["path"] = "/metadata/labels"
    patch["value"] = labels

    patches.append(patch)

    extensions.appsClient.patch_namespaced_deployment(
      namespace="default", name=self.name(), body=patches)


  def is_owner(self, userid: str):
    return self.labels().get("ownerid") == userid


  def creation_time(self):
    return self.__deploymentData.metadata.creation_timestamp


  def hashed_password(self):
    containers = self.__deploymentData.spec.template.spec.containers

    container = list(
      filter(lambda c: c.name == "code-server", containers))[0]

    return "montibelle"


  def create_service(self):
    return create_instance_service(self.name())


  def delete_service(self):
    return delete_instance_service(self.name())


  def create_route(self):
    return create_instance_route(self.name())


  def delete_route(self):
    return delete_instance_route(self.name())


  def set_porject_folder_empty_dir(self):
    name = self.name()
    patches = list()
    volumes = extensions.appsClient.read_namespaced_deployment(
      namespace="default", name=name).spec.template.spec.volumes


    volumes = list(filter(lambda v: v.name != "user-storage", volumes))
    volumes.append(client.V1Volume(name="user-storage", empty_dir={}))

    patch = dict()
    patch["op"] = "replace"
    patch["path"] = "/spec/template/spec/volumes"
    patch["value"] = volumes

    patches.append(patch)

    print(extensions.appsClient.patch_namespaced_deployment(
      namespace="default", name=name, body=patches))


  def set_project_folder_pvc(self, pvc: PersistentVolumeClaim):
    name = self.name()
    patches = list()
    volumes = extensions.appsClient.read_namespaced_deployment(
      namespace="default", name=name).spec.template.spec.volumes

    volumes = list(filter(lambda v: v.name != "user-storage", volumes))
    volumes.append(client.V1Volume(
      name="user-storage",
      persistent_volume_claim={"claimName": pvc.get_name()},
    ))

    patch = dict()
    patch["op"] = "replace"
    patch["path"] = "/spec/template/spec/volumes"
    patch["value"] = volumes

    patches.append(patch)

    extensions.appsClient.patch_namespaced_deployment(
      namespace="default", name=name, body=patches)


  def get_project_pvc(self):
    volumes = self.__deploymentData.spec.template.spec.volumes
    volume = None

    for v in volumes:
      if v.name == "user-storage":
        volume = v

    if volume:
      claim_name = volume.persistent_volume_claim.claim_name
      print(claim_name)
      return PersistentVolumeClaim(claim_name)

    else:
      return None


  def delete(self):
    self.delete_route()
    self.delete_service()
    CodeServerDeployment.delete_by_name(self.name())


  @staticmethod
  def get_all():
    try:
      deployments_raw = extensions.appsClient.list_namespaced_deployment(
        "default")
      code_deployments_raw = filter(
        lambda d: d.metadata.labels and
        d.metadata.labels.get("service") == "code-server",
        deployments_raw.items)

      code_servers = list(map(lambda d: CodeServerDeployment(
        d.metadata.name), code_deployments_raw))

      return code_servers, 0

    except client.exceptions.ApiException as ex:
      return None, ex.status


  @staticmethod
  def get_by_name(name):
    deployments, code = CodeServerDeployment.get_all()
    if code:
      return None

    deployments = list(filter(lambda d: d.name() == name, deployments))

    if len(deployments) > 0:
      return deployments[0]
    else:
      return None


  @staticmethod
  def get_by_owner(ownerid):
    deployments, code = CodeServerDeployment.get_all()
    if code:
      return None

    deployments = list(filter(lambda d: d.is_owner(ownerid), deployments))

    return deployments


  @staticmethod
  def delete_by_name(name):
    try:
      extensions.appsClient.delete_namespaced_deployment(
        namespace="default", name=name)
    except client.exceptions.ApiException as ex:
      return ex.status


  @staticmethod
  def create(ownerid, name=None, hashed_password=None,
       claim: PersistentVolumeClaim = None, stack: str = "space"):
    if not name:
      name = "user-environment-" + get_random_string(length=20)
    if not hashed_password:
      password = get_random_string(length=20)
      hashed_password = argon2.using(
        type="i",
        parallelism=1,
        time_cost=3,
        memory_cost=4096,
      ).hash(password)

    if stack == "space":
      deployment_file = "res/k8s/spaceDeployment.yml"
    elif stack == "inverter":
      deployment_file = "res/k8s/inverterDeployment.yml"
    elif stack == "aero":
      deployment_file = "res/k8s/aeroDeployment.yml"
    elif stack == "it":
      deployment_file = "res/k8s/itDeployment.yml"
    elif stack == "rail":
      deployment_file = "res/k8s/railDeployment.yml"
    elif stack == "auto":
      deployment_file = "res/k8s/autoDeployment.yml"
    else:
      deployment_file = "res/k8s/sysmlDeployment.yml"

    try:
      with open(deployment_file) as file:
        data = yaml.safe_load(file)

        data["metadata"]["name"] = name
        data["metadata"]["labels"]["ownerid"] = ownerid
        data["metadata"].setdefault("labels", {})
        data["metadata"]["labels"]["ownerid"] = ownerid
        data["metadata"]["labels"]["stack"] = stack
        data["spec"]["selector"]["matchLabels"]["app"] = name
        data["spec"]["template"]["metadata"]["labels"]["app"] = name
        data["spec"]["template"]["metadata"]["labels"]["type"] = "user-environment"
        data["spec"]["template"]["metadata"]["labels"]["stack"] = stack

        containers = data["spec"]["template"]["spec"]["containers"]

        container = list(
          filter(lambda c: c["name"] == "code-server", containers))[0]

        if claim:
          volume = {"name": "user-storage",
               "persistentVolumeClaim": {"claimName": claim.get_name()}}
          data["spec"]["template"]["spec"]["volumes"] = list(filter(
            lambda v: v["name"] != "user-storage", data["spec"]["template"]["spec"]["volumes"]))
          data["spec"]["template"]["spec"]["volumes"].append(volume)

        extensions.appsClient.create_namespaced_deployment(
          namespace="default", body=data)

      deployment = CodeServerDeployment(name)
      deployment.create_route()
      deployment.create_service()
      print("created code server")
      return deployment, 0
    except client.exceptions.ApiException as ex:
      print(ex)
      return None, ex.status
