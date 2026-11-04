import extensions

from kubernetes import client
from kubernetes.client import ApiException

from utils import get_log

def create_instance_route(deployment_name):
  """
  Adds a path for a deployment to the ingress.
  """
  namespace = "default"
  ingress_name = "montibelle-ingress"

  new_service_name = deployment_name + "-service"
  new_path = f'/instances/{deployment_name}(/|$)(.*)'

  try:
    ingress = extensions.networkingClient.read_namespaced_ingress(
      namespace=namespace, name=ingress_name)
  except ApiException as e:
    if e.status == 404:
      raise RuntimeError(f"Ingress '{ingress_name}' not found in "
               f"namespace '{namespace}'")
    else:
      raise

  if ingress.spec.rules is None:
    ingress.spec.rules = []

  rule = None
  if ingress.spec.rules is not None and len(ingress.spec.rules) > 0:
    rule = ingress.spec.rules[0]

  if rule is None:
    rule = client.V1IngressRule(
      host=None,
      http=client.V1HTTPIngressRuleValue(paths=[])
    )
    ingress.spec.rules.append(rule)

  if rule.http is None:
    rule.http = client.V1HTTPIngressRuleValue(paths=[])

  service_exists = any(
    p.backend and
    p.backend.service and
    p.backend.service.name == new_service_name
    for p in rule.http.paths
  )

  if not service_exists:
    new_path_obj = client.V1HTTPIngressPath(
      path_type="ImplementationSpecific",
      path=new_path,
      backend=client.V1IngressBackend(
        service=client.V1IngressServiceBackend(
          name=new_service_name,
          port=client.V1ServiceBackendPort(number=80)
        )
      )
    )
    rule.http.paths.append(new_path_obj)
    get_log().info(f"✅ Added new backend: {new_service_name} at path"
                   f" {new_path}")
  else:
    get_log().warn(f"⚠️ Backend '{new_service_name}' already in ingress")

  extensions.networkingClient.patch_namespaced_ingress(
    name=ingress_name,
    namespace=namespace,
    body=ingress
  )

  get_log().info("✅ Ingress updated successfully")


def delete_instance_route(deployment_name):
  """
  Deletes the path for a deployment from the ingress.
  """
  patches = list()
  paths = extensions.networkingClient.read_namespaced_ingress(
    namespace="default", name="montibelle-ingress").spec.rules[0].http.paths

  paths = list(filter(lambda path: path.backend.service.name !=
                  deployment_name + "-service", paths))

  patch = dict()
  patch["op"] = "replace"
  patch["path"] = "/spec/rules/0/http/paths"
  patch["value"] = paths

  patches.append(patch)

  extensions.networkingClient.patch_namespaced_ingress(
    namespace="default", name="montibelle-ingress", body=patches)
