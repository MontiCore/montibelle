import extensions

from kubernetes import client


def create_instance_service(deployment_name):
  """
  Creates a service for a deployment.
  """
  try:
    service_name = deployment_name + "-service"
    body = client.V1Service(
      api_version="v1",
      kind="Service",
      metadata=client.V1ObjectMeta(
        name=service_name
      ),
      spec=client.V1ServiceSpec(
        selector={"app": deployment_name},
        ports=[client.V1ServicePort(
          port=80
        )]
      )
    )

    extensions.coreClient.create_namespaced_service(
      namespace="default", body=body)
    return service_name
  except client.exceptions.ApiException as ex:
    print("Failed service creation:" + str(ex.status))
    print(ex.reason)
    return ex.status


def delete_instance_service(deployment_name):
  """
  Deletes the service for a deployment.
  """
  try:
    extensions.coreClient.delete_namespaced_service(
      namespace="default", name=deployment_name + "-service")

    return True
  except client.exceptions.ApiException as ex:
    return ex.status
