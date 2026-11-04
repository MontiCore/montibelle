import time

from flask import current_app
from cluster.deployment import CodeServerDeployment


def get_stack_title(stack):
  configured_titles = current_app.config.get("STACK_TITLES", {})
  if not isinstance(configured_titles, dict):
    configured_titles = {}

  return configured_titles.get(
    stack,
    configured_titles.get("default", "MontiBelle - SysMLv2Prover"),
  )


def update_heartbeat(instance_id):
  deployments, _ = CodeServerDeployment.get_all()
  deployment = list(filter(lambda d: d.name() == instance_id, deployments))[0]

  deployment.set_label(
    "heartbeat_deadline",
    str(
      round(time.time())
      + int(current_app.config.get("HEARTBEAT_INTERVAL_IN_SECONDS", 60))
    ),
  )


def create_missing_routes():
  """
  In case there are missing routes to running user pods, we add them to
  ingress. This might be the case when Ingress is reset, e.g because of an
  update.
  """
  deployments, code = CodeServerDeployment.get_all()
  if not code:
    for deployment in deployments:
      deployment.create_route()
