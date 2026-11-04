import urllib.parse
from urllib.parse import urlparse

from flask import current_app, make_response, redirect, render_template, request, url_for
from flask_login import current_user, login_required

from cluster.deployment import CodeServerDeployment
from cluster.pvc import PersistentVolumeClaim
from services.instance_service import get_stack_title, update_heartbeat
from services.user_service import is_pro_or_admin


@login_required
def keep_alive():
  """
  Refresh heartbeat for the instance owned by the user with 'id'.
  Validates that the deployment exists and belongs to the
  user before updating its heartbeat timestamp.
  """
  id = request.args.get(key="id", default=None)

  if not id:
    current_app.logger.debug(
      f"[/keepAlive] no instance id provided for call from user{current_user.username}"
    )
    return "Please specify an instance id."

  deployments, code = CodeServerDeployment.get_all()

  if code == 0:
    deployments = list(
      filter(lambda d: d.name() == id and d.is_owner(str(current_user.id)), deployments)
    )
    current_app.logger.debug(
      f"[/keepAlive] {len(deployments)} deployments found for user {str(current_user.id)}"
    )

    if len(deployments) == 1:
      deployment = deployments[0]
      update_heartbeat(deployment.name())
      current_app.logger.debug(
        f"[/keepAlive] updated heartbeat for instance{deployment.name()}"
      )
      return "OK"

    return "Access to instance forbidden or instance could not be identified!"

  current_app.logger.debug(f"[/keepAlive] keppAlive error {code}")
  return "Error: " + code


@login_required
def userinstance():
  """
  Get the users stack-specific code-server instance if it exists.
  If no deployment exists for the user and stack, create a new one.
  """
  userid = str(current_user.id)
  stack = request.args.get("stack", "space")
  current_app.logger.debug(
    f"[/userinstance] User {current_user.username} requested instance with stack {stack}"
  )
  deployments, code = CodeServerDeployment.get_all()
  current_app.logger.debug(f"[/userinstance] Found {len(deployments)} deployments")
  deployment = None

  if code == 0:
    for d in deployments:
      if d.is_owner(userid) and d.labels().get("stack", "space") == stack:
        current_app.logger.debug(
          f"[/userinstance] Found existing deployment {d.name()} for user {current_user.username} with stack {stack}"
        )
        deployment = d
        break
  else:
    current_app.logger.debug(f"[/userinstance] Error {code} while getting deployments")
    return "An error occurred: " + str(code)

  if not deployment:
    persistent_stacks = ["sysml", "inverter"]
    if stack in persistent_stacks and is_pro_or_admin(current_user.username):
      pvcs, _ = PersistentVolumeClaim.get_by_owner_and_stack(userid, stack)
      if len(pvcs) > 0:
        pvc = pvcs[0]
      else:
        pvc = PersistentVolumeClaim.create(userid, stack=stack)[0]
    else:
      pvc = None

    deployment, code = CodeServerDeployment.create(ownerid=userid, claim=pvc, stack=stack)
    current_app.logger.debug(
      f"[/userinstance] Created new deployment {deployment.name()} for user {current_user.username} with stack {stack}"
    )
    if code:
      return "An error occurred: " + str(code)

  return make_response(
    redirect(
      url_for(
        "userinstance_preparing", deployment_name=deployment.name(), stack=stack
      )
    )
  )


@login_required
def userinstance_codeserver(deployment_name):
  """
  Builds template context with instance metadata and access link, and
  sets the code-server session cookie when the deployment is running.
  """
  userid = str(current_user.id)
  deployment = CodeServerDeployment.get_by_name(deployment_name)
  folder = request.args.get("folder")

  if not deployment.is_owner(userid):
    return "forbidden"

  deployment_infos = dict()
  deployment_infos["name"] = deployment.name()
  deployment_infos["password"] = deployment.hashed_password()
  deployment_infos["stack"] = deployment.labels().get("stack", "space")

  deployment_infos["id"] = deployment.name()
  deployment_infos["link"] = (
    f"{current_app.config.get('CLUSTER_ADDRESS', '')}/instances/{deployment.name()}/"
  )
  deployment_infos["status"] = deployment.status()

  if folder:
    deployment_infos["link"] = deployment_infos["link"] + f"?folder={folder}"

  resp = make_response(
    render_template(
      "userInstance.html",
      deployment_infos=deployment_infos,
      stack_title=get_stack_title(deployment_infos["stack"]),
    )
  )

  if deployment.status() == "Running":
    resp.set_cookie(
      key="code-server-session",
      value=urllib.parse.quote(deployment.hashed_password()),
      path=f"/instances/{deployment_name}",
      domain="." + urlparse(request.base_url).hostname,
    )

  return resp


@login_required
def userinstance_reset(deployment_name):
  """
  Allows reset only for supported persistent stacks, deletes the current
  deployment and matching PVC, then redirects to provision a fresh
  instance for the same stack.
  """
  userid = str(current_user.id)
  deployment = CodeServerDeployment.get_by_name(deployment_name)
  current_app.logger.debug(
    f"[/userinstance/<deployment_name>/reset] User {current_user.username} requested reset for instance {deployment_name} with stack {deployment.labels().get('stack', 'space')}"
  )

  if not deployment:
    return "instance not found", 404

  if not deployment.is_owner(userid):
    return "forbidden", 403

  stack = deployment.labels().get("stack", "space")
  if stack not in ["sysml", "inverter"]:
    return "reset is only supported for persistent stacks", 400

  pvcs, code = PersistentVolumeClaim.get_by_owner_and_stack(userid, stack)
  if code:
    return "An error occurred: " + str(code), 500

  deployment.delete()

  if len(pvcs) > 0:
    pvcs[0].delete()

  return redirect(url_for("userinstance", stack=stack))


@login_required
def userinstance_preparing(deployment_name):
  """
  Render the preparing page for an owned deployment instance.
  Builds the deployment based on the deployment template in 
  res/k8s/<deployment>
  """
  stack = request.args.get("stack", "space")
  if not deployment_name:
    return make_response(redirect(url_for("userinstance", stack=stack)))

  userid = str(current_user.id)
  deployment = CodeServerDeployment.get_by_name(deployment_name)
  if not deployment:
    return make_response(redirect(url_for("userinstance", stack=stack)))

  if not deployment.is_owner(userid):
    return "forbidden"

  deployment_infos = dict()
  deployment_infos["name"] = deployment.name()
  deployment_infos["password"] = deployment.hashed_password()

  deployment_infos["id"] = deployment.name()
  deployment_infos["link"] = (
    f"{current_app.config.get('CLUSTER_ADDRESS', '')}/instances/{deployment.name()}/"
  )
  deployment_infos["instanceQuery"] = ""

  open_cloned = bool(request.args.get("openCloned", type=bool, default=False))

  if open_cloned:
    deployment_infos[
      "instanceQuery"
    ] = f"?folder=/home/ive/{deployment.labels().get('lastClonedGitBaseName', '')}"

  deployment_infos["status"] = deployment.status()
  deployment_infos["stack"] = deployment.labels().get("stack", stack)

  current_app.logger.debug(
    f"[/userinstance/<deployment_name>/preparing] Preparing instance {deployment.name()} for user {current_user.username}:"
  )

  return make_response(
    render_template(
      "userInstancePreparing.html",
      deployment_infos=deployment_infos,
      stack_title=get_stack_title(deployment_infos["stack"]),
    )
  )


@login_required
def instance_state():
  """
  Return the runtime status of the instance owned by the user with 'id'.
  The runtime status is the status of the corresponding deployment.
  """
  id = request.args.get(key="id", default=None)

  if not id:
    current_app.logger.debug("[/instance_state] instance_state called without instance id")
    return "Please specify an instance id."

  deployments, code = CodeServerDeployment.get_all()

  if code != 0:
    current_app.logger.debug(
      f"[/instance_state] instance_state error {code} for instance id {id} and user {current_user.username}"
    )
    return "Error " + str(code)

  deployments = list(
    filter(lambda d: d.name() == id and d.is_owner(str(current_user.id)), deployments)
  )

  if len(deployments) == 0:
    current_app.logger.debug(
      f"[/instance_state] instance_state found no deployment for instance id {id} and user {current_user.username}"
    )
    return "Deployment not found."

  if len(deployments) > 1:
    current_app.logger.debug(
      f"[/instance_state] instance_state found multiple deployments for instance id {id} and user {current_user.username}"
    )
    return "Deployment not unique."

  deployment = deployments[0]
  current_app.logger.debug(
    f"[/instance_state] instance_state for instance {deployment.name()} of user {current_user.username} is {deployment.status()}"
  )
  return deployment.status()
