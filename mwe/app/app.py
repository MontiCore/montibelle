#!/usr/bin/env python3
# pylint: disable=maybe-no-member
# pylint: max-line-length=80
import json
import sys

from kubernetes import config
from flask import Flask
from extensions import bootstrap, db, login_manager, init_kube_clients
from models.user import User
from routes.admin import admin_panel
from routes.auth import index, login, logout
from routes.instances import (
  instance_state,
  keep_alive,
  userinstance,
  userinstance_codeserver,
  userinstance_preparing,
  userinstance_reset,
)
from services.instance_service import create_missing_routes
from utils import init_log, get_log


app = Flask(__name__, template_folder="res/html/", static_folder="res/static/")
app.config.from_file("config.json", load=json.load)

init_log(app)
get_log().debug(f'Starting "{app.name}" in development mode')

db.init_app(app)
login_manager.init_app(app)
login_manager.login_view = 'login'
get_log().debug(f'Configured login_manager')

bootstrap.init_app(app)
get_log().debug(f'Using bootstrap')

try:
  config.load_incluster_config()
  init_kube_clients()
  get_log().debug(f'Detected cluster usage')
except BaseException:
  try:
    config.load_kube_config()
    init_kube_clients()
    get_log().debug(f'Detected local usage')
  except BaseException:
    get_log().exception('Failed to load kube config. Right kubernetes version?')
    sys.exit(1)

db.create_all()

@login_manager.user_loader
def load_user(user_id):
  return User.query.get(int(user_id))

app.route("/")(index)
app.route("/login", methods=["GET", "POST"])(login)
app.route("/logout")(logout)
app.route("/admin", methods=["GET", "POST"])(admin_panel)
app.route("/keepAlive")(keep_alive)
app.route("/userinstance")(userinstance)
app.route("/userinstance/<deployment_name>")(userinstance_codeserver)
app.route("/userinstance/<deployment_name>/reset")(userinstance_reset)
app.route("/userinstance/<deployment_name>/preparing")(userinstance_preparing)
app.route("/instance_state")(instance_state)

create_missing_routes()
get_log().debug(f'Created missing routes')

if __name__ == '__main__':
  get_log().debug(f'Staring app now')
  app.run(debug=True, host="0.0.0.0", port=app.config["PORT"])
  get_log().debug(f'Started app')
