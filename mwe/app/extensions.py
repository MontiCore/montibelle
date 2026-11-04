from flask_bootstrap import Bootstrap
from flask_login import LoginManager
from flask_sqlalchemy import SQLAlchemy
from kubernetes import client


db = SQLAlchemy()
login_manager = LoginManager()
bootstrap = Bootstrap()
appsClient = None
coreClient = None
jobsClient = None
networkingClient = None


def init_kube_clients():
  global appsClient, coreClient, jobsClient, networkingClient
  appsClient = client.AppsV1Api()
  coreClient = client.CoreV1Api()
  jobsClient = client.BatchV1Api()
  networkingClient = client.NetworkingV1Api()
