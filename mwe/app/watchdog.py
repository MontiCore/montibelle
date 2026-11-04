#!/usr/bin/env python3
import time

from flask import current_app

from app import app
from cluster.deployment import CodeServerDeployment
from services.instance_service import update_heartbeat
from utils import get_log


if __name__ == '__main__':
  get_log().debug(f'Starting watch dog')
  with app.app_context():
    while True:
      try:
        deployments, _ = CodeServerDeployment.get_all()
        for deployment in deployments:
          ctime = round(time.time())
          labels = deployment.labels()

          if "heartbeat_deadline" not in labels.keys():
            update_heartbeat(deployment.name())

          heartbeat_deadline = int(deployment.labels()["heartbeat_deadline"])

          if heartbeat_deadline < ctime:
            current_app.logger.debug(
              f"No heartbeat from {deployment.name} in "
              + f"{current_app.config.get('HEARTBEAT_INTERVAL_IN_SECONDS', 60)}"
              + f"seconds. Deleting..."
            )
            deployment.delete()
      finally:
        time.sleep(10)
