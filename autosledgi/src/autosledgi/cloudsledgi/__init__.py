import logging
import os
from time import sleep
import shutil

import kubernetes
import botocore.exceptions

'''
The current packaging structure does not allow to import 
other cloudsledgi files here. Instead we import them directly 
in the methods when needed.
'''

S3_BUCKET_NAME = os.getenv("AS_CLOUD_BUCKET", "cloudsledgi")

S3_ENDPOINT = os.getenv("AS_S3_ENDPOINT", None)
S3_ACCESS_KEY = os.getenv("AS_S3_ACCESS_KEY", None)
S3_SECRET_KEY = os.getenv("AS_S3_SECRET_KEY", None)

AS_K8S_ENDPOINT = os.getenv("AS_K8S_ENDPOINT", None)
AS_K8S_TOKEN = os.getenv("AS_K8S_TOKEN", None)

AS_CLOUD_IMAGE = "registry.git.rwth-aachen.de/montibelle/frontend/tooling/autosledgi-python:latest"

JOB_VCPUS = int(os.getenv("AS_CLOUD_CPUS", 0))
JOB_MEMORY = int(os.getenv("AS_CLOUD_RAM", 0))

logger = logging.getLogger('cloudsledgi')


def redirect_to_cloud(args):
    """
    Redirects a autosledgi run to the cloud and monitors it.
    """
    from autosledgi.cloudsledgi.cloudsledgi_job import CloudsledgiJobStatus, K8sCloudsledgiJob

    job = None

    try:

        if AS_K8S_ENDPOINT and AS_K8S_TOKEN:
            job = K8sCloudsledgiJob(args)
        else:
            logger.error(
                "Please set credentials for a Kubernetes cluster using the environment variables AS_K8S_ENDPOINT and AS_K8S_TOKEN.")
            return 13

        container_logger = logging.getLogger("container_logger")
        stream_handler = logging.StreamHandler()
        stream_handler.setFormatter(logging.Formatter("cloudsledgi.job.%(message)s"))
        container_logger.addHandler(stream_handler)

        logger.info("Uploading theories..")
        job.upload_files()
        job.run()

        logger.info("Waiting for cloud job to start.")
        while not job.get_batch_status() == CloudsledgiJobStatus.RUNNING:
            sleep(0.5)

        for line in job.follow_log():
            container_logger.log(21, line)

        status = job.get_batch_status()

        while not status.isFinished():
            status = job.get_batch_status()
            sleep(1)

        if status == CloudsledgiJobStatus.SUCCEEDED:
            job.download_results(deleteAfterPull=False)
        else:
            logger.error("Job failed.")

        return 0
    except botocore.exceptions.NoCredentialsError:
        logger.error("AWS Auth Error. Please provide credentials using awscli.")
        return 13

    except KeyboardInterrupt or InterruptedError:
        if job:
            if job.get_batch_status().value >= CloudsledgiJobStatus.PENDING.value:
                logger.info("Trying to cancel cloud job...")
                if job.kill():
                    logger.info("Cloud job canceled!")
                else:
                    logger.error("Could not cancel cloud job.")

    finally:
        if not job.get_batch_status().isFinished() and not job.get_batch_status() == CloudsledgiJobStatus.UNKNOWN:
            logger.warning("Killing cloud job to avoid 'ghost' jobs that block ressources.")
            job.kill()


def pull_source_from_cloud(sid: str):
    """
    Pulls unproved sources and dependencies from S3.
    sid (str): The source id that identifies the sources to pull.
    """
    from autosledgi.cloudsledgi import s3
    logger.info(f"Initilizing S3")
    s3.init()
    logger.info(f"Pulling cloud sources {sid}..")
    s3.s3_pull(prefix=f"theories/{sid}/", target="/s3")


def push_results_to_cloud(target: str):
    """
    Pushes the solved theory file to S3.
    target (str): The target argument of the autosledgi execution. (Used to find solved files.)
    """
    from autosledgi.cloudsledgi import s3

    folder = ""
    if target.endswith(".thy"):
        folder = os.path.dirname(target)
    else:
        folder = os.path.normpath(target)

    curr_job_id = os.environ.get("AWS_BATCH_JOB_ID", None)
    if not curr_job_id:
        curr_job_id = os.environ.get("K8S_JOB_ID", "NO_JOB_ID")

    logger.info("Pushing results to cloud..")
    s3.s3_put(folder, f"results/{curr_job_id}/", source_name_mapper=lambda
        local_file_name, _: local_file_name[3:])

    logger.info("Removing results from filesystem")
    shutil.rmtree(folder)
    return 0


def get_k8s_client():
    '''    configuration = kubernetes.client.Configuration()

    configuration.host = AS_K8S_ENDPOINT
    configuration.verify_ssl = False
    configuration.api_key = {"authorization": "Bearer " + AS_K8S_TOKEN}

    api_client = kubernetes.client.ApiClient(configuration)'''

    kubernetes.config.load_config()
    api_client = kubernetes.client.ApiClient()

    return api_client
