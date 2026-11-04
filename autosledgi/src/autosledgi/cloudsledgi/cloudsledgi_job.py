import logging
import random
import os
import abc
from enum import Enum

from kubernetes.client import *
from kubernetes import watch, client as kclient

from autosledgi.cloudsledgi import s3, get_k8s_client
from autosledgi.isabelle.utils import get_roots_refs

import autosledgi.cloudsledgi as c

logger = logging.getLogger("cloudsledgi")


class CloudsledgiJobStatus(Enum):
    """
    Enum class to interpret the state of a Cloudsledgi job.
    """
    NOT_SUBMITTED = 0
    SUBMITTED = 1
    PENDING = 2
    RUNNABLE = 3
    STARTING = 4
    RUNNING = 5
    SUCCEEDED = 6
    FAILED = 7
    UNKNOWN = 8

    def __str__(self):
        return self.name

    def isFinished(self):
        return (self.value == CloudsledgiJobStatus.FAILED.value) or (self.value == CloudsledgiJobStatus.SUCCEEDED.value)


class CloudsledgiJob:
    """
    Used to create a Batch job that executes a given Autosledgi task
    """
    __metaclass__ = abc.ABCMeta
    _jid: str = None
    _sid: str = None

    args = None
    usePrebuiltPSL = True

    def __init__(self, args, sid: str = None, jid: str = None):
        self.args = args
        self._sid = sid
        self._jid = jid
        s3.init()

    def upload_files(self):
        """
        Upload all files required to execute Autosledgi on Batch to AWS S3 storage.
        """

        if self._sid is None:
            self._sid = str(CloudsledgiJob.get_free_autosledgi_sourceid())

            session_directories = self.args.session_directories

            if session_directories is None:
                session_directories = []

            self.args.theorypath = os.path.abspath(self.args.theorypath)

            upload_dirs = set()

            if os.path.isfile(self.args.theorypath) and self.args.theorypath.endswith('.thy'):
                upload_dirs.add(os.path.dirname(self.args.theorypath))
            elif os.path.isdir(self.args.theorypath):
                upload_dirs.add(self.args.theorypath)
            else:
                raise Exception("Theory path must be .thy file or folder containing theory files.")

            for dir in session_directories:
                upload_dirs = upload_dirs.union(get_roots_refs(dir, top_only=True))

            for dir in upload_dirs:
                prefix = os.path.normpath(f"theories/{self._sid}/{dir}")
                s3.s3_put(source=dir, prefix=prefix, exclude_extension=[".log", ".json"])

            return self._sid

    def download_results(self, deleteAfterPull=True, target="/", prefix=None):
        '''
        If the underlaying Batch job is finished this method can be used to download the results.
        deleteAfterPull(Bool): When set the results will be deleted on S3 to save storage. Defaults to True.
        '''
        if not prefix:
            prefix = f"results/{self._jid}/"

        if self.get_batch_status().isFinished():
            logger.info(f"Downloading results for job {self._jid}..")
            s3.s3_pull(prefix=prefix,
                       target=target, delete_after_pull=deleteAfterPull)
            logger.info(f"Downloaded all files!")
            return True
        else:
            logger.warning(
                "Cannot download results as job is not yet finished.")
            return False

    def get_jobid(self):
        return self._jid

    def get_source_id(self):
        return self._sid

    def _get_remote_command(self, usePrebuiltPSL=False):
        command = list()
        command.append("prove")

        command.append("-t")
        command.append(str(self.args.timeout))

        if self.args.sledge_timeout:
            command.append("-st")
            command.append(str(self.args.sledge_timeout))

        if self.args.session:
            command.append("-s")
            command.append(self.args.session)

        for d in self.args.session_directories:
            d = os.path.normpath("/s3/" + os.path.abspath(d))
            command.append("-d")
            command.append(d)

        if usePrebuiltPSL:
            command.append("-d")
            command.append("/home/isabelle/lib/PSL")

        if self.args.provers:
            command.append("--provers")
            command.append(self.args.provers)

        if self.args.recursive:
            command.append("-r")

        target = os.path.normpath("/s3/" + self.args.theorypath)
        command.append(target)

        command.append("--log_dir")
        if os.path.isfile(self.args.theorypath) and self.args.theorypath.endswith('.thy'):
            command.append(os.path.dirname(os.path.normpath("/s3/" + self.args.theorypath)))
        elif os.path.isdir(self.args.theorypath):
            command.append(os.path.normpath("/s3/" + self.args.theorypath))
        else:
            raise Exception("Theory path must be .thy file or folder containing theory files.")

        return command

    def _get_job_envs(self):
        envs = list()
        envs.append({"name": "CLOUD_SOURCE_ID", "value": self._sid})

        if c.S3_ENDPOINT and c.S3_ACCESS_KEY and c.S3_SECRET_KEY:
            envs.append({"name": "AS_S3_ENDPOINT", "value": c.S3_ENDPOINT})
            envs.append({"name": "AS_S3_ACCESS_KEY", "value": c.S3_ACCESS_KEY})
            envs.append({"name": "AS_S3_SECRET_KEY", "value": c.S3_SECRET_KEY})

        return envs

    @classmethod
    @abc.abstractmethod
    def run(self, resubmit=False):
        raise NotImplementedError("Implement in super class")

    @classmethod
    @abc.abstractmethod
    def get_batch_status(self):
        raise NotImplementedError("Implement in super class")

    @classmethod
    @abc.abstractmethod
    def get_log_messages(self):
        raise NotImplementedError("Implement in super class")

    @staticmethod
    def get_free_autosledgi_sourceid():
        '''
        Will generate a source id that is not used by AWS S3.
        '''
        id = random.randrange(10000000, 100000000)
        while s3.s3_prefix_exists(prefix=f"theories/{id}"):
            id = random.randrange(10000000, 100000000)

        return id

    @classmethod
    @abc.abstractmethod
    def kill(self):
        raise NotImplementedError("Implement in super class")


class K8sCloudsledgiJob(CloudsledgiJob):

    def __init__(self, args, sid: str = None, jid: str = None):
        super().__init__(args, sid=sid, jid=jid)

    @staticmethod
    def get_free_k8s_jobid():
        '''
        Will generate a source id that is not used by AWS S3.
        '''
        id = random.randrange(10000000, 100000000)
        while s3.s3_prefix_exists(prefix=f"results/cj-{id}"):
            id = random.randrange(10000000, 100000000)

        return f"cj-{id}"

    def get_batch_status(self) -> CloudsledgiJobStatus:
        """
        Get the current job state.
        """
        try:
            if self._jid:
                client = kclient.BatchV1Api(get_k8s_client())
                core_client = kclient.CoreV1Api(get_k8s_client())
                status_return: V1JobStatus = client.read_namespaced_job_status(name=self._jid, namespace="cloudsledgi").status
                status_return_pod: V1PodStatus = core_client.read_namespaced_pod_status(name=self.__get_pod_name(), namespace="cloudsledgi").status

                if status_return.active:
                    if status_return_pod.phase.lower() == "pending":
                        return CloudsledgiJobStatus.PENDING

                    return CloudsledgiJobStatus.RUNNING

                elif status_return.succeeded:
                    return CloudsledgiJobStatus.SUCCEEDED

                elif status_return.failed:
                    return CloudsledgiJobStatus.FAILED

                else:
                    return CloudsledgiJobStatus.PENDING

            else:
                return CloudsledgiJobStatus.NOT_SUBMITTED

        except Exception as ex:
            logger.debug(ex)
            return CloudsledgiJobStatus.UNKNOWN

    def __get_pod_name(self):
        batch_client = BatchV1Api(get_k8s_client())
        job_def = batch_client.read_namespaced_job(self.get_jobid(), "cloudsledgi")
        controllerUid = job_def.metadata.labels["controller-uid"]
        core_client = CoreV1Api(get_k8s_client())

        pod_label_selector = "controller-uid=" + controllerUid
        pods_list = core_client.list_namespaced_pod(
            namespace="cloudsledgi", label_selector=pod_label_selector)

        pod_name = pods_list.items[0].metadata.name
        return pod_name

    def get_log_messages(self):
        """
        Get the log messages of the underlaying Batch job. Will only contain messages when the job is finished.
        """
        if self.get_batch_status().isFinished():
            core_client = CoreV1Api(get_k8s_client())
            pod_name = self.__get_pod_name()

            try:
                pod_log_response = core_client.read_namespaced_pod_log(
                    name=pod_name, namespace="cloudsledgi")

                return pod_log_response.split("\n")

            except Exception as ex:
                logger.error(ex)

            return list()

        else:
            return list()

    def follow_log(self):
        if self.get_batch_status() == CloudsledgiJobStatus.RUNNING:
            w = watch.Watch()
            core_client = CoreV1Api(get_k8s_client())
            for line in w.stream(core_client.read_namespaced_pod_log, name=self.__get_pod_name(), namespace='cloudsledgi'):
                yield line


    def _get_job_envs(self):
        envs = super()._get_job_envs()
        envs.append({"name": "K8S_JOB_ID", "value": self.get_jobid()})
        return envs

    def get_jobid(self):
        if not self._jid:
            self._jid = K8sCloudsledgiJob.get_free_k8s_jobid()

        return self._jid

    def kill(self):
        if self._jid:
            try:
                client = kclient.BatchV1Api(get_k8s_client())
                core_client = CoreV1Api(get_k8s_client())
                pod_name = self.__get_pod_name()
                client.delete_namespaced_job(namespace="cloudsledgi", name=self._jid)
                core_client.delete_namespaced_pod(namespace="cloudsledgi", name=pod_name)

                return True
            except Exception as ex:
                logger.error(ex)
                return False
        else:
            return True

    def run(self, resubmit=False):
        """
        Submit the job.
        """
        if self._jid and not resubmit:
            logger.warning("Job already submitted. (Skip)")
            return False

        if self._sid:
            logger.debug("Source id set -> Skipping upload..")
        else:
            logger.info("No source id set. Uploading sources now..")
            self.upload_files()

        client = kclient.BatchV1Api(get_k8s_client())

        envs = list()
        for env in self._get_job_envs():
            envs.append(V1EnvVar(name=env["name"], value=env["value"]))
        containers = list()


        resources = dict()
        if c.JOB_MEMORY:
            resources["memory"] = str(c.JOB_MEMORY) + "Mi"
            resources["memory"] = str(c.JOB_MEMORY) + "Mi"

        if c.JOB_VCPUS:
            resources["cpu"] = str(c.JOB_VCPUS * 1000) + "m"
            resources["cpu"] = str(c.JOB_VCPUS * 1000) + "m"

        resourceReq: V1ResourceRequirements = V1ResourceRequirements(requests=resources, limits=resources)

        container = V1Container(
            name="autosledgi",
            image=c.AS_CLOUD_IMAGE,
            args=self._get_remote_command(),
            image_pull_policy="Always",
            resources=resourceReq,
            env=envs
        )

        containers.append(container)

        body = kclient.V1Job()
        body.metadata = V1ObjectMeta(name=self.get_jobid(), namespace="cloudsledgi")
        body.spec = V1JobSpec(template=V1JobTemplateSpec(
            spec=V1PodSpec(
                security_context=V1PodSecurityContext(fs_group=1000),
                containers=containers,
                restart_policy="Never",
                image_pull_secrets=[V1LocalObjectReference(name="cloudsledgi-image-pull")])),
            backoff_limit=3,
            ttl_seconds_after_finished=60*60,
            active_deadline_seconds=60*60
        )

        client.create_namespaced_job("cloudsledgi", body)
