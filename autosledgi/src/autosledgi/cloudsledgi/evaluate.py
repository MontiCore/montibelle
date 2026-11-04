from enum import Enum
import json
import logging
import os
import matplotlib.pyplot as plt
import numpy as np
import scipy.optimize

from autosledgi.cloudsledgi.cloudsledgi_job import CloudsledgiJob

logger = logging.getLogger("Autosledgi")


def eval(args):
    config = EvaluationConfig(args.config)

    eval = Evaluation(config)

    eval.uploadSource()
    eval.submitJobs()

    logger.info("Waiting for some jobs to finish..")

    isFinished, nFinished, nTotal = eval.isFinished()
    while not isFinished:
        isFinished, nFinished, nTotal = eval.isFinished()
        print(f"\r{nFinished}/{nTotal} finished.", end="", flush=True)
        import time
        time.sleep(2)

    eval.pullResults(repull=False)
    eval.parseResults(reparse=True)

    eval.createImages(multiPointSelectionMethod=MultiPointSelectionMethod.AVERAGE,
                      regressionMethod=RegressionMethod.NO_REGRESSION)
    eval.createImages(multiPointSelectionMethod=MultiPointSelectionMethod.AVERAGE,
                      regressionMethod=RegressionMethod.LINEAR)
    eval.createImages(multiPointSelectionMethod=MultiPointSelectionMethod.AVERAGE,
                      regressionMethod=RegressionMethod.LOG)

    eval.createImages(multiPointSelectionMethod=MultiPointSelectionMethod.MEDIAN,
                      regressionMethod=RegressionMethod.NO_REGRESSION)
    eval.createImages(multiPointSelectionMethod=MultiPointSelectionMethod.MEDIAN,
                      regressionMethod=RegressionMethod.LINEAR)
    eval.createImages(multiPointSelectionMethod=MultiPointSelectionMethod.MEDIAN,
                      regressionMethod=RegressionMethod.LOG)

    return 0


class EvalState(Enum):
    INIT = 0
    UPLOADED = 1
    PROCESSING = 2
    PROCESSING_FINISHED = 3
    RESULTS_DOWNLOADED = 4
    RESULTS_PARSED = 5


class RegressionMethod(Enum):
    LINEAR = 0
    LOG = 1
    NO_REGRESSION = 2


class MultiPointSelectionMethod(Enum):
    AVERAGE = 0
    MEDIAN = 1


class EvaluationConfig():
    json = dict()
    file = None

    def __init__(self, file) -> None:
        self.file = os.path.abspath(file)
        if not os.path.exists(file):
            self.json = dict()

            self.json["evalName"] = "Eval"

            self.json["batch"] = dict()
            self.ncpus = [2]
            self.ram = [2000]

            self.json["proof"] = dict()
            self.targetTheory = ""
            self.sessionFolders = []
            self.session = ""
            self.timeout = 120
            self.sid = 0
            self.jobRedundancy = 1

            self.evalState = EvalState.INIT.value
        else:
            with open(file) as json_file:
                self.json = json.load(json_file)

    @property
    def jobRedundancy(self):
        return self.json["batch"]["jobRedundancy"]

    @jobRedundancy.setter
    def jobRedundancy(self, value):
        self.json["batch"]["jobRedundancy"] = value

    @property
    def ncpus(self):
        return list(sorted(self.json["batch"]["cpus"]))

    @ncpus.setter
    def ncpus(self, ncpus):
        self.json["batch"]["cpus"] = ncpus

    @property
    def ram(self):
        return list(sorted(self.json["batch"]["ram"]))

    @ram.setter
    def ram(self, ram):
        self.json["batch"]["ram"] = ram

    @property
    def targetTheory(self):
        return self.json["proof"]["targetTheory"]

    @targetTheory.setter
    def targetTheory(self, targetTheory):
        self.json["proof"]["targetTheory"] = targetTheory

    @property
    def sessionFolders(self):
        return self.json["proof"]["sessionFolders"]

    @sessionFolders.setter
    def sessionFolders(self, sessionFolders):
        self.json["proof"]["sessionFolders"] = sessionFolders

    @property
    def session(self):
        return self.json["proof"]["session"]

    @session.setter
    def session(self, session):
        self.json["proof"]["session"] = session

    @property
    def timeout(self):
        return self.json["proof"]["timeout"]

    @timeout.setter
    def timeout(self, timeout):
        self.json["proof"]["timeout"] = timeout

    @property
    def sid(self):
        return self.json["proof"]["sid"]

    @sid.setter
    def sid(self, sid):
        self.json["proof"]["sid"] = sid

    @property
    def evalState(self):
        return self.json["evalState"]

    @evalState.setter
    def evalState(self, value):
        self.json["evalState"] = value

    @property
    def evalDir(self):
        return os.path.dirname(self.file)

    def getJob(self, jid):
        return self.json["jobs"][jid]

    def getJobRAM(self, jid):
        return self.json["jobs"][jid]["ram"]

    def getJobCPUs(self, jid):
        return self.json["jobs"][jid]["cpus"]

    def getJobStats(self, jid):
        return self.json["jobs"][jid]["stats"]

    def getTotalExecutionTime(self, jid):
        try:
            stats = self.json["jobs"][jid]["stats"]
            if stats:
                return stats["totalExecutionTime"]
            else:
                return -1
        except:
            return -1

    def isValid(self, jid):
        solved = False
        try:
            statData = self.getJobStats(jid)
            if statData["lemmas"][0]["totalGoals"] == 0:
                return False

            stats = JobStatistic(statData=statData)
            solved = stats.isTheorySolved()
        except:
            return False

        return self.getTotalExecutionTime(jid) != -1 and solved

    def getJobIDs(self, cpus=None, ram=None, validOnly=False, sortedByRAM=False, sortedByCPUs=False):
        jobDataDict: dict = self.json.get("jobs")
        ids = jobDataDict.keys()

        ids = list(filter(lambda jid: self.getJobCPUs(jid) in self.ncpus, ids))
        ids = list(filter(lambda jid: self.getJobRAM(jid) in self.ram, ids))

        if cpus:
            ids = list(filter(lambda jid: self.getJobCPUs(jid) == cpus, ids))

        if ram:
            ids = list(filter(lambda jid: self.getJobRAM(jid) == ram, ids))

        if validOnly:
            ids = list(filter(lambda jid: self.isValid(jid), ids))

        if sortedByCPUs:
            ids = sorted(ids, key=lambda jid: self.getJobCPUs(jid))

        if sortedByRAM:
            ids = sorted(ids, key=lambda jid: self.getJobRAM(jid))

        return ids

    def save(self):
        with open(self.file, 'w') as f:
            json.dump(self.json, f, indent=4)


class Evaluation():
    config: EvaluationConfig = None
    jobs = []

    def __init__(self, evalConfig: EvaluationConfig):
        self.config = evalConfig
        if self.config.json.get("jobs"):
            jobDataDict: dict = self.config.json["jobs"]

            for jid in jobDataDict.keys():
                job = CloudsledgiJob(None, self.config.sid, jid)
                self.jobs.append(job)

        self.config.save()

    def uploadSource(self):
        if self.config.evalState >= EvalState.UPLOADED.value:
            logger.info("Skipping upload as source is already uploaded!")
            return

        args = AutosledgiCloudArgs(None)

        args.cloudFolders = set()
        args.session_directories = set()
        for folder in self.config.sessionFolders:
            args.cloudFolders.add(os.path.normpath(os.path.abspath(folder)))

        args.cloudFolders.add(os.path.normpath(os.path.abspath(
            os.path.dirname(self.config.targetTheory))))

        uploadJob = CloudsledgiJob(args)
        id = uploadJob.upload_files
        self.config.sid = id

        self.config.evalState = EvalState.UPLOADED.value
        self.config.save()

    def submitJobs(self):
        if self.config.evalState != EvalState.UPLOADED.value:
            logger.info("Skipping submission as jobs were already created!")
            return

        logger.info("Creating jobs..")

        for cpu in self.config.ncpus:
            for ram in self.config.ram:
                jobArgs = AutosledgiCloudArgs(None)

                jobArgs.cloudFolders = set()
                jobArgs.session_directories = set()
                for folder in self.config.sessionFolders:
                    jobArgs.cloudFolders.add(os.path.normpath(os.path.abspath(folder)))
                    jobArgs.session_directories.add(os.path.normpath(os.path.abspath(folder)))

                jobArgs.session_directories.add(os.path.normpath(os.path.abspath(
                    os.path.dirname(self.config.targetTheory))))

                jobArgs.provers = "z3 cvc4 e spass"
                jobArgs.session = self.config.session
                jobArgs.target = self.config.targetTheory
                jobArgs.sledge_timeout = self.config.timeout
                jobArgs.timeout = self.config.timeout
                jobArgs.recursive = False

                jobArgs.memory = ram
                jobArgs.vcpus = cpu

                job = CloudsledgiJob(jobArgs, sid=str(self.config.sid))
                job.usePrebuiltPSL = True

                for _ in range(self.config.jobRedundancy):
                    self.jobs.append(job)

        logger.info("Submitting jobs..")

        self.config.json["jobs"] = dict()
        job: CloudsledgiJob
        for job in self.jobs:
            job.run(resubmit=True)
            jobData = dict()
            jobData["ram"] = job.args.memory
            jobData["cpus"] = job.args.vcpus

            self.config.json["jobs"][job.getBatchId()] = jobData

        self.config.evalState = EvalState.PROCESSING.value
        logger.info("All jobs submitted!")

    def isFinished(self):
        total = len(self.jobs)

        if self.config.evalState == EvalState.PROCESSING.value:
            finished = 0
            job: CloudsledgiJob

            for job in self.jobs:
                if job.get_batch_status().isFinished():
                    finished += 1

            if finished == total:
                self.config.evalState = EvalState.PROCESSING_FINISHED.value

            self.config.save()
            return (finished == total), finished, total

        elif self.config.evalState > EvalState.PROCESSING.value:
            return True, total, total

        else:
            return False, 0, 0

    def pullResults(self, repull=False):
        if self.config.evalState == EvalState.PROCESSING_FINISHED.value or (
            self.config.evalState >= EvalState.PROCESSING_FINISHED.value and repull):
            job: CloudsledgiJob

            for job in self.jobs:
                try:
                    theoryFolder = os.path.dirname(self.config.targetTheory)
                    prefix = os.path.normpath(f"results/{job.getBatchId()}/{theoryFolder}")
                    target = os.path.normpath(self.config.evalDir + f"/jobResults/{job.getBatchId()}")
                    job.download_results(target=target, prefix=prefix, deleteAfterPull=False)
                except:
                    logger.info(f"Skipping {job.getBatchId()}")

            self.config.evalState = EvalState.RESULTS_DOWNLOADED.value
            self.config.save()
        elif self.config.evalState < EvalState.PROCESSING_FINISHED.value:
            raise Exception("Not yet ready for pulling results.")

        elif self.config.evalState > EvalState.PROCESSING_FINISHED.value:
            logger.info("Skip pulling results as results are already pulled")
            return

    def parseResults(self, reparse=False):
        if self.config.evalState < EvalState.RESULTS_PARSED.value or (
            self.config.evalState >= EvalState.RESULTS_PARSED.value and reparse):

            jobDict: dict = self.config.json["jobs"]
            for jid in jobDict.keys():
                try:
                    statFile = os.path.normpath(self.config.evalDir + f"/jobResults/{jid}/statistics.json")
                    stat = JobStatistic(statFile)
                    jobDict[jid]["stats"] = stat.statData
                except:
                    logger.info(f"Skip parsing of {jid}")

            self.config.evalState = EvalState.RESULTS_PARSED.value
            self.config.save()

        else:
            pass

        pass

    def createImages(self, multiPointSelectionMethod: MultiPointSelectionMethod = MultiPointSelectionMethod.AVERAGE,
                     regressionMethod: RegressionMethod = RegressionMethod.LINEAR):
        validJobs = self.config.getJobIDs(validOnly=True)
        nInvalid = len(self.config.getJobIDs()) - len(validJobs)

        for vcpu in self.config.ncpus:
            try:
                avgSearchTimes = dict()
                for ram in self.config.ram:
                    searchTimes = list(map(lambda jid: JobStatistic(statData=self.config.getJobStats(
                        jid)).getTotalSearchTime(), self.config.getJobIDs(cpus=vcpu, ram=ram, validOnly=True,
                                                                          sortedByCPUs=True)))

                    if len(searchTimes) > 0:
                        if multiPointSelectionMethod == MultiPointSelectionMethod.AVERAGE:
                            avgSearchTimes[ram] = np.average(np.array(searchTimes))
                        else:
                            avgSearchTimes[ram] = np.median(np.array(searchTimes))

                x: list(int) = list(avgSearchTimes.keys())
                y: list(float) = list(avgSearchTimes.values())

                if regressionMethod == RegressionMethod.NO_REGRESSION:
                    plt.plot(x, y, label=str(vcpu) + " vcpus", linewidth=1, marker=".")
                else:
                    plt.scatter(x, y, label=str(vcpu) + " vcpus", linewidth=0, marker=".")

                if regressionMethod == RegressionMethod.LOG:
                    def log_fit(x, a, b):
                        return a + b * np.log(x)

                    fitting_parameters, _ = scipy.optimize.curve_fit(log_fit, x, y)
                    x_min = 0
                    x_max = max(self.config.ram)
                    x_fit = np.linspace(x_min, x_max, 100)

                    plt.plot(x_fit, log_fit(x_fit, *fitting_parameters))
                elif regressionMethod == RegressionMethod.LINEAR:
                    coef = np.polyfit(x, y, 1)
                    poly1d_fn = np.poly1d(coef)
                    plt.plot(x, poly1d_fn(x))

                plt.legend()
            except FileExistsError:
                continue

        name = self.config.json["evalName"]
        plt.xlabel("Arbeitsspeicher in MB")
        plt.ylabel("Suchzeit in Sekunden")
        plt.title(f"Suchzeit von {name}")
        plt.savefig(
            f"{self.config.evalDir}/1-groupedByCPU-{regressionMethod.name}-{multiPointSelectionMethod.name}.png")

        plt.close()

        for ram in self.config.ram:
            try:
                avgSearchTimes = dict()
                for cpu in self.config.ncpus:
                    searchTimes = list(map(lambda jid: JobStatistic(statData=self.config.getJobStats(
                        jid)).getTotalSearchTime(),
                                           self.config.getJobIDs(cpus=cpu, ram=ram, validOnly=True, sortedByRAM=True)))

                    if len(searchTimes) > 0:
                        if multiPointSelectionMethod == MultiPointSelectionMethod.AVERAGE:
                            avgSearchTimes[cpu] = np.average(np.array(searchTimes))
                        else:
                            avgSearchTimes[cpu] = np.median(np.array(searchTimes))

                x: list(int) = list(avgSearchTimes.keys())
                y: list(float) = list(avgSearchTimes.values())

                if regressionMethod == RegressionMethod.NO_REGRESSION:
                    plt.plot(x, y, linewidth=1, label=str(ram), marker=".")
                else:
                    plt.scatter(x, y, linewidth=0, label=str(ram), marker=".")

                if regressionMethod == RegressionMethod.LOG:
                    def log_fit(x, a, b):
                        return a + b * np.log(x)

                    fitting_parameters, _ = scipy.optimize.curve_fit(log_fit, x, y)
                    x_min = 0
                    x_max = max(self.config.ncpus)
                    x_fit = np.linspace(x_min, x_max, 100)

                    plt.plot(x_fit, log_fit(x_fit, *fitting_parameters))
                elif regressionMethod == RegressionMethod.LINEAR:
                    coef = np.polyfit(x, y, 1)
                    poly1d_fn = np.poly1d(coef)
                    plt.plot(x, poly1d_fn(x))

                plt.legend(title="Arbeitsspeicher in MB")

            except Exception as ex:
                logger.error(ex)
                continue

        name = self.config.json["evalName"]
        plt.xlabel("Anzahl vCPUs")
        plt.ylabel("Suchzeit in Sekunden")
        plt.title(f"Suchzeit von {name}")
        plt.savefig(
            f"{self.config.evalDir}/2-groupedByRAM-{regressionMethod.name}-{multiPointSelectionMethod.name}.png")
        plt.close()


        avgSearchTimes = dict()
        for cpu in self.config.ncpus:
            searchTimes = list(map(lambda jid: JobStatistic(statData=self.config.getJobStats(
                jid)).getTotalSearchTime(), self.config.getJobIDs(validOnly=True, cpus=cpu, sortedByCPUs=True)))

            if len(searchTimes) > 0:
                if multiPointSelectionMethod == MultiPointSelectionMethod.AVERAGE:
                    avgSearchTimes[cpu] = np.average(np.array(searchTimes))
                else:
                    avgSearchTimes[cpu] = np.median(np.array(searchTimes))

        x: list(int) = list(avgSearchTimes.keys())
        y: list(float) = list(avgSearchTimes.values())

        plt.scatter(x, y, linewidth=0, marker=".")

        def log_fit(x, a, b):
            return a + b * np.log(x)

        fitting_parameters, _ = scipy.optimize.curve_fit(log_fit, x, y)

        x_min = 0
        x_max = 100
        x_fit = np.linspace(x_min, x_max, 100)

        plt.xlabel("Anzahl vCPUs")
        plt.ylabel("Suchzeit in Sekunden")
        plt.title(
            f"Log-Regressionskurve \n ({multiPointSelectionMethod.name} der Daten mit gleicher Anzahl von vCPUs)")
        plt.plot(x_fit, log_fit(x_fit, *fitting_parameters))
        plt.savefig(f"{self.config.evalDir}/3-complete-logRegresssion-{multiPointSelectionMethod.name}")
        plt.close()

        for ram in self.config.ram:
            ids = self.config.getJobIDs(validOnly=True, ram=ram, sortedByCPUs=True)
            x: list(int) = list(map(lambda jid: self.config.getJobCPUs(jid), ids))
            y: list(float) = list(map(lambda jid: JobStatistic(
                statData=self.config.getJobStats(jid)).getTotalSearchTime(), ids))
            plt.plot(x, y, marker=".", linewidth=0, label=str(ram) + " MB RAM")

        ids = self.config.getJobIDs(validOnly=True, sortedByCPUs=True)
        x: list(int) = list(map(lambda jid: self.config.getJobCPUs(jid), ids))
        y: list(float) = list(map(lambda jid: JobStatistic(
            statData=self.config.getJobStats(jid)).getTotalSearchTime(), ids))

        coef = np.polyfit(x, y, 1)
        poly1d_fn = np.poly1d(coef)
        plt.plot(x, poly1d_fn(x), label="linear-Regression")

        def log_fit(x, a, b):
            return a + b * np.log(x)

        fitting_parameters, _ = scipy.optimize.curve_fit(log_fit, x, y)
        x_min = 0
        x_max = max(self.config.ncpus) + 5
        x_fit = np.linspace(x_min, x_max, 100)

        plt.plot(x_fit, log_fit(x_fit, *fitting_parameters), label="log-Regression")
        plt.legend()
        plt.xlabel("Anzahl vCPUs")
        plt.ylabel("Suchzeit in Sekunden")
        plt.title(f"Alle Datenpunkte ({len(validJobs)})")

        plt.savefig(f"{self.config.evalDir}/4-allPoints")
        plt.close()

        cpus = self.config.ncpus
        labels = [f"{cpu} cpus" for cpu in cpus]

        totalDatapointsN = [len(self.config.getJobIDs(cpus=cpu, validOnly=False)) for cpu in cpus]
        validDatapointsN = [len(self.config.getJobIDs(cpus=cpu, validOnly=True)) for cpu in cpus]
        invalidDatapointsN = [len(self.config.getJobIDs(cpus=cpu, validOnly=False)) -
                              len(self.config.getJobIDs(cpus=cpu, validOnly=True)) for cpu in cpus]

        invalidDatapoints = [len(self.config.getJobIDs(cpus=cpu, validOnly=True)) /
                             len(self.config.getJobIDs(cpus=cpu, validOnly=False)) for cpu in cpus]

        fig, ax = plt.subplots()

        x = np.arange(len(cpus))

        r1 = ax.bar(x, invalidDatapoints, 0.5)
        ax.set_ylabel("Prozentual (absolut)")

        ax.set_yticks([0.25, 0.5, 0.75, 1])
        ax.set_yticklabels([f"{round(tick * 100)}%" for tick in ax.get_yticks()])
        ax.set_ylim((0, 1.1))

        ax.set_xticks(x)
        ax.set_xticklabels(labels)

        ax.bar_label(
            r1,
            labels=[f"{round(invalidDatapoints[i] * 100, 2)}%\n({validDatapointsN[i]}/{totalDatapointsN[i]})" for i in
                    range(len(invalidDatapoints))], padding=3)

        plt.title("Anteil erfolgreicher Beweise nach CPU")

        plt.tight_layout()
        plt.savefig(f"{self.config.evalDir}/5-successJobs", dpi=200)
        plt.close()

        rams = self.config.ram
        labels = rams

        totalDatapointsN = [len(self.config.getJobIDs(ram=ram, validOnly=False)) for ram in rams]
        validDatapointsN = [len(self.config.getJobIDs(ram=ram, validOnly=True)) for ram in rams]
        invalidDatapointsN = [len(self.config.getJobIDs(ram=ram, validOnly=False)) -
                              len(self.config.getJobIDs(ram=ram, validOnly=True)) for ram in rams]

        invalidDatapoints = [len(self.config.getJobIDs(ram=ram, validOnly=True)) /
                             len(self.config.getJobIDs(ram=ram, validOnly=False)) for ram in rams]

        fig, ax = plt.subplots()

        x = np.arange(len(rams))

        r1 = ax.bar(x, invalidDatapoints, 0.5)
        ax.set_ylabel("Prozentual (absolut)")

        ax.set_yticks([0.25, 0.5, 0.75, 1])
        ax.set_yticklabels([f"{round(tick * 100)}%" for tick in ax.get_yticks()])
        ax.set_ylim((0, 1.1))

        ax.set_xticks(x)
        ax.set_xticklabels(labels)
        ax.set_xlabel("MB Arbeitsspeicher")

        ax.bar_label(
            r1,
            labels=[f"{round(invalidDatapoints[i] * 100, 2)}%\n({validDatapointsN[i]}/{totalDatapointsN[i]})" for i in
                    range(len(invalidDatapoints))], padding=3)

        plt.title("Anteil erfolgreicher Beweise nach Arbeitsspeicher")

        plt.tight_layout()
        plt.savefig(f"{self.config.evalDir}/5-successJobs-ram", dpi=200)
        plt.close()

    def terminate(self):
        from . import aws_batch
        for jid in self.config.getJobIDs():
            aws_batch.job_terminate(jobid=jid, reason="Canceld by script")

        exit(0)


class JobStatistic():
    statData = None

    def __init__(self, statFile=None, statData=None):
        if statData:
            self.statData = statData
            return
        else:
            with open(statFile) as json_file:
                self.statData = json.load(json_file)

    def getTotalExecutionTime(self):
        return self.statData["totalExecutionTime"]

    def getLemmaDatas(self):
        return self.statData["lemmas"]

    def getSearchTimesOfGoal(self, lemmaIndex, goalIndex):
        goal = self.getLemmaDatas()[lemmaIndex]["goals"][goalIndex]
        searchTimes = [goal["proofs"][i]["searchTime"] for i in range(len(goal["proofs"]))]
        return searchTimes

    def getFastestSearchTimeOfGoal(self, lemmaIndex, goalIndex):
        return min(self.getSearchTimesOfGoal(lemmaIndex, goalIndex))

    def getTotalLemmaSearchTime(self, lemmaIndex):
        if self.isLemmaSolved(lemmaIndex):
            searchTimes = list()
            for goalIndex in range(len(self.getLemmaDatas()[lemmaIndex]["goals"])):
                searchTimes.append(self.getFastestSearchTimeOfGoal(lemmaIndex, goalIndex))
            return sum(searchTimes)
        else:
            return 0

    def getTotalSearchTime(self):
        searchTimes = [self.getTotalLemmaSearchTime(i) for i in range(len(self.getLemmaDatas()))]
        return sum(searchTimes)

    def isLemmaSolved(self, lemmaIndex):
        return bool(self.getLemmaDatas()[lemmaIndex]["solved"])

    def isTheorySolved(self):
        for i in range(len(self.getLemmaDatas())):
            if not self.isLemmaSolved(i):
                return False
        return True
