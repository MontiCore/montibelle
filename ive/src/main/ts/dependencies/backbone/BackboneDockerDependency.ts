import { getLogger } from "log4js";
import { Uri } from "vscode";
import { BackboneClient } from "../../ive/BackboneClient";
import { Config } from "../../ive/Config";
import { IveUri } from "../../util/IveUri";
import { TaskUtil } from "../../util/TaskUtil";
import { DockerServerDependency } from "../DockerServerDependency";
import { Server } from "../Server";
import { RunningBackboneServer } from "./RunningBackboneServer";
import { homedir } from "os";
import { mkdirSync, existsSync } from "fs";

export class BackboneServerDockerDependency extends DockerServerDependency<BackboneClient> implements Server<BackboneClient> {

  constructor (
    image: string,
    readonly localSource: Uri,
    readonly localTarget: Uri,
    readonly backboneSource: Uri,
    readonly backboneTarget: Uri,
    readonly localHwls?: Uri,
    readonly backboneHwls?: Uri,
    version: string = "latest"
  ) {
    super(image, BackboneServerDockerDependency.mavenVersionToDockerTag(version));
  }

  async start(): Promise<RunningBackboneServer> {
    getLogger().trace(`Starting backbone server as docker container of ${this.getFullName()}`);

    return new Promise(async (resolve, reject) => {

      let localLibFolder = Uri.joinPath(IveUri.getParent(this.localTarget), "lib");

      const dockerCommand = this.createRunCommand()
        .addVol(
          IveUri.appendUri(this.localSource).fsPath,
          IveUri.appendUri(this.backboneSource).path)
        .addVol(
          IveUri.appendUri(this.localTarget).fsPath,
          IveUri.appendUri(this.backboneTarget).path)
        .addVol(
          IveUri.appendUri(localLibFolder).fsPath,
          IveUri.appendUri(localLibFolder).path)
        .addPort(8080, 8080);

      if (!existsSync(localLibFolder.fsPath)) {
        mkdirSync(localLibFolder.fsPath);
      }

      if (this.localHwls !== undefined && this.backboneHwls !== undefined) {
        dockerCommand
          .addVol(
            IveUri.appendUri(this.localHwls).fsPath,
            IveUri.appendUri(this.backboneHwls).path);
      }

      let homeFolder = Uri.file(homedir());

      let accessTokenFolder = Uri.joinPath(homeFolder, ".montibelle");
      let awsFolder = Uri.joinPath(homeFolder, ".aws");

      dockerCommand.addVol(accessTokenFolder.fsPath, "/home/isabelle/.montibelle");

      if (require("fs").existsSync(awsFolder.fsPath)) {
        dockerCommand.addVol(awsFolder.fsPath, "/home/isabelle/.aws");
      }

      let execution = await TaskUtil.execute(`Run backbone at "localhost:8080"`,
      dockerCommand.createProcessExecution());

      await TaskUtil.onExecutionStartOf(execution);
      return resolve(
        new RunningBackboneServer(Config.getBackboneAddress(),
        this.backboneSource,
        this.backboneTarget,
        this.backboneHwls)
      );
    });
  }

}
