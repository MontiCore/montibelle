import { Uri, workspace } from "vscode";
import { BackboneClient } from "../../ive/BackboneClient";
import { Config } from "../../ive/Config";
import { JarServerDependency } from "../JarServerDependency";
import { RunningServer } from "../RunningServer";
import { Server } from "../Server";
import { RunningBackboneServer } from "./RunningBackboneServer";
import { getLogger } from "log4js";
import { ChildProcessWithoutNullStreams } from "node:child_process";

export class BackboneServerJarDependency extends JarServerDependency<BackboneClient> implements Server<BackboneClient> {
  private childProcess: ChildProcessWithoutNullStreams | undefined;

  constructor(
    projectId: number,
    groupPath: string,
    artifactName: string,
    version: string,
    binDir: Uri,
    apiPath: string,
    readonly source: Uri,
    readonly target: Uri,
    readonly hwls?: Uri) {
    super(projectId, groupPath, artifactName, version, binDir, apiPath, false);
  }

  async start(): Promise<RunningServer<BackboneClient>> {
    return new Promise(async (resolve, reject) => {
      let options = ["-jar", this.getFullPath()];

      let workspacePath = "/" + workspace.workspaceFolders![0].uri.toString().split("//")[1].slice(1).replace("%3A", ":")

      let timestamp = new Date().toISOString().split('.')[0].replace(/[-:T]/g, '');

      options.push(`--logging.file.name=${workspacePath}/target/logs/backbone_${timestamp}.log`);

      if (Config.getCorePath()) {
        options = options.concat([`--core.path=${Config.getCorePath()}`]);
      }

      this.childProcess = require('child_process').spawn("java", options);
      getLogger('user').info("Started Backbone");

      this.childProcess?.stderr.on('data', (chunk: any) => {
        getLogger('backbone').error(chunk.toString());
      });
      this.childProcess?.stderr.on('data', (chunk: any) => {
        getLogger('backbone').info(chunk.toString());
      });

      resolve(new RunningBackboneServer(Config.getBackboneAddress(), this.source, this.target, this.hwls));
    });
  }

  stop() {
    this.childProcess?.kill();
    getLogger('backbone').info("Stopped Backbone");
  }

}
