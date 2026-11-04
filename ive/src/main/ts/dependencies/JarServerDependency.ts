import { existsSync, createWriteStream, readFileSync, mkdirSync, statSync, unlinkSync } from "fs";
import { join } from "path";
import { get } from 'https';
import { homedir } from "os";
import { window, ProgressLocation, Uri } from "vscode";
import { getLogger } from "log4js";
import { MissingGitlabToken } from "../ive/errors/MissingGitlabToken";
import { ServerDependency } from "./ServerDependency";
import { Server } from "./Server";
import { RunningServer } from "./RunningServer";

export abstract class JarServerDependency<ClientType> implements ServerDependency<ClientType>, Server<ClientType> {

  protected version: string;

  constructor(
    readonly projectId: number,
    readonly groupPath: string,
    readonly artifactName: string,
    version: string,
    readonly binDir: Uri,
    readonly apiPath: string,
    readonly jarWithDependencies: boolean = true
  ) {
    let regex = /^(?<semver>[1-9][0-9]*\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*))(-(?<timestamp>(?!SNAPSHOT).*))?$/;
    let match = regex.exec(version);
    if (match === null || match?.length < 1) {
      throw Error(`Version must follow pattern "<major>.<minor>.<patch>(-<timestamp>)?", was ${version}`);
    }
    else {
      this.version = version;
    }
  }

  getJarName(): string {
    let baseName = this.artifactName + "-" + this.version;
    if (this.jarWithDependencies) {
      return baseName + "-jar-with-dependencies.jar";
    } else {
      return baseName + ".jar";
    }
  }

  getFullPath(): string {
    return join(this.binDir.fsPath, this.getJarName());
  }

  exists(): boolean {
    return existsSync(this.getFullPath());
  }

  getFullLink() {
    let version: string;
    if(this.version.includes("-")) {
      version = this.version.split("-")[0] + "-SNAPSHOT";
    }
    else {
      version = this.version;
    }
    return `${this.apiPath}/projects/${this.projectId}/packages/maven/${this.groupPath}/${version}/${this.getJarName()}`;
  }

  abstract start(): Promise<RunningServer<ClientType>>;

  async download(): Promise<Server<ClientType>> {
    if (this.exists()) {
      getLogger().debug(`External dependency ${this.getJarName()} already exists. Skipping download.`);
      return Promise.resolve(this);
    }

    const tokenPath: string = join(homedir(), ".montibelle", "accesstoken.txt");

    if (!existsSync(tokenPath)) {
      throw new MissingGitlabToken();
    }
    else {
      let url = this.getFullLink();
      let token = readFileSync(tokenPath, { encoding: "utf8" }).trim();
      let target = this.getFullPath();

      if (!existsSync(this.binDir.fsPath)) {
        mkdirSync(this.binDir.fsPath, { recursive: true });
      }

      let res = new Promise<JarServerDependency<ClientType>>((resolve, reject) => {
        getLogger().trace(`Attempting to download ${url} into "${target}"`);

        let targetFile = createWriteStream(target);
        let request = get(
          url,
          { headers: { 'Private-Token': token } },
          (res) => {
            res.pipe(targetFile);
            res.on("end", () => {
              const dlSize = statSync(target).size;
              getLogger().trace("Download size: " + dlSize);

              if (dlSize > 10e4) {
                resolve(this);
              }
              else {
                let message = readFileSync(target, { "encoding": "utf8" });
                unlinkSync(target);
                getLogger().error(`Download failed: ${message}.`);
                throw Error(message);
              }
            });
          }
        );
        request.on("error", (err) => reject(err));
        request.on("closed", (err) => reject(err));
      });

      window.withProgress(
        {
          location: ProgressLocation.Notification,
          title: `Downloading dependency ${this.getJarName()}`
        },
        (progress, token) => { return res; }
      );

      return res;
    }
  }

}
