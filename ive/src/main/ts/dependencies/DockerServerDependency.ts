import { getLogger } from "log4js";
import { InputBoxOptions, Task, TaskExecution, TaskProcessEndEvent, tasks, TaskScope, window } from "vscode";
import { Concurrency } from "../util/Concurrency";
import { TaskUtil } from "../util/TaskUtil";
import { ServerDependency } from "./ServerDependency";
import { DockerCommand } from "./DockerCommand";
import { RunningServer } from "./RunningServer";
import { Server } from "./Server";


export abstract class DockerServerDependency<ClientType> implements ServerDependency<ClientType>, Server<ClientType> {

  static mavenVersionToDockerTag(version: string): string {
    let regex = /^(?<semver>[1-9][0-9]*\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*))(-(?<snapshot>.*))?$/;
    let match = regex.exec(version);
    if (match !== null && match?.groups!.snapshot !== undefined && match?.groups!.snapshot !== "SNAPSHOT") {
      return version.replace(regex, "$<semver>-SNAPSHOT");
    }
    else {
      return version;
    }
  }

  private static attemptLogin: ((registry: string) => Promise<void>) = Concurrency.synchronize(async (registry: string) => {
    return new Promise(async (resolve, reject) => {
      let options: InputBoxOptions = {
        prompt: `Login to Docker Registry at ${registry}`,
        placeHolder: "username:password",
        validateInput: (value) => {
          if (!value.includes(":") || value.includes(" ")) {
            return `Format must be "<username>:<password>"! (colon, no spaces)`;
          }
          return undefined;
        }
      };
      let input = await window.showInputBox(options);
      if (input === undefined) {
        let reason = "Failed to specify login credentials";
        getLogger().debug(`Aborting login attempt. ${reason}.`);
        return reject(reason);
      }
      let username = input.split(":")[0];
      let password = input.split(":")[1];

      getLogger().trace(`Running "docker login ${registry} -u ***** -p *****"`);
      let execution: TaskExecution = await TaskUtil.execute(
        `Logging in to ${registry}`,
        new DockerCommand(registry, "login").addArgs("-u", username, "-p", password).createProcessExecution()
      );

      let end = await TaskUtil.onExecutionEndOf(execution);
      getLogger().trace(`Attempted login returned ${end.exitCode}. Restricting further attempts.`);
      DockerServerDependency.alreadyAttemptedLogin = true;
      return end.exitCode === 0 ? resolve() : reject();
    });
  });

  private static alreadyAttemptedLogin: boolean = false;

  private registry: string;

  constructor(
    private image: string,
    private tag: string = "latest"
  ) {
    this.registry = image.split("/")[0];
  }

  public getFullName(): string {
    return this.image + ":" + this.tag;
  }

  public getReadableName(): string {
    return this.image.split("/").pop() + ":" + this.tag;
  }

  public createRunCommand(): DockerCommand {
    return new DockerCommand(this.getFullName(), "run");
  }

  abstract start(): Promise<RunningServer<ClientType>>;

  public async download(): Promise<DockerServerDependency<ClientType>> {
    return new Promise(async (resolve, reject) => {

      let execution: TaskExecution = await TaskUtil.execute(
        `Pull ${this.getReadableName()}`,
        new DockerCommand(this.getFullName(), "pull").createProcessExecution()
      );

      let end = await TaskUtil.onExecutionEndOf(execution);
      if (end.exitCode === 0) {
        getLogger().debug(`Successful pull of ${this.getReadableName()}`);
        return resolve(this);
      }
      else if (!DockerServerDependency.alreadyAttemptedLogin) {
        getLogger().debug(`Failed to pull ${this.getReadableName()}, attempting login`);
        try {
          await DockerServerDependency.attemptLogin(this.registry);
          getLogger().debug(`Successful login, re-attempting pull of ${this.getReadableName()}`);
          return this.download();
        }
        catch (error) {
          let reason = `Login failed`;
          getLogger().debug(`Cannot pull ${this.getReadableName()}. ${reason}.`);
          return reject(reason);
        }
      }
      else {
        let reason = `Unknown error or follow-up issue`;
        getLogger().debug(`Cannot pull ${this.getReadableName()}. ${reason}.`);
        return reject(reason);
      }
    });
  }

}
