import { ProcessExecution } from "vscode";

export class DockerCommand {

  private command: string;

  private image: string;

  private volumes: Map<String, String> = new Map();

  private ports: Map<number, number> = new Map();

  private args: string[] = [];

  constructor(image: string, command: string) {
    this.image = image;
    this.command = command;
  }

  addVol(source: string, target: string) {
    const escChar = process.platform === "win32" ? "`" : "\\";
    this.volumes.set(source.replace(" ", escChar + " "), target);
    return this;
  }

  addArg(arg: string) {
    this.args.push(arg);
    return this;
  }

  addArgs(...args: string[]) {
    for (let arg of args) {
      this.addArg(arg);
    }
    return this;
  }

  addPort(local: number, container: number) {
    this.ports.set(local, container);
    return this;
  }

  createProcessExecution(): ProcessExecution {
    let pArgs: string[] = [this.command];

    if(this.command === "run") {
      pArgs.push("--rm");
    }

    this.volumes.forEach((target, source) => {
      pArgs.push("--mount");
      pArgs.push(`type=bind,source=${source},destination=${target}`);
    });
    this.ports.forEach((container, local) => {
      pArgs.push("-p");
      pArgs.push(`${local}:${container}`);
    });

    pArgs.push(this.image);

    this.args.forEach(a => pArgs.push(a));

    return new ProcessExecution(process.platform.startsWith("win") ? "docker.exe" : "docker", pArgs);
  }

}
