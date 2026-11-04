import { PathLike } from "fs";
import { getLogger } from "log4js";
import * as vscode from 'vscode';
import { workspace } from "vscode";
import { BackboneServerDockerDependency } from "../dependencies/backbone/BackboneDockerDependency";
import { BackboneServerJarDependency } from "../dependencies/backbone/BackboneJarDependency";
import { RunningBackboneServer } from "../dependencies/backbone/RunningBackboneServer";
import { Server } from "../dependencies/Server";
import { ServerDependency } from "../dependencies/ServerDependency";
import { IveUri } from "../util/IveUri";
import { BackboneClient } from "./BackboneClient";

export namespace Config {


  const api = "https://git.rwth-aachen.de/api/v4";
  const bbReg = "registry.git.rwth-aachen.de/montibelle/frontend/tooling/backbone";


  const welcomeScreen = "ive.showWelcome";
  const AIMontibelleScreen = "ive.showAIMontibelle";

  const modelLocation = "ive.workspace.modelLocation";
  const compilationTarget = "ive.workspace.compilationTarget";
  const handWrittenArtifacts = "ive.workspace.handWrittenArtifacts";

  const smlAddr = "ive.dependencies.sysmlLanguageServer.bAddress";

  const bbMode = "ive.dependencies.backboneServer.aMode";
  const bbAddr = "ive.dependencies.backboneServer.bAddress";
  const bbVer = "ive.dependencies.backboneServer.cVersion";

  const transVer = "ive.dependencies.backboneServer.transformer.version";

  const asCore = "ive.dependencies.backboneServer.proofFinding.backend";
  const timeout = "ive.dependencies.backboneServer.proofFinding.timeout";

  function get<T>(key: string, defaultValue?: T): T {
    let lastDot = key.lastIndexOf(".");
    if (defaultValue !== undefined) {
      return workspace.getConfiguration(key.substring(0, lastDot)).get<T>(key.substring(lastDot + 1)) ?? defaultValue;
    }
    else {
      return workspace.getConfiguration(key.substring(0, lastDot)).get<T>(key.substring(lastDot + 1))!!;
    }
  }

  function set<T>(key: string, value: T) {
    let lastDot = key.lastIndexOf(".");
    return workspace.getConfiguration(key.substring(0, lastDot))
      .update(key.substring(lastDot + 1), value, vscode.ConfigurationTarget.Workspace);
  }

  export enum Mode {
    LOCAL, DOCKER, RUNNING
  }

  function toMode(mode: string): Mode {
    if (mode.includes("Docker")) {
      return Mode.DOCKER;
    }
    else if (mode.includes("Local")) {
      return Mode.LOCAL;
    }
    else {
      return Mode.RUNNING;
    }
  }


  function backboneVersion(): string {
    return get<string>(bbVer);
  }

  function sysmlHostname(): string {
    let regex = /^(?<hostname>.+):(?<port>[1-9][0-9]*)$/;
    let match = regex.exec(get<string>(smlAddr));
    return match!.groups!.hostname;
  }

  function sysmlPort(): number {
    let regex = /^(?<hostname>.+):(?<port>[1-9][0-9]*)$/;
    let match = regex.exec(get<string>(smlAddr));
    return +match!.groups!.port;
  }

  export function getShowWelcome(): boolean {
    return get<boolean>(welcomeScreen);
  }

  export function getShowAIMontibelle(): boolean {
    return get<boolean>(AIMontibelleScreen, true);
  }

  export function getSource(): string {
    return get<string>(modelLocation, "source");
  }

  export function setSource(source: string): Thenable<void> {
    getLogger().trace(`Switching workspace source to ${source}`);
    return set(modelLocation, source);
  }

  export function getTarget(): string {
    return get<string>(compilationTarget, "target");
  }

  export function getTheoryTarget(): string {
    return vscode.Uri.joinPath(vscode.Uri.parse(getTarget()), "theories").fsPath.toString();
  }

  export function setTarget(target: string): Thenable<void> {
    getLogger().trace(`Switching workspace target to ${target}`);
    return set(compilationTarget, target);
  }

  export function getHwls(): string {
    return get<string>(handWrittenArtifacts, "hwls");
  }

  export function setHwls(hwls: string): Thenable<void> {
    getLogger().trace(`Switching workspace hwls to ${hwls}`);
    return set(handWrittenArtifacts, hwls);
  }

  export function transformerVersion(): string {
    return get<string>(transVer);
  }

  export function getBackboneMode(): Mode {
    return toMode(get<string>(bbMode, "Docker"));
  }

  export function getBackboneAddress(): string {
    return get<string>(bbAddr);
  }

  export function backboneDependency(
    localWorkspacePath: vscode.Uri,
    backboneWorkspacePath: vscode.Uri,
    binPath: vscode.Uri): ServerDependency<BackboneClient>
  {
    switch (getBackboneMode()) {
      case Mode.RUNNING: {
        return {
          download(): Promise<Server<BackboneClient>> {
            return Promise.resolve({
              start(): Promise<RunningBackboneServer> {
                getLogger().trace(`Starting dummy backbone`);
                let source = IveUri.appendUri(backboneWorkspacePath, Config.getSource());
                let target = IveUri.appendUri(backboneWorkspacePath, Config.getTarget());
                let hwls = IveUri.appendUri(backboneWorkspacePath, Config.getHwls());
                return Promise.resolve(new RunningBackboneServer(Config.getBackboneAddress(), source, target, hwls));
              }
            });
          }
        };
      }
      case Mode.LOCAL: {
        return new BackboneServerJarDependency(
          41628,
          "montibelle/backbone",
          "backbone",
          backboneVersion(),
          binPath,
          api,
          IveUri.appendUri(localWorkspacePath, Config.getSource()),
          IveUri.appendUri(localWorkspacePath, Config.getTarget()),
          IveUri.appendUri(localWorkspacePath, Config.getHwls())
        );
      }
      case Mode.DOCKER: {
        return new BackboneServerDockerDependency(
          bbReg,
          IveUri.appendUri(localWorkspacePath, Config.getSource()),
          IveUri.appendUri(localWorkspacePath, Config.getTarget()),
          IveUri.appendUri(backboneWorkspacePath, Config.getSource()),
          IveUri.appendUri(backboneWorkspacePath, Config.getTarget()),
          IveUri.appendUri(localWorkspacePath, Config.getHwls()),
          IveUri.appendUri(backboneWorkspacePath, Config.getHwls()),
          backboneVersion()
        );
      }
    }
  }

  export function getCorePath(): PathLike {
    return vscode.Uri.file(get<string>(asCore)).fsPath;
  }

  export function getTimeout(): Number {
    return get<Number>(timeout);
  }

  export function getModelLocationKey(): String {
    return modelLocation;
  }

  export function getCompilationTargetKey(): string {
    return compilationTarget;
  }

}
