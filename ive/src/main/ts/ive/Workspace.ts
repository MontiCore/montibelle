import { getLogger } from "log4js";
import { Disposable, ExtensionContext, extensions, Uri, workspace } from "vscode";
import { DidChangeConfigurationNotification, DidChangeConfigurationParams, LanguageClient } from "vscode-languageclient/node";
import { IveUri } from "../util/IveUri";
import { BackboneClient } from "./BackboneClient";
import { Config } from "./Config";
import { Models } from "./models/Models";
import { SidebarView } from "./SidebarView";
import { Theories, TheoriesLocation } from "./theories/Theories";
import {Server} from "../dependencies/Server";
import {BackboneServerJarDependency} from "../dependencies/backbone/BackboneJarDependency";

export class Workspace implements Disposable {

  private backboneClient: Promise<BackboneClient>;
  private backboneServer: Server<BackboneClient> | undefined;

  private sysmlClient: Promise<LanguageClient>;
  private sysmlResources: Disposable | undefined;
  private sysmlReconfigDisposable: Disposable | undefined;


  private sidebar: SidebarView;

  private models: Models;

  private theories: Theories;

  constructor(context: ExtensionContext) {
    let localWorkspace = workspace.workspaceFolders!![0].uri;

    this.sysmlClient = new Promise(resolve => setTimeout(resolve, 2 * 1000)).then(() => extensions.getExtension("MontiBelle.sysmlv2")?.exports.getLanguageClient());

    let backboneWorkspace = workspace.workspaceFolders!![0].uri;

    this.backboneClient = Config
      .backboneDependency(
        localWorkspace,
        backboneWorkspace,
        IveUri.appendUri(context.extensionUri, "bin")
      )
      .download()
      .then(server => {
        this.backboneServer = server;
        return server.start();
      })
      .then(runningServer => runningServer.connect())
      .catch(reason => {
        getLogger("user").warn(`Backbone is not active. ${reason}.`);
        throw reason;
      });

    this.theories = new Theories(IveUri.appendUri(localWorkspace, Config.getTheoryTarget()));
    this.models = new Models(IveUri.appendUri(localWorkspace, Config.getSource()), this.backboneClient, this.theories);

    this.sidebar = new SidebarView(context, this.models, this.theories, new TheoriesLocation(localWorkspace), this);

    this.sysmlClient.then((client) => {
       let newSource = IveUri.appendUri(localWorkspace, Config.getSource()).fsPath;

      let params: DidChangeConfigurationParams = {
        settings: {
          source: newSource
        }
      };
      client.sendNotification(DidChangeConfigurationNotification.type, params);
    });

  }

  private addSourceReconfiguration(localWorkspace: Uri, client: LanguageClient, docker: boolean) {
    return workspace.onDidChangeConfiguration(configChange => {
      if (configChange.affectsConfiguration("ive.workspace.modelLocation")) {
        let newSource = IveUri.appendUri(localWorkspace, Config.getSource()).fsPath;
        if (docker) {
          newSource = newSource.replace(/\\/g, "/");
        }
        let params: DidChangeConfigurationParams = {
          settings: {
            source: newSource
          }
        };
        client.sendNotification(DidChangeConfigurationNotification.type, params);
      }
    });
  }

  public dispose() {
    this.sysmlClient.then(sysmlClient => sysmlClient.stop());
    this.sysmlResources?.dispose();
    this.sysmlReconfigDisposable?.dispose();

    this.sidebar.dispose();

    this.models.dispose();
    this.theories.dispose();

    if (this.backboneServer instanceof BackboneServerJarDependency) {
        this.backboneServer?.stop();
    }
  }

  public getBackboneClient(): Promise<BackboneClient> {
    return this.backboneClient;
  }

  public getSysMLLspClient(): Promise<LanguageClient> {
    return this.sysmlClient;
  }

}
