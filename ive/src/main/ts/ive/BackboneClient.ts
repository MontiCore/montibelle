import { BackboneClient as BackboneRpcClient } from "@montibelle/backbone-rpc-client/";
import { OperationInput } from "@montibelle/backbone-rpc-client/out/montibelle/backbone/hwl/OperationInput";
import { RetrievalInput } from "@montibelle/backbone-rpc-client/out/montibelle/backbone/hwl/RetrievalInput";
import { getLogger } from "log4js";
import { Uri } from "vscode";
import { Concurrency } from "../util/Concurrency";
import { Config } from "./Config";
import { TransformState } from "../dependencies/TransformState";
import { window, ProgressLocation } from "vscode";
import { BetterObservable } from "../util/Observable";
import { ProveDefinition } from "@montibelle/backbone-rpc-client/out/montibelle/backbone/proof/ProveDefinition";
import * as fs from 'fs';
import * as path from 'path';

export class BackboneClient extends BetterObservable<BackboneClient> {


  private static instance: BackboneClient | undefined;

  private backboneClient: BackboneRpcClient;

  private workspaceId: string | undefined;


  private transformState: TransformState | undefined;

  constructor(private host: string, private source: Uri, private target: Uri, private hwl?: Uri) {
    super();
    this.backboneClient = new BackboneRpcClient(host);
    BackboneClient.instance = this;
  }

  public static getInstance() {
    return this.instance;
  }

  getLatest(): BackboneClient | Promise<BackboneClient> {
    return this;
  }

  public getTransformState(){
    return this.transformState;
  }

  public check(): Promise<void> {
    return new Promise((resolve, reject) => {
      this.checkWorkspaceId()
        .then(_ => resolve())
        .catch(reason => {
          getLogger().error(`Backbone could probably not be reached at ${this.host}`, reason);
          return reject(reason);
        });
    });
  }

  private checkWorkspaceId = Concurrency.synchronize(async () => {
    if (this.workspaceId === undefined) {
      await this.backboneClient.montibelle.backbone.Workspace
        .register({
          sourceUri: this.source.toString(),
          targetUri: this.target.toString(),
          hwlUri: this.hwl?.toString()
        })
        .then(res => {
          this.workspaceId = res.toString();
          getLogger().trace(`Workspace registered with ID ${res}`);
        });
    }
  });

  async addHwl(input: Omit<OperationInput, "workspaceId">) {
    try {
      await this.checkWorkspaceId();
      await this.backboneClient.montibelle.backbone.Hwl.add({ ...input, workspaceId: this.workspaceId!! });
    }
    catch (e) {
      getLogger("user").error(e);
    }
  }

  async removeHwl(input: Omit<OperationInput, "workspaceId">) {
    await this.checkWorkspaceId();
    await this.backboneClient.montibelle.backbone.Hwl.remove({ ...input, workspaceId: this.workspaceId!! });
  }

  async getHwls (input: Omit<RetrievalInput, "workspaceId">) {
    await this.checkWorkspaceId().catch(err => { return; });
    return await this.backboneClient.montibelle.backbone.Hwl.getHwlsForTheory(
      { ...input, workspaceId: this.workspaceId!! }
      );
  }

  async transform() {
    getLogger().info("Transforming sysml models...");
    await this.checkWorkspaceId();
    window.withProgress(
      {
        location: ProgressLocation.Window
      },
      async (progress, token) => {
        progress.report({ message: "Transforming models.." });

        let logFile = await this.backboneClient.montibelle.backbone.Transformer.transform(
          this.workspaceId!!,
          Config.transformerVersion()
          );


        this.transformState = new TransformState(logFile.toString());
        this.onChange(this);

        this.transformState.register((state) => {
          this.onChange(this);
          if (state.totalComponents > 0 && !state.finished) {
            progress.report({
              message: `Transforming models ${state.processedComponents}/${state.totalComponents}`,
              increment: state.processedComponents / state.totalComponents }
            );
          }
        });

        await this.transformState.waitFinsished();
        getLogger().info("Finished sysml model transformation");

        if (!this.transformState.error) {
          progress.report({ message: `${this.transformState.totalComponents} models were transformed.`, increment: 100 });
          await new Promise(resolve => setTimeout(resolve, 1000));
        }
      });
  }

  async transformIfNeccessary(){
    var logContainsError = false;

    var latestModelTime = 0;
    const modelFiles = fs.readdirSync(this.source.fsPath);
    modelFiles.forEach(modelFile => {
      const filePath = path.join(this.source.fsPath, modelFile);
      const modelStats = fs.statSync(filePath);
      if (modelStats.mtime.getTime() > latestModelTime) {
        latestModelTime = modelStats.mtime.getTime();
      }
    });

    var latestTransformerTime = -1;
    var latestTransformerLog = "";
    if (fs.existsSync(path.join(this.target.fsPath, "logs"))) {
      const logFiles = fs.readdirSync(path.join(this.target.fsPath, "logs"));
      logFiles.filter(fileName => fileName.includes("transformer")).forEach(transformerFile => {
        const filePath = path.join(path.join(this.target.fsPath, "logs"), transformerFile);
        const modelStats = fs.statSync(filePath);
        if (modelStats.mtime.getTime() > latestTransformerTime) {
          latestTransformerTime = modelStats.mtime.getTime();
          latestTransformerLog = filePath;
        }
      });

      if(latestTransformerLog != ""){
        logContainsError = fs.readFileSync(latestTransformerLog).toString().toLowerCase().includes("error");
      }
    }

    if (latestModelTime > latestTransformerTime || logContainsError) {
      this.transform();
    } else {
      this.transformState = new TransformState(latestTransformerLog.toString());
      this.transformState.update(latestTransformerLog.toString());
      this.onChange(this);
      await this.transformState.waitFinsished().finally(
        () => this.transformState?.onChange(this.transformState)
      );
      getLogger().info("No model has been changed. No transformation needed.");
    }
  }

  async prove(input: Omit<ProveDefinition, "workspaceId">) {
    await this.checkWorkspaceId();
    return await this.backboneClient.montibelle.backbone.Proof.verify( { ...input, workspaceId: this.workspaceId!! });
  }

  async cancelVerify(theoryFile: string) {
    return await this.backboneClient.montibelle.backbone.Proof.cancelVerify(theoryFile);
  }

  async getProofState(theoryFile: string) {
    return await this.backboneClient.montibelle.backbone.Proof.getProofState(theoryFile);
  }

  async getProofProgress(theoryFile: string) {
    return await this.backboneClient.montibelle.backbone.Proof.getProofProgress(theoryFile);
  }

}