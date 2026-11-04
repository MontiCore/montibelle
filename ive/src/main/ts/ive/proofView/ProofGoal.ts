import { Disposable } from "vscode-languageclient";
import { IntervalFunction } from "../../util/IntervalFunction";
import { ThemeIcon, TreeItem, TreeItemCollapsibleState, Uri, workspace } from "vscode";
import * as path from 'path';
import { IveUri } from "../../util/IveUri";
import { Theories } from "../theories/Theories";
import { BackboneClient } from "../BackboneClient";
import { window } from "vscode";
import * as vscode from 'vscode';
import * as fs from 'fs';
import { Config } from "../Config";
import { ProofViewProvider } from "./ProofViewProvider";
import { ProofProvider } from "./ProofProvider";
import { ProgressBar } from "../../dependencies/ProgressBar";
import { getLogger } from "log4js";

export class ProofGoal extends TreeItem implements Disposable {
  public subgoals: ProofGoal[] = [];
  public proofState = ProofState.UNKNOWN;
  private proofStateWatcher?: IntervalFunction = undefined;
  private progressBar?: ProgressBar;

  constructor(
    public readonly theoryFile: Uri,
    protected proofProvider: ProofProvider,
    public readonly parent?: ProofGoal
  ) {
    super("", TreeItemCollapsibleState.None);
  }

  private setIveIcon(icon: string | null) {
    let basepath = path.join(__filename, '..', '..', '..', '..', '..', '..', 'res', 'icons');

    if(icon) {
      this.iconPath = { light: path.join(basepath, 'light', icon!),
        dark: path.join(basepath, 'dark', icon!) };
    }
  }

  public isSubgoal() {
    return this.parent != undefined;
  }

  public getState(){
    return this.proofState;
  }

  public setState(state: ProofState){
    this.proofState = state;
    this.contextValue = state;
    this.refresh();
  }

  public async on_ui_selection() {
    const theory_doc = await vscode.workspace.openTextDocument(this.theoryFile);

    await vscode.window.showTextDocument(theory_doc, {
      viewColumn: vscode.ViewColumn.Active,
      preview: false
    });
  }


  public async refreshProofState() {
    if (this.proofStateWatcher == undefined) {
      this.progressBar = new ProgressBar();
      this.progressBar.show();
      this.proofStateWatcher = new IntervalFunction(async () => {
        const client = BackboneClient.getInstance()!;
        const proofProgress = await client.getProofProgress(this.theoryFile.fsPath);
        this.progressBar?.update(proofProgress);
        const backboneProofState = await client.getProofState(this.theoryFile.fsPath);
        this.proofState = ProofState[backboneProofState as keyof typeof ProofState];

        await this.refresh(true);

        if (this.proofState != ProofState.RUNNING) {
          this.progressBar?.closeWithCancel();
          this.progressBar = undefined;
          this.proofStateWatcher?.dispose();
          this.proofStateWatcher = undefined;
        }
      }, 1000);
    }
  }

  public async prove(){
    if(!BackboneClient.getInstance()?.getTransformState()?.finished){
      window.showInformationMessage("Model transformation is not finished yet");
      return;
    }

    let proveSubgoals: "Try proving subgoals first" | "Ignore subgoals" | undefined = undefined;

    if (this.subgoals.some(subgoal => subgoal.proofState != ProofState.VERIFIED)) {
      proveSubgoals = await window.showWarningMessage(
        "Some subgoals are not proven yet. Do you want to prove them first?",
        { modal: true },
        "Try proving subgoals first", "Ignore subgoals"
      );
      if (proveSubgoals == undefined) {
        return;
      }
    }

    if (proveSubgoals == "Try proving subgoals first") {
      for (let subgoal of this.subgoals){
        if (subgoal.proofState == ProofState.VERIFIED) {
          continue;
        }
        await subgoal.prove();
      }
    }

    this.proofState = ProofState.RUNNING;
    this.refresh(true);
    console.log("Timeout " + Config.getTimeout())
    BackboneClient.getInstance()?.prove({
       theoryFile: this.theoryFile.fsPath,
       session: "top",
       sessionDirectories: [workspace.workspaceFolders![0].uri.fsPath],
       timeout: Config.getTimeout(),
       cloud: false
      })
    .then(() => {this.refreshProofState();});


    while (this.proofState == ProofState.RUNNING) {
      await new Promise( resolve => setTimeout(resolve, 500));
    }
  }

  public async refresh(refreshView: boolean = false) {
    if(fs.readFileSync(this.theoryFile.fsPath).includes("(* Disproven!")) {
      this.proofState = ProofState.DISPROVEN;
      this.contextValue = this.proofState;
    } else if(!fs.readFileSync(this.theoryFile.fsPath).includes("(* autosledgi *) sorry")
         && fs.readFileSync(this.theoryFile.fsPath).includes("(* We are done here *)")){
      this.proofState = ProofState.VERIFIED;
      this.contextValue = this.proofState;
    }

    this.label = this.toString();

    this.subgoals.forEach(subgoal => subgoal.dispose());
    this.subgoals = this.calculateSubgoals();

    this.contextValue = this.getState();
    this.description = "";
    this.tooltip = this.toString(true);

    switch (this.getState()) {
      case ProofState.RUNNING:
        this.iconPath = new ThemeIcon('loading~spin');
        break;
      case ProofState.VERIFIED:
        this.setIveIcon("circle-green.svg");
        break;
      case ProofState.UNKNOWN:
        this.setIveIcon("circle-grey.svg");
        break;
      case ProofState.BLOCKED:
        this.setIveIcon("circle-grey.svg");
        break;
      case ProofState.DISPROVEN:
        this.setIveIcon("circle-red.svg");
        break;
    }

    if (refreshView){
      await ProofViewProvider.getInstance()?.refresh(this);
    }
  }

  protected calculateSubgoals(): ProofGoal[] {
    return [];
  }

  public toString(full?: boolean) {
    return IveUri.getFilenameWithoutExtension(this.theoryFile)
  }

  dispose(): void {
    getLogger().info("ProofGoal is disposed " + this.toString(true));
    this.proofStateWatcher?.dispose();
  }
}

export class RequirementProofGoal extends ProofGoal {

  constructor(
    public readonly name: string,
    theoryFile: Uri,
    proofProvider: ProofProvider,
    parent?: ProofGoal
  ) {
    super(theoryFile, proofProvider, parent);
    this.refresh();
  }

  dispose(): void {
    super.dispose();
  }

  public async on_ui_selection() {
    let reqModel = this.proofProvider.getUriByGoal(this.name);

    if(!reqModel) {
      getLogger().error("Unable to open requirement model for " + this.toString(true));
      return;
    }

    const sysml_doc = await vscode.workspace.openTextDocument(reqModel);
    await vscode.window.showTextDocument(sysml_doc, {
      viewColumn: vscode.ViewColumn.Active,
      preview: false
    });
  }
}

export class RefinementProofGoal extends ProofGoal {

  constructor(
    public readonly chain: string[],
    theoryFile: Uri,
    proofProvider: ProofProvider,
    parent?: ProofGoal
  ) {
    super(theoryFile, proofProvider, parent);
    this.refresh();
  }

   protected calculateSubgoals(): ProofGoal[] {
    if (this.chain.length <= 2) {
      return [];
    }

    let subgoals: ProofGoal[] = [];
    for (let i = 0; i < this.chain.length - 1; i++) {
      let sgTheoryUri = IveUri.appendUri(Theories.getInstance()!.getLocation(),
                                       "ref",
                                       this.chain[i + 1],
                                       this.chain[i],
                                       "ref_" + this.chain[i + 1] + "_rough_" + this.chain[i] + ".thy");
      let subgoal = new RefinementProofGoal([this.chain[i], this.chain[i + 1]], sgTheoryUri, this.proofProvider, this);
      subgoals.push(subgoal);
    }

    return subgoals;
  }

  public async on_ui_selection() {
    let refiner = this.proofProvider.getUriByGoal(this.head());
    let refinement = this.proofProvider.getUriByGoal(this.last());

    if (refinement && refiner) {
      const refinerDocPromise = vscode.workspace.openTextDocument(refiner);
      const refinementDocPromise = vscode.workspace.openTextDocument(refinement);

      const [refiner_doc, refinement_doc] = await Promise.all([refinerDocPromise, refinementDocPromise]);

      await vscode.window.showTextDocument(refiner_doc, {
        viewColumn: vscode.ViewColumn.One,
        preview: false
      });
      await vscode.window.showTextDocument(refinement_doc, {
        viewColumn: vscode.ViewColumn.Two,
        preview: false
      });
    }
  }

  public head() {
    return this.chain[0];
  }

  public tail() {
    return this.chain.slice(1);
  }

  public last() {
    return this.chain[this.chain.length - 1];
  }

  public contains(goal: RefinementProofGoal) {
    return goal.chain.every((v, i) => this.chain.indexOf(v, i) + 1);
  }

  public async refresh(refreshView?: boolean): Promise<void> {
    super.refresh(refreshView);

    this.collapsibleState = this.chain.length > 2 ? TreeItemCollapsibleState.Expanded : TreeItemCollapsibleState.None;
  }

  public toString(full?: boolean) {
    const reversedChain = [...this.chain].reverse();
    if (this.chain.length > 2 && !full) {
      return reversedChain[0] + " ⊑ ... ⊑ " + reversedChain[reversedChain.length - 1];
    } else {
      return reversedChain.join(" ⊑ ");
    }
  }

  dispose(): void {
    super.dispose();
  }
}

export enum ProofState {
  UNKNOWN = "unknown",
  VERIFIED = "proven",
  RUNNING = "running",
  DISPROVEN = "disproven",
  BLOCKED = "blocked",
}
