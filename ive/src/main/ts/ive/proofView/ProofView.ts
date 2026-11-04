import { Disposable, TreeView, ViewColumn, commands, window, workspace } from 'vscode';
import * as vscode from 'vscode';
import { BackboneClient } from '../BackboneClient';
import { ProofProvider } from './ProofProvider';
import { ProofGoal, ProofState } from './ProofGoal';
import { ProofViewProvider } from './ProofViewProvider';


export class ProofView implements Disposable{

  private view?: TreeView<ProofGoal>;

  private provider?: ProofViewProvider;

  private disposables: Disposable[] = [];

  private commands: Disposable[] = [];

  private stopProve = false;

  constructor(proofProvider: ProofProvider) {
    this.provider = new ProofViewProvider(proofProvider);
    this.view = window.createTreeView('proofView',
    {
      treeDataProvider : this.provider,
      canSelectMany : false,
      showCollapseAll : false
    });

    this.commands.push(commands.registerCommand('ive.proofs.refresh', async () => proofProvider.refresh()));

    this.commands.push(commands.registerCommand('ive.proofs.verify', async (goal: ProofGoal) => {
      goal.prove();
    }));

    this.commands.push(commands.registerCommand('ive.proofs.verify.all', async () => {
      for (let goal of await this.provider?.getChildren()!){
        if(this.stopProve){
          this.stopProve = false;
          break;
        }

        if(goal.proofState == ProofState.RUNNING) {
          break;
        }

        if (goal.proofState == ProofState.VERIFIED || goal.proofState == ProofState.BLOCKED) {
          continue;
        }
        await goal.prove();
      }
    }));

    this.commands.push(commands.registerCommand('ive.proofs.verify.stop', async (goal: ProofGoal) => {
      goal.proofState = ProofState.BLOCKED;
      await BackboneClient.getInstance()?.cancelVerify(goal.theoryFile.fsPath);
      this.stopProve = true;
      this.provider?.refresh(goal);
    }));

    this.commands.push(commands.registerCommand('ive.proofs.openTheory', async (goal: ProofGoal) => {
        let theory = goal.theoryFile;
        try {
          await workspace.fs.stat(theory);
          window.showTextDocument(theory, { viewColumn: vscode.ViewColumn.One });
        } catch {
          window.showWarningMessage("Theory not found.\nEither your models are not transformed yet or you did not explicitly specify the refinement.");
        }
      }));


    this.disposables.push(this.view.onDidChangeSelection((e) => {
      if (e.selection.length === 1) {
        e.selection.forEach((goal) => {
          goal.on_ui_selection();
        });
      }
    }));
  }


  public async initProofs() {
    const goals = await this.provider?.getChildren();

    for (const goal of goals ?? []) {
      const proofStateString = await BackboneClient.getInstance()!.getProofState(goal.theoryFile.fsPath);
      goal.setState(ProofState[proofStateString as keyof typeof ProofState]);

      if (goal.getState() == ProofState.RUNNING) {
        goal.refreshProofState();
      }
    }
  }


  public getProvider() {
    return this.provider;
  }

   public dispose() {
    this.view?.dispose();
    this.commands.forEach((command) => command.dispose());
    this.disposables.forEach((disposable) => disposable.dispose());
  }
}
