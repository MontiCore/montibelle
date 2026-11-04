import { Event, EventEmitter, ProviderResult, TreeDataProvider } from "vscode";
import { ProofGoal, ProofState } from "./ProofGoal";
import { ProofProvider } from "./ProofProvider";

export class ProofViewProvider implements TreeDataProvider<ProofGoal> {

  private static instance?: ProofViewProvider;

  constructor(private proofProvider: ProofProvider) {
    this._changeEventEmitter = new EventEmitter<ProofGoal | null>();
    this.onDidChangeTreeData = this._changeEventEmitter.event;

    proofProvider.register(() => { this.refresh(); });
    ProofViewProvider.instance = this;
  }

  public static getInstance() {
    return this.instance;
  }

  private _changeEventEmitter : EventEmitter<ProofGoal | null>;

  onDidChangeTreeData?: Event<ProofGoal | undefined | null>;

  getTreeItem(element: ProofGoal): ProofGoal {
    element.refresh();
    return element;
  }

  public async refresh(goal?: ProofGoal) : Promise<void> {
    if(goal !== undefined){
      var otherGoals = (await this.getChildren()!).filter(g => g !== goal);

      if(goal.proofState == ProofState.RUNNING){
        otherGoals.forEach(g => {
          if(g.proofState != ProofState.VERIFIED && g.proofState != ProofState.DISPROVEN){
            g.setState(ProofState.BLOCKED);
            this._changeEventEmitter.fire(g);
          }
        });
      }

      if(goal.proofState == ProofState.UNKNOWN
        || goal.proofState == ProofState.VERIFIED
        || goal.proofState == ProofState.DISPROVEN) {
        otherGoals.forEach(g => {
          if(g.proofState == ProofState.BLOCKED) {
            g.setState(ProofState.UNKNOWN);
            this._changeEventEmitter.fire(g);
          }
        });
      }
    }
    this._changeEventEmitter.fire(goal ? goal : null);
  }


  async getChildren(element?: ProofGoal): Promise<ProofGoal[]>{
    if (!element) {
      return Promise.resolve(this.proofProvider.getRootGoals());
    } else if (element instanceof ProofGoal){
      return element.subgoals;
    } else {
      Error("Called getChildren on an element with TreeItemCollapsibleState.None");
      return [];
    }
  }

  getParent(element: ProofGoal): ProviderResult<ProofGoal> {
    return element.parent;
  }

}
