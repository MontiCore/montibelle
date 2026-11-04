import { Uri } from "vscode";
import { BetterObservable } from "../../util/Observable";
import { Models } from "../models/Models";
import { IveUri } from "../../util/IveUri";
import { getLogger } from "log4js";
import { ProofGoal, ProofState, RefinementProofGoal, RequirementProofGoal } from "./ProofGoal";
import { Theories } from "../theories/Theories";
import path from "path";

const REF_NAME_MISSALIGN_WARN_MSG = "The refinement therorie does not match folder stucture for:"
const REF_STRUCTURE_MISSALIGN_MSG = "Refinement sturcture missalign for:"

export class ProofProvider extends BetterObservable<ProofProvider> {

  private rootGoalCache: ProofGoal[] = [];
  private goalToUriMap: Map<String, Uri> = new Map<String, Uri>();

  constructor(private models: Models, private theories: Theories) {
    super();
    theories.register(() => { this.refresh(); });
    models.register((uri) => { this.refresh(); });
    Promise.resolve(this.refresh());
  }

  private getReqThyGoalByUri(thyFileUri: Uri): ProofGoal {
    let proof_label = path.basename(IveUri.getFilenameWithoutExtension(thyFileUri));
    return new RequirementProofGoal(proof_label, thyFileUri, this, undefined);
  }

  private getRefThyGoalByUri(thyFileUri: Uri): ProofGoal | undefined {
    let goals: ProofGoal[] = [];

    const regex = /ref\/([^/]+)\/([^/]+)\/ref_(.+?)_rough_(.+?)\.thy$/;

    const match = regex.exec(thyFileUri.path);

    if (!match) {
        getLogger().debug(REF_STRUCTURE_MISSALIGN_MSG + " " +  thyFileUri.toString());
        return undefined;
    }

    const rootFolder = match[1];
    const subFolder  = match[2];
    const fileNameMatchingRootFolder = match[3];
    const fileNameMatchingSubFolder  = match[4];

    if (rootFolder != fileNameMatchingRootFolder || subFolder != fileNameMatchingSubFolder) {
      getLogger().warn(REF_NAME_MISSALIGN_WARN_MSG + " " + thyFileUri?.toString());
      return undefined;
    }

    return new RefinementProofGoal([subFolder, rootFolder], thyFileUri, this, undefined);
  }

  getUriByGoal(arg0: string) {
    return this.goalToUriMap.get(arg0);
  }

  public async refresh() {
    let sysmlFileUris = await IveUri.getFilesOfExtension(".sysml", this.models.getLocation(), true);

    let newGoalUriMap = new Map<String, Uri>();
    for (let smlf of sysmlFileUris) {
      newGoalUriMap.set(IveUri.getFilenameWithoutExtension(smlf), smlf)
    }
    this.goalToUriMap = newGoalUriMap

    let new_root_goals: ProofGoal[] = [];

    let refThyUri = Uri.joinPath(this.theories.getLocation(), "ref");
    let refThyFileUris = await IveUri.getFilesOfExtension(".thy", refThyUri, true);
    getLogger().info("Processing refinement count: " + refThyFileUris.length)

    for (let uri of refThyFileUris) {
      let existingProof = this.rootGoalCache?.filter(g => g.theoryFile.toString() == uri.toString())
      if (existingProof?.length === 1) {
        if (existingProof[0].proofState === ProofState.VERIFIED) {
          existingProof[0].proofState = ProofState.UNKNOWN;
        }
        new_root_goals.push(existingProof[0]);

      } else if (existingProof?.length === 0){
        let expected_thy_goal = this.getRefThyGoalByUri(uri)
        if (expected_thy_goal) {
          new_root_goals.push(expected_thy_goal);
        }
      } else {
        getLogger().error("Received two matching goals while updating gc.")
      }
    }

    let reqThyUri = Uri.joinPath(this.theories.getLocation(), "req");
    let reqThyFileUris = await IveUri.getFilesOfExtension(".thy", reqThyUri, true);

    for (let uri of reqThyFileUris) {
      let existingProof = this.rootGoalCache?.filter(g => g.theoryFile.toString() == uri.toString())
      if (existingProof?.length === 1) {
        if (existingProof[0].proofState === ProofState.VERIFIED) {
          existingProof[0].proofState = ProofState.UNKNOWN;
        }
        new_root_goals.push(existingProof[0]);
      } else if (existingProof?.length === 0) {
        new_root_goals.push(this.getReqThyGoalByUri(uri));
      } else {
        getLogger().error("Received two matching goals while updating gc.")
      }
    }

    let newGoalUris = new_root_goals.map(h => h.theoryFile);
    this.rootGoalCache?.filter(g => !newGoalUris.includes(g.theoryFile))
                       .forEach(g => { g.dispose() })
    this.rootGoalCache = new_root_goals.sort((a, b) => a.label!.toString().localeCompare(b.label!.toString()));

    this.onChange(this);
  }

  public async getRootGoals() {
    if (this.rootGoalCache.length === 0) {
      await this.refresh();
    }
    return this.rootGoalCache!;
  }

  getLatest(): ProofProvider | Promise<ProofProvider> {
    return this;
  }
}
