import { join } from 'path';
import { Disposable, ExtensionContext, TaskGroup, Uri } from 'vscode';
import { Theories, TheoriesLocation } from '../ive/theories/Theories';
import { Models } from './models/Models';
import { ModelsView } from './models/ModelsView';
import { TheoriesView } from './theories/TheoriesView';
import { Workspace } from './Workspace';
import { ProofView } from './proofView/ProofView';
import { ProofProvider } from './proofView/ProofProvider';

export class SidebarView implements Disposable {

  private modelsView: ModelsView;

  private proofView?: ProofView;

  private theoriesView: TheoriesView;

  public constructor(
    context: ExtensionContext,
    private models: Models,
    private theories: Theories,
    private theoriesLocation: TheoriesLocation,
    private iveWorkspace: Workspace)
  {
    let resources = Uri.file(join(context.extensionPath, 'res'));
    this.modelsView = new ModelsView(this.models, resources);

    this.proofView = new ProofView(new ProofProvider(this.models, theories));
    this.proofView?.initProofs();

    this.theoriesView = new TheoriesView(this.theories);
  }

  public dispose() {
    this.modelsView.dispose();
    this.proofView?.dispose();
    this.theoriesView.dispose();
  }
}
