import * as path from 'path';
import { Uri, TreeItem, TreeItemCollapsibleState } from "vscode";
import { IveUri } from '../../util/IveUri';

export class ModelFile extends TreeItem {

  public name: String;

  constructor(uri: Uri, public packageDeclaration: string[]) {
    super(uri, TreeItemCollapsibleState.None);

    this.name = IveUri.getFilenameWithoutExtension(uri);

    this.command = { title: 'Open Model', command: 'vscode.open', arguments: [uri] };
    let icon = 'sysml.svg';
    this.iconPath = path.join(__filename, '..', '..', '..', '..', '..', '..', 'res', 'icons', icon);
    this.contextValue = 'model';
  }

  public getFullyQualifiedName() : string {
    return `${this.packageDeclaration.map(s => `${s}.`).join("")}${this.name}`;
  }

}
