import { statSync } from "fs";
import * as path from 'path';
import { ThemeIcon, TreeItem, TreeItemCollapsibleState, Uri } from "vscode";
import { IveUri } from "../../util/IveUri";
import { ModelFile } from "./ModelFile";

export class ModelPackage extends TreeItem {

  parent? : ModelPackage;

  children : Thenable<(ModelPackage | ModelFile)[]>;

  packageDeclaration: string[];

  constructor(public uri: Uri, parent? : ModelPackage) {
    super(uri, TreeItemCollapsibleState.Collapsed);
    this.contextValue = 'package';
    this.iconPath = new ThemeIcon('package');

    this.parent = parent;
    if(parent) {
      this.packageDeclaration = [...parent.packageDeclaration, IveUri.getFilenameWithoutExtension(uri)];
    }
    else {
      this.packageDeclaration = [IveUri.getFilenameWithoutExtension(uri)];
    }

    this.children = IveUri.readdir(uri).then(fileUris =>
      Promise.resolve(
        fileUris
          .filter(fileUri => {
            let fileInfo = statSync(fileUri.fsPath);
            return fileInfo.isDirectory() || fileInfo.isFile() && /\.(arc|sysml)$/.test(path.basename(fileUri.fsPath));
          })
          .map(fileUri => {
            if(statSync(fileUri.fsPath).isDirectory()) {
              return new ModelPackage(fileUri, this);
            }
            else {
              return new ModelFile(fileUri, this.packageDeclaration);
            }
          })
      )
    );
  }

}
