import * as path from 'path';
import { TreeItem, TreeItemCollapsibleState, Uri } from "vscode";
import { TheoryFile } from "./TheoryFile";
import { TheoryFileType } from './TheoryFileType';
import { IveUri } from "../../util/IveUri";
import { readdirSync, statSync } from "fs";
import { ModelFile } from '../models/ModelFile';
import { ModelPackage } from '../models/ModelPackage';

export class TheoryPackage extends TreeItem {

  parent?: TheoryPackage;

  children: Thenable<(TheoryPackage | TheoryFile)[]>;

  public static getDefinitionIfPresent(uri: Uri): Uri | null {
    var result: Uri | null = null;
    if (statSync(uri.fsPath).isDirectory()) {
      readdirSync(uri.fsPath).forEach(file => {
        if (TheoryFile.isSPS(file)) {
          result = IveUri.appendUri(uri, file);
        }
      });
    }
    return result;
  }

  public static async filter<E>(arr: E[], predicate: ((_: E) => Promise<boolean>)): Promise<E[]> {
    const results = await Promise.all(arr.map(predicate));
    return arr.filter((_, index) => results[index]);
  }

  public constructor(public uri: Uri, definitions: Uri, parent?: TheoryPackage) {
    super(uri, TreeItemCollapsibleState.Expanded);

    this.parent = parent;

    this.children = IveUri
      .readdir(uri)
      .then(fileUris =>
        Promise.resolve(
          fileUris
            .filter(fileUri => statSync(fileUri.fsPath).isDirectory())
            .map(fileUri => {
              var definitionTheoryUri = TheoryPackage.getDefinitionIfPresent(fileUri);
              if (definitionTheoryUri !== null) {
                return new TheoryFile(definitionTheoryUri, this, TheoryFileType.SPS);
              }
              else {
                return new TheoryPackage(fileUri, definitions, this);
              }
            })
        )
      );

    this.iconPath = {
      light: path.join(__filename, '..', '..', '..', '..', '..', '..', 'res', 'icons', 'light', 'folder.svg'),
      dark: path.join(__filename, '..', '..', '..', '..', '..', '..', 'res', 'icons', 'dark', 'folder.svg')
    };
  }

}
