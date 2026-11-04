import { assert } from 'console';
import * as path from 'path';
import { Uri, TreeItem, TreeItemCollapsibleState } from "vscode";
import { TheoryPackage } from './TheoryPackage';
import { TheoryFileType } from './TheoryFileType';
import { IveUri } from '../../util/IveUri';
import { existsSync } from 'fs';

export class TheoryFile extends TreeItem {

  readonly children: Thenable<TheoryFile[]>;

  readonly session: string;

  readonly name: string;

  public static isSPS(baseName: string): Boolean {
    return (
      baseName.startsWith("def_") &&
      !baseName.endsWith("_Input.thy") &&
      !baseName.endsWith("_Output.thy") &&
      !baseName.endsWith("_States.thy") &&
      !baseName.endsWith("_gen.thy")
    );
  }

  public static isRefinement(baseName: string): Boolean {
    return (
      baseName.startsWith("ref_") &&
      !baseName.endsWith("_StateMapping.thy") &&
      !baseName.endsWith("_arec.thy")
    );
  }

  private static getLabel(baseName: string, type: TheoryFileType): string {
    switch (type) {
      case TheoryFileType.SPS:
        return baseName.split("_").pop()!;
      case TheoryFileType.ATTACHEE:
        return baseName.split("_").pop()!;
      case TheoryFileType.REFINEMENT:
        var rough, refined, x;
        [refined, rough, ...x] = baseName.replace(/^ref_/, "").split("_rough_");
        assert(x.length === 0);
        return refined.split("_").pop() + " ⊑ " + rough.split("_").pop();
      case TheoryFileType.AREC:
        return "A.R.E.C.";
      case TheoryFileType.STATEMAPPING:
        return "State Mapping";
      case TheoryFileType.HWL:
        return baseName;
      default:
        return baseName;
    }
  }

  public constructor(
    public readonly uri: Uri,
    public readonly parent: TheoryPackage | TheoryFile | undefined,
    public readonly type: TheoryFileType,
    session?: string
  ) {
    super(TheoryFile.getLabel(IveUri.getFilenameWithoutExtension(uri), type));
    this.resourceUri = uri;
    this.contextValue = type.toString();
    this.command = { title: 'Open Theory', command: 'vscode.open', arguments: [uri] };
    this.iconPath = path.join(__filename, '..', '..', '..', '..', '..', '..', 'res', 'icons', 'isabelle.png');
    this.collapsibleState = TreeItemCollapsibleState.None;

    this.session = session ?? IveUri.extractSessionFor(uri);
    this.name = IveUri.getFilenameWithoutExtension(uri);

    if (type === TheoryFileType.SPS) {
      var folderContainingTheSps = IveUri.getParent(IveUri.getParent(this.uri));

      this.children = IveUri.getFilesOfExtension(".thy", folderContainingTheSps, true)
        .then(uris =>
          Promise.resolve(
            uris
              .filter(uri =>
                this.isParentOver(uri) ||
                this.isComposedOf(uri) ||
                this.isDefinitionInRefinement(uri)
              )
              .map(uri => {
                var type: TheoryFileType;
                if (this.isParentOver(uri)) {
                  type = TheoryFileType.ATTACHEE;
                }
                else if (this.isDefinitionInRefinement(uri)) {
                  type = TheoryFileType.REFINEMENT;
                }
                else                             {
                  type = TheoryFileType.SPS;
                }
                return new TheoryFile(uri, this, type);
              })
          )
        );

      this.collapsibleState = TreeItemCollapsibleState.Collapsed;
    }
    else if (this.type == TheoryFileType.REFINEMENT) {
      var parentFolder = IveUri.getParent(this.uri);
      var res: TheoryFile[] = [];
      let arecUri = IveUri.appendUri(parentFolder, `${this.name}_arec.thy`);
      let stateMapTheory = IveUri.appendUri(parentFolder, `${this.name}_StateMapping.thy`);
      if (existsSync(arecUri.fsPath)) {
        res.push(new TheoryFile(arecUri, this, TheoryFileType.AREC));
      }
      if (existsSync(stateMapTheory.fsPath)) {
        res.push(new TheoryFile(stateMapTheory, this, TheoryFileType.STATEMAPPING));
      }

      this.children = Promise.resolve(res);

      this.collapsibleState = res.length > 0 ? TreeItemCollapsibleState.Collapsed : TreeItemCollapsibleState.None;
    }
    else {
      this.children = Promise.resolve([]);
    }
  }

  private isComposedOf(theory: Uri): Boolean {
    let theoryNameWithExtension = path.basename(theory.fsPath);
    return new RegExp(`^${this.name}_[a-z]\w*(?<!_arec.thy)$`).test(theoryNameWithExtension);
  }

  private isParentOver(theory: Uri): Boolean {
    let theoryNameWithExtension = path.basename(theory.fsPath);
    return new RegExp(`^${this.name}_(Input|Output|States).thy$`).test(theoryNameWithExtension);
  }

  private isDefinitionInRefinement(potentialRefinementTheory: Uri): Boolean {


    let roughFqn = TheoryFile.deriveFromRelativeLocation(this.uri, potentialRefinementTheory);

    if (roughFqn.length > 3 && roughFqn[0] === ".." && roughFqn[1] === ".." && roughFqn[2] === "refines") {
      roughFqn = roughFqn.slice(3, -1);
      let theoryNameWithExtension = path.basename(potentialRefinementTheory.fsPath);
      return `ref_${this.fqn().join("_")}_rough_${roughFqn.join("_")}.thy` === theoryNameWithExtension;
    }
    else {
      return false;
    }
  }

  private fqn(): string[] {
    let fqn: string[] = [];
    let accu: TheoryFile | TheoryPackage = this;

    fqn.push(this.label!!.toString());
    while (accu.parent !== undefined) {
      accu = accu.parent!!;
      if (accu instanceof TheoryPackage) {
        fqn.push(path.basename(accu.uri.fsPath));
      }
      else {
        fqn.push(accu.label!!.toString());
      }
    }

    return fqn.reverse();
  }

  private static deriveFromRelativeLocation(sps: Uri, refinement: Uri): string[] {
    let rel = path.relative(sps.fsPath, refinement.fsPath);
    let fqn = rel.split(path.sep);
    return fqn;
  }

}
