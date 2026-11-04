import { statSync } from 'fs';
import { Event, EventEmitter, TreeDataProvider, TreeItem, Uri } from 'vscode';
import { IveUri } from '../../util/IveUri';
import { BetterObservable } from '../../util/Observable';
import { ModelFile } from '../models/ModelFile';
import { ModelPackage } from '../models/ModelPackage';
import { Theories } from './Theories';
import { TheoryFile } from './TheoryFile';
import { TheoryFileType } from './TheoryFileType';
import { TheoryPackage } from './TheoryPackage';


export class TheoriesProvider extends BetterObservable<(TheoryFile | TheoryPackage)[]>
  implements TreeDataProvider<TheoryFile | TheoryPackage> {

  private _changeEventEmitter: EventEmitter<TheoryFile | null>;

  private definitionsLocation: Uri;

  constructor(theories: Theories) {
    super();

    this._changeEventEmitter = new EventEmitter<TheoryFile | null>();
    this.onDidChangeTreeData = this._changeEventEmitter.event;
    this.definitionsLocation = theories.getSpsLocation();

    theories.register((theories) => {
      this.definitionsLocation = theories.getSpsLocation();
      this.refresh();
      this.getChildren().then(children => this.onChange(children));
    });

  }

  public refresh(): void {
    this._changeEventEmitter.fire(null);
  }


  public getLatest(): Promise<(TheoryFile | TheoryPackage)[]> {
    return this.getChildren();
  }


  onDidChangeTreeData?: Event<TheoryFile | undefined | null>;

  getTreeItem(element: TheoryFile): TreeItem | Thenable<TreeItem> {
    return element;
  }

  async getChildren(element?: TheoryFile | TheoryPackage): Promise<(TheoryFile | TheoryPackage)[]> {
    if (element && element instanceof TheoryFile) {
      return Promise.resolve(element.children);
    }
    else if (element && element instanceof TheoryPackage) {
      return Promise.resolve(element.children);
    }
    else {
      return IveUri
        .readdir(this.definitionsLocation)
        .then(fileUris =>
          Promise.resolve(
            fileUris
              .filter(fileUri => statSync(fileUri.fsPath).isDirectory())
              .map(fileUri => {
                var definitionTheoryUri = TheoryPackage.getDefinitionIfPresent(fileUri);
                if (definitionTheoryUri !== null) {
                  return new TheoryFile(definitionTheoryUri, undefined, TheoryFileType.SPS);
                }
                else {
                  return new TheoryPackage(fileUri, this.definitionsLocation, undefined);
                }
              })
          )
        );
    }
  }

}
