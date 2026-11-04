import { statSync } from "fs";
import * as path from 'path';
import { Event, EventEmitter, TreeDataProvider, TreeItem, Uri } from 'vscode';
import { IveUri } from '../../util/IveUri';
import { BetterObservable } from '../../util/Observable';
import { ModelFile } from './ModelFile';
import { ModelPackage } from './ModelPackage';
import { Models } from './Models';

export class ModelsProvider
  extends BetterObservable<(ModelFile | ModelPackage)[]>
  implements TreeDataProvider<ModelPackage | ModelFile> {

  private _changeEventEmitter : EventEmitter<ModelPackage | null>;

  private modelSource: Uri;

  constructor(private models : Models) {
    super();

    this._changeEventEmitter = new EventEmitter<ModelPackage | null>();
    this.onDidChangeTreeData = this._changeEventEmitter.event;
    this.modelSource = models.getLocation();

    models.register((observable: Models) => {
      this.modelSource = observable.getLocation();
      this.refresh();
      this.getChildren().then(result => this.onChange(result));
    });
  }

  public refresh() : void {
    this._changeEventEmitter.fire(null);
  }


  public getLatest(): Promise<(ModelFile | ModelPackage)[]> {
    return this.getChildren();
  }


  onDidChangeTreeData?: Event<ModelPackage | undefined | null>;

	getTreeItem(element: ModelFile | ModelPackage): TreeItem | Thenable<TreeItem> {
    return element;
	}

	async getChildren(element?: ModelPackage): Promise<(ModelFile | ModelPackage)[]> {
    if(element) {
      return Promise.resolve(element.children);
    }
    else {
      let children : (ModelPackage | ModelFile)[] = [];

      await IveUri.readdir(this.modelSource).then(fileUris =>
        children = fileUris
          .filter(fileUri => {
            let fileInfo = statSync(fileUri.fsPath);
            return fileInfo.isDirectory() || fileInfo.isFile() && /\.(arc|sysml)$/.test(path.basename(fileUri.fsPath));
          })
          .map(fileUri => {
            if(statSync(fileUri.fsPath).isDirectory()) {
              return new ModelPackage(fileUri);
            }
            else {
              return new ModelFile(fileUri, []);
            }
          })
      );

      return Promise.resolve(children);
    }
  }

}
