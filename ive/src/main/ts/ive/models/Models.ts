import { Disposable, FileSystemWatcher, RelativePattern, Uri, workspace } from 'vscode';
import { Concurrency } from '../../util/Concurrency';
import { IveUri } from '../../util/IveUri';
import { BetterObservable } from '../../util/Observable';
import { BackboneClient } from "../BackboneClient";
import { Theories } from '../theories/Theories';

export class Models extends BetterObservable<Models> implements Disposable {

  private __transformationNeccessary = true;

  private watcher: FileSystemWatcher;

  constructor(private location: Uri, private backboneClient: Promise<BackboneClient>, private theories: Theories) {
    super();

    let globPattern: RelativePattern = {
      baseUri: location,
      base: location.fsPath,
      pattern: '**/*'
    };

    this.watcher = workspace.createFileSystemWatcher(globPattern);
    this.watcher.onDidChange((uri: Uri) => {
      if (Models.isPackageOrModel(uri)) {
        this.__transformationNeccessary = true;
        this.onChange(this);
      }
    });
    this.watcher.onDidDelete((uri: Uri) => {
      if (Models.isPackageOrModel(uri)) {
        this.__transformationNeccessary = true;
        this.onChange(this);
      }
    });
    this.watcher.onDidCreate((uri: Uri) => {
      if (Models.isPackageOrModel(uri)) {
        this.__transformationNeccessary = true;
        this.onChange(this);
      }
    });
  }

  dispose() {
    this.watcher.dispose();
  }

  private isTransformationNeccessary = Concurrency.synchronize(async () => {
    let tmp = this.__transformationNeccessary;
    this.__transformationNeccessary = false;
    return tmp;
  });

  public async transformIfNeccessary(force: boolean = false) {
    await this.theories.clear();
    this.backboneClient.then(client => client.transform());
  }

  public getLocation(): Uri {
    return this.location;
  }

  private static isPackageOrModel(uri: Uri): boolean {
    return IveUri.isOrWasDirectory(uri) || uri.fsPath.endsWith(".arc") || uri.fsPath.endsWith(".sysml");
  }


  public getLatest(): Models | Promise<Models> {
    return this;
  }

}