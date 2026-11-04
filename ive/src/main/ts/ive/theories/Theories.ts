import { getLogger } from 'log4js';
import { Disposable, FileSystemWatcher, Uri, workspace } from 'vscode';
import { ConfigurationRequest } from 'vscode-languageclient';
import { IveUri } from '../../util/IveUri';
import { BetterObservable } from '../../util/Observable';
import { Config } from '../Config';

export class Theories extends BetterObservable<Theories> implements Disposable {

  private watcher: FileSystemWatcher;
  private static instance: Theories | undefined;

  constructor(private location: Uri)
  {
    super();
    this.watcher = workspace.createFileSystemWatcher("**/*.thy");
    this.watcher.onDidChange(_ => {
      this.onChange(this);
    });
    this.watcher.onDidDelete(_ => {
      this.onChange(this);
    });
    this.watcher.onDidCreate((uri: Uri) => {
      this.onChange(this);
    });
    Theories.instance = this;
  }

  public static getInstance() {
    return this.instance;
  }

  dispose() {
    this.watcher.dispose();
  }

  public getLocation() : Uri {
    return this.location;
  }

  public getSpsLocation() : Uri {
    return IveUri.appendUri(this.location, "sps");
  }

  public clear() {
    getLogger().trace(`Clearing target directory ${this.getLocation()}`);
    IveUri.clearDirectory(this.getLocation());
  }


  public getLatest(): Theories {
    return this;
  }

}

export class TheoriesLocation extends BetterObservable<Uri> {

  constructor(private localWorkspace: Uri)
  {
    super();
    workspace.onDidChangeConfiguration(config => {
      if(config.affectsConfiguration(Config.getCompilationTargetKey())) {
        this.onChange(IveUri.appendUri(localWorkspace, Config.getTheoryTarget()));
      }
    });
  }


  public getLatest(): Uri {
    return IveUri.appendUri(this.localWorkspace, Config.getTheoryTarget());
  }

}