import { createReadStream, PathLike, unwatchFile, watch, watchFile } from "fs";
import { getLogger } from "log4js";
import { createInterface } from "readline";
import { integer } from "vscode-languageclient";
import { BetterObservable } from "../util/Observable";

export class AutosledgiState extends BetterObservable<AutosledgiState> {

  public nrOfLemmas: integer | undefined = undefined;

  public currentLemma: integer | undefined = undefined;

  public percentage: integer | undefined = undefined;

  public done: boolean = false;

  public error: boolean = false;

  public errorMessage: string | undefined = undefined;

  private shutdownPattern: string = '.*?INFO\\s*?Shutting down\.\.\.'

  private errorPattern: string = '.*?ERROR\\s*?(?<message>.*)'

  private sessionPattern: string = '.*?INFO\\s*Session started\.'

  private progressPattern: string = '.*?INFO\\s*Loading theories (?<percentage>.*?)%\.\.'

  private lemmaPattern: string = '.*?INFO\\s*?Proving lemma (?<current>\\d+)/(?<total>\\d+)'

  constructor(private logfile: PathLike) {
    super();
    watchFile(logfile, { interval: 500 }, (cur, prev) => {
      if (cur.mtime != prev.mtime) {
        this.updateInBackground().finally(() => {
          this.onChange(this);
        });
      }
    });
  }

  getLatest(): AutosledgiState {
    return this;
  }

  public async waitFinsished(): Promise<void> {
    return new Promise<void>((resolve, reject) => {
      let check = (state: AutosledgiState) => {
        if(state.done) {
          this.unregister(check);
          resolve();
        }
        else if(state.error) {
          this.unregister(check);
          reject();
        }
      };
      this.register(check);
    });
  }

  private async updateInBackground() {
    const rl = createInterface({
      input: createReadStream(this.logfile),
      crlfDelay: Infinity
    });

    for await (const line of rl) {
      getLogger().trace(line);
      if(line.match(this.shutdownPattern)) {
        getLogger().trace(`Detected that autosledgi is shutting down`);
        unwatchFile(this.logfile);
        this.done = true;
      }
      else if(line.match(this.errorPattern)) {
        getLogger().trace(`Detected error in autosledgi run`);
        unwatchFile(this.logfile);
        var match = line.match(this.errorPattern);
        this.error = true;
        this.errorMessage = match?.groups?.message;
      }
      else if(line.match(this.lemmaPattern)) {
        getLogger().trace(`Detected lemma update`);
        var match = line.match(this.lemmaPattern);
        this.nrOfLemmas = parseInt(match!.groups!.total);
        this.currentLemma = parseInt(match!.groups!.current);
      }
      else if(line.match(this.sessionPattern)) {
        getLogger().trace(`Detected session start`);
        this.percentage = 20;
      }
      else if(line.match(this.progressPattern)) {
        getLogger().trace(`Detected percentage`);
        var match = line.match(this.progressPattern);
        let percentage: integer = parseInt(match!.groups!.percentage);
        this.percentage = 20 + ((this.currentLemma!-1)*80/100) + (80*percentage/(100*this.nrOfLemmas!));
      }
    }
  }

}