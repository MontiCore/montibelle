import { readFileSync, watchFile, createReadStream, unwatchFile } from "fs";
import { getLogger } from "log4js";
import { createInterface } from "readline";
import { integer } from "vscode-languageclient";
import { BetterObservable } from "../util/Observable";

export class TransformState extends BetterObservable<TransformState> {

  public totalComponents: integer = -1;
  public processedComponents: integer = 0;

  public error: boolean = false;
  public finished: boolean = false;

  constructor(public readonly logLocation: string) {
    super();
    watchFile(logLocation, { interval: 500 }, (cur, prev) => {
      getLogger().trace(`Observing ${logLocation} for changes..`);
      if (cur.mtime != prev.mtime) {
        this.update(logLocation).finally(() => {
          this.onChange(this);
        });
      }
    });
  }

  public async update(logLocation: string) {
    const fileStream = createReadStream(logLocation);

    const rl = createInterface({
      input: fileStream,
      crlfDelay: Infinity
    });

    for await (const line of rl) {
      let totalComponentsPattern = 'SysMLProvider ([0-9]+) components were found';
      let transformingPattern = "SysMLProvider Transforming ([0-9]+) of ([0-9]+):";
      let errorPattern = /^\[ERROR\]|BUILD FAILED/i;
      let finishedPattern = /BUILD SUCCESSFUL|SysMLProvider All components were transformed/i;

      let matchTotalComps = line.match(totalComponentsPattern);
      if (matchTotalComps != null) {
        this.totalComponents = parseInt(matchTotalComps[1]);
      }

      let matchTransforming = line.match(transformingPattern);
      if (matchTransforming != null) {
        this.processedComponents = parseInt(matchTransforming[1]) - 1;
      }

      if (line.match(errorPattern) != null) {
        this.finished = true;
        this.error = true;
        unwatchFile(logLocation);
      }

      if (line.match(finishedPattern) != null) {
        this.finished = true;
        unwatchFile(logLocation);
      }
    }
  }

  public async waitFinsished(): Promise<TransformState> {
    while (!this.finished) {
      await new Promise(resolve => setTimeout(resolve, 500));
    }
    return this;
  }

  public getLatest(): TransformState | Promise<TransformState> {
    return this;
  }
}