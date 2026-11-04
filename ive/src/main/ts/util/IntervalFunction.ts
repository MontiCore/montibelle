import { Disposable } from "vscode";

export class IntervalFunction implements Disposable {

  private interval: NodeJS.Timeout | undefined;

  constructor(private funct: () => void, private intervalMs: number) {
    this.interval = setInterval(funct, intervalMs);
  }

  dispose() {
    if (this.interval) {
      clearInterval(this.interval);
    }
  }

}