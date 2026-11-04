import { getLogger } from "log4js";

export class Observable<E> {

  observers : Observer<E>[] = [];

  public register(observer: Observer<E>) {
    this.observers.push(observer);
  }

  public unregister(observer: Observer<E>) {
    let index = this.observers.indexOf(observer);
    if(index >= 0) {
      this.observers.splice(index, 1);
    }
  }

  public onChange(changed: E) {
    this.observers.forEach(observer => observer.notify(changed));
  }

}

export interface Observer<E> {

  notify(changed: E) : void;

}

export abstract class BetterObservable<E> {

  listener: ((_:E) => void)[] = [];

  public register(observer:((_:E) => void)) {
    this.listener.push(observer);
    return this.getLatest();
  }

  public unregister(observer:((_:E) => void)) {
    let index = this.listener.indexOf(observer);
    if(index >= 0) {
      this.listener.splice(index, 1);
    }
  }

  private queue?: NodeJS.Timeout;

  public onChange(changed: E) {
    if(this.queue !== undefined) {
      clearTimeout(this.queue);
    }

    this.queue = setTimeout(() => {
      getLogger().trace(`${this.constructor.name} has changed. Notifying all observers.`);
      this.listener.map((observer, i) => {
        try {
          observer(changed);
        }
        catch(err) {
          getLogger().error(err);
        }
      });
    }, 500);
  }

  abstract getLatest() : E | Promise<E>;

}
