export namespace Concurrency {

  export const synchronize = <T>(funct: (...p: any) => PromiseLike<T>) => {
    let inFlight: Promise<T> | false = false;

    return (...p: any) => {
      if (!inFlight) {
        inFlight = (async () => {
          try {
            return await funct(...p);
          } finally {
            inFlight = false;
          }
        })();
      }
      return inFlight;
    };
  };

}