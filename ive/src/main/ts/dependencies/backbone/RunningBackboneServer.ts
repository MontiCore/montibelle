import { getLogger } from "log4js";
import { Uri } from "vscode";
import { BackboneClient } from "../../ive/BackboneClient";
import { RunningServer } from "../RunningServer";

export class RunningBackboneServer implements RunningServer<BackboneClient> {

  constructor(
    readonly address: string,
    readonly backboneSource: Uri,
    readonly backboneTarget: Uri,
    readonly backboneHwls?: Uri)
  { }

  connect() : Promise<BackboneClient> {
    getLogger().trace(`Connecting to backbone server at "${this.address}"`);

    return new Promise(async (resolve, reject) =>
    {
      let client: BackboneClient | undefined;
      let tries = 10;
      let interval = 3000;
      do {
        try {
          client = new BackboneClient(this.address, this.backboneSource, this.backboneTarget, this.backboneHwls);
          await client.check();
          break;
        }
        catch(reason) {
          client = undefined;
          tries--;
          getLogger().warn(`Failed to connect to backbone server.` +
            ` Re-attempting every ${interval}ms for ${tries} more times. ${reason}.`);
          await new Promise(resolve => setTimeout(resolve, interval));
        }
      }
      while(tries > 0);

      if(client !== undefined) {
        getLogger().trace(`Successfully connected client to backbone server`);
        client.transformIfNeccessary();
        return resolve(client);
      }
      else {
        let reason = `Probably not online or misconfiguration.`;
        getLogger().warn(`Failed to reach backbone server. ${reason}.`);
        return reject(reason);
      }
    });
  }

}