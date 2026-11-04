import { getLogger } from "log4js";
import { Socket } from "net";


export class SocketUtil {

  public static async connect(port: number, address: string) : Promise<Socket> {
    return new Promise((resolve, reject) =>
    {
      const socket = new Socket();
      let tries = 5;
      let interval = 3000;
      let latestErr: Error;

      socket.addListener("close", async (had_error:boolean) => {
        let reason = had_error ? `Socket error` : `Socket was closed`;
        getLogger().trace(`Socket "${address}:${port}" closed.`, reason);

        if(had_error) {
          if(tries > 0) {
            getLogger().trace(`Re-attempting connection to socket at ${address}:${port} in ${interval}ms. ${tries} tries left.`)
            tries--;
            await new Promise(resolve => setTimeout(resolve, interval));
            socket.connect(port, address);
          }
          else {
            getLogger().trace(`Could not connect to socket at ${address}:${port}. Is the service up and running?`);
            return reject(latestErr);
          }
        }
      });

      socket.addListener("error", (err: Error) => {
        getLogger().trace(`Socket "${address}:${port}" encountered an error`, err);
        latestErr = err;
      });

      socket.addListener("ready", async (args:any[]) => {
        getLogger().trace(`Socket "${address}:${port}" connected.`
          + ` Listening for errors for ${interval}ms before proceeding.`, args);

        let didClose = false;
        socket.once("close", (had_error:boolean) => {                                 didClose = !had_error; });
        await new Promise(resolve => setTimeout(resolve, interval));
        if(didClose) {
          getLogger().trace(`Socket "${address}:${port}" was closed after connecting. Re-attempting connection.`)
          socket.connect(port, address);
        }
        else {
          getLogger().trace(`Socket "${address}:${port}" successfully connected.`, args);
          return resolve(socket);
        }
      });

      socket.connect(port, address);
    });
  }
}