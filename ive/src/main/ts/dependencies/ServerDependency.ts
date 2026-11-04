import { Server } from "./Server";

export interface ServerDependency<ClientType> {

  download() : Promise<Server<ClientType>>

}