import { RunningServer } from "./RunningServer";

export interface Server<ClientType> {

  start() : Promise<RunningServer<ClientType>>;

}