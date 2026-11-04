export interface RunningServer<ClientType> {

  connect() : Promise<ClientType>;

}