import fetch from 'node-fetch';

export class JsonRpcClient {

  private counter: number = 1;

  private host: string;

  constructor(host: string){
    this.host = host;
  }

  protected async sendRequest(route: string, method: string, params: any | any[]): Promise<any> {
    return new Promise((resolve, reject) =>
      fetch(`${this.host}/${route}`, {
        method: "POST",
        headers: {
          "Content-Type": "application/json"
        },
        body: JSON.stringify(
          {
            "jsonrpc": "2.0",
            "method": method,
            "params": params,
            "id": this.counter++
          }
        )
      })
      .then(res => {
        if (res.status == 200) {
          res.json().then(json => resolve(json));
        }
        else {
          const contentType = res.headers.get("Content-Type");
          if(res.status == 500 && contentType && contentType === "application/json-rpc") {
            res.json().then(json => {
              if("error" in json) {
                reject(json.error);
              }
              else {
                reject(res.status + " " + res.statusText);
              }
            });
          }
          else {
            reject(res.status + " " + res.statusText);
          }
        }
      })
      .catch(err => reject(err))
    );
  }

}
