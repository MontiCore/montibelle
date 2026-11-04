import { spawnSync, SpawnSyncOptionsWithStringEncoding } from "child_process";
import { getLogger } from "log4js";
import { Config } from "../ive/Config";

function isExecutableAvailable(executable: string) : boolean {
	if (process.platform === "win32") {
		let args = [executable];
		return spawnSync("where", args).status === 0;
  }
  else {
		let args = ["-v", executable];
		const spawnOptions: SpawnSyncOptionsWithStringEncoding = { shell: true, encoding: "utf8" };
		return spawnSync("command", args, spawnOptions).status === 0;
	}
}

export function showDependencyWarnings() : boolean {
  let dependencies : string[][] = [];
  if(Config.getBackboneMode() === Config.Mode.DOCKER) {
    dependencies.push(["docker", "Docker"]);
  }
  if(Config.getBackboneMode() === Config.Mode.LOCAL) {
    dependencies.push(['java', 'Java 11 or higher']);

    if(Config.getBackboneMode() === Config.Mode.LOCAL) {
      dependencies.push(['python3', 'Python 3'], ['isabelle', 'Isabelle 2023']);
    }
  }

  let allAvailable = true;

  for (const dep of dependencies) {
    let executable = dep[0];
    let description = dep[1];

    if(!isExecutableAvailable(executable)) {
      getLogger("user").error(`Cannot find ${executable}. Is ${description} installed and on $PATH?`);
      allAvailable = false;
    }
  }

  return allAvailable;
}
