const { exit } = require("process");

/**
 * This script compares the version of the backbone-server (Maven/Java) and backbone-client (NPM/TypeScript) dependency.
 */
console.log('Comparing server and client version numbers for the "backbone" dependency.');

versionKey = "ive.dependencies.backboneServer.cVersion";

packageJson = require("../package.json");
serverVersion = packageJson.contributes.configuration.properties[versionKey].default;
clientVersion = packageJson.dependencies["@montibelle/backbone-rpc-client"];

// Extract SemVer, i.e. <Major>.<Minor>.<Patch> - Rest cannot be compared anyway
regex = /^(?<semver>[1-9][0-9]*\.(?:0|[1-9][0-9]*)\.(?:0|[1-9][0-9]*))(-(?<snapshot>.*))?$/;
serverVersion = regex.exec(serverVersion).groups.semver;
clientVersion = regex.exec(clientVersion).groups.semver;

if(serverVersion !== clientVersion) {
  console.error(`Version mismatch: Default for server was ${serverVersion}, client was ${clientVersion}!`);
  console.error(`Change "${versionKey}" and/or "@montibelle/backbone-rpc-client" to matching versions.`);
  exit(1);
}

console.log("Success: Server and client versions are consistent.");
