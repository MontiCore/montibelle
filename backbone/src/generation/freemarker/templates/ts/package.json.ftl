${signature("version")}
{
    "name": "@montibelle/backbone-rpc-client",
      "version": "${version}",
      "description": "A Json-RPC client to interact with the MontiBelle Backbone",
      "main": "out/index.js",
      "types": "out/index.d.ts",
      "scripts": {
        "prepare": "tsc",
        "watch": "tsc -watch -p ./"
      },
      "files": [
        "out/*"
      ],
      "repository": {
        "type": "git",
        "url": "git@git.rwth-aachen.de:montibelle/frontend/backbone.git"
      },
      "publishConfig": {
        "@montibelle:registry": "https://git.rwth-aachen.de/api/v4/projects/41628/packages/npm/"
      },
      "author": "",
      "license": "To be decided",
      "devDependencies": {
            "typescript": "^5.0.2"
      },
      "dependencies": {
        "@types/node-fetch": "^2.5.6",
        "node-fetch": "^2.6.0"
      }
}
