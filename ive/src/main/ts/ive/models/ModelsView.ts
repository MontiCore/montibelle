import { writeFile, existsSync, mkdir, unlink } from "fs";
import { getLogger } from "log4js";
import { commands, Disposable, InputBoxOptions, TreeView, Uri, window } from "vscode";
import { IveUri } from "../../util/IveUri";
import { Validation } from "../../util/Validation";
import { Models } from "./Models";
import { ModelsProvider } from "./ModelsProvider";
import { ModelFile } from "./ModelFile";
import { ModelPackage } from "./ModelPackage";
export class ModelsView implements Disposable {

  public provider: ModelsProvider;

  private view: TreeView<ModelFile | ModelPackage>;

  private commands: Disposable[] = [];

  public constructor(private models: Models, private resources: Uri) {

    this.provider = new ModelsProvider(models);
    this.view = window.createTreeView('modelsView',
      {
        treeDataProvider: this.provider,
        canSelectMany: true,
        showCollapseAll: true
      });

    this.provider.register(_ => {
      getLogger().trace("Models changed, attempting transformation.");
      this.models.transformIfNeccessary().finally(() => getLogger().trace("Completed transformation."));
    });


    this.commands.push(commands.registerCommand('ive.models.refresh', async () => this.provider.refresh()));

    this.commands.push(commands.registerCommand('ive.models.addFile', async (modelPackage: ModelPackage, type) => {
      let path = modelPackage?.uri ?? this.models.getLocation();
      let options: InputBoxOptions = {
        prompt: `Specify file name`,
        placeHolder: "<filename>.<extension>",
        validateInput: (value) => {
          if (!Validation.isValidFileName(value)) {
            return "Invalid file name";
          }
          if (existsSync(IveUri.appendUri(path, value).fsPath)) {
            return "File already exists";
          }
          return undefined;
        }
      };
      window.showInputBox(options).then(value => {
        if (value !== undefined) {
          let file = IveUri.appendUri(path, value);
          mkdir(IveUri.getParent(file).fsPath, (err) => {
            if (!err || err.code === 'EEXIST') {
              writeFile(file.fsPath, "", async (err) => {
                if (!err) {
                  window.showTextDocument(file);
                }
                else {
                  getLogger("user").error(err.message);
                }
              });
            }
            else {
              getLogger("user").error(err.message);
            }
          });
        }
      });
    }));

    this.commands.push(commands.registerCommand('ive.models.addComponent', async (modelPackage: ModelPackage, type) => {
      let options: InputBoxOptions = {
        prompt: `Specify a name for the model artifact`,
        placeHolder: "ModelName",
        validateInput: (value) => {
          if (!Validation.isValidComponentName(value)) {
            return "Invalid artifact name";
          }
          if (existsSync(IveUri.appendUri(modelPackage.uri, "/", value + ".sysml").fsPath)) {
            return "Artifact already exists";
          }
          return undefined;
        }
      };
      window.showInputBox(options).then(value => {
        if (value !== undefined) {
          let file = IveUri.appendUri(modelPackage.uri, value + ".sysml");
          window.showTextDocument(file);
        }
      });
    }));

    this.commands.push(commands.registerCommand('ive.models.addPackage', async (_package: ModelPackage, type) => {
      this.addPackage(_package.uri);
    }));

    this.commands.push(commands.registerCommand('ive.models.addRootPackage', async () => {
      this.addPackage(this.models.getLocation());
    }));

    this.commands.push(commands.registerCommand('ive.models.delete', async (modelFile: ModelFile, type) => {
      let path = modelFile.resourceUri;
      if (path !== undefined) {
        unlink(path.fsPath, async (err) => {
          if (err) {
            getLogger("user").error("Could not delete artifact: " + err.message);
          }
        });
      }
    }));

    this.commands.push(commands.registerCommand('ive.models.transform', async () => {
      this.models.transformIfNeccessary(true);
    }));
  }

  public dispose() {
    this.commands.forEach((command) => command.dispose());
    this.view.dispose();
  }

  private addPackage(path: Uri) {
    let options: InputBoxOptions = {
      prompt: `Specify package name`,
      placeHolder: "",
      validateInput: (value) => {
        if (!Validation.isValidPackageName(value)) {
          return "Invalid package name";
        }
        if (existsSync(IveUri.appendUri(path, value).fsPath)) {
          return "Package already exists";
        }
        return undefined;
      }
    };
    window.showInputBox(options).then(value => {
      if (value !== undefined) {
        mkdir(IveUri.appendUri(path, value).fsPath, async (err) => {
          if (err) {
            getLogger("user").error(err.message);
          }
        });
      }
    });
  }

}
