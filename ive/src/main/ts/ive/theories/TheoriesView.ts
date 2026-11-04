import { commands, Disposable, InputBoxOptions, TreeView, window } from "vscode";
import { Theories } from "./Theories";
import { BetterObservable } from "../../util/Observable";
import { ModelFile } from "../models/ModelFile";
import { ModelPackage } from "../models/ModelPackage";
import { TheoriesProvider } from "./TheoriesProvider";
import { TheoryFile } from "./TheoryFile";
import { TheoryPackage } from "./TheoryPackage";
import { getWorkspace } from "../../extension";

export class TheoriesView implements Disposable {

  public provider: TheoriesProvider;

  private view: TreeView<TheoryFile| TheoryPackage>;

  private commands: Disposable[] = [];

  public constructor(theories: Theories) {
    this.provider = new TheoriesProvider(theories);
    this.view = window.createTreeView('theoriesView',
    {
      treeDataProvider : this.provider,
      showCollapseAll : true
    });

    this.commands.push(commands.registerCommand('ive.theories.refresh', async () => {
      this.provider.refresh();
    }));

    this.commands.push(commands.registerCommand('ive.hwl.addPrologue', async (theory: TheoryFile) => {
      await TheoriesView.addHwl(theory, true);
    }));

    this.commands.push(commands.registerCommand('ive.hwl.addEpilogue', async (theory: TheoryFile) => {
      await TheoriesView.addHwl(theory, false);
    }));

    this.commands.push(commands.registerCommand('ive.hwl.remove', async hwl => {
      await TheoriesView.removeHwl(hwl);
    }));
  }

  public dispose() {
    this.commands.forEach((command) => command.dispose());
    this.view.dispose();
  }

  public static async addHwl(theory: TheoryFile, isPrologue: Boolean) {
    let options: InputBoxOptions = {
      prompt: isPrologue ?
        `Specify the HWL you want to be imported into ${theory.name} in the form of <session-name>.<hwl-name>` :
        `Specify the HWL you want to extend ${theory.name} with in the form of <session-name>.<hwl-name>`,

      validateInput: (val) => {
        if (val.includes(".")) {
          let res = val.split(".");
          if (res[0] !== "" && res[1] !== "") {
            return undefined;
          }
        }
        return "Input in not in correct form. <session-name>.<hwl-name> required";
      }
    };

    let res = await window.showInputBox(options);
    if (res === undefined) {
      return;
    }

    let hwlSession = res.split(".")[0];
    let hwlName = res.split(".")[1];

    let input = {
      targetTheorySession: theory.session,
      targetTheoryName: theory.name,
      hwlType: isPrologue,
      hwlSession: hwlSession,
      hwlName: hwlName
    };

    await getWorkspace()!.getBackboneClient().then(client => client.addHwl(input));
  }

  public static async removeHwl(hwl: TheoryFile) {

  }

}
