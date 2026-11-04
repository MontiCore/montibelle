import * as fs from 'fs';
import * as path from 'path';
import { RelativePattern, Uri, workspace } from 'vscode';
import { InvalidModelException } from '../ive/errors/invalidModelException';

export namespace IveUri {

  export function isOrWasDirectory(uri: Uri) : boolean {
    return path.basename(uri.fsPath) === IveUri.getFilenameWithoutExtension(uri);
  }

  export function getParent(uri: Uri): Uri {
    return Uri.file(path.dirname(uri.fsPath));
  }

  export function extractSessionFor(uri: Uri) {
    var folderWithRoot = uri;
    var stat = fs.statSync(uri.fsPath);

    if (stat.isFile()) {
      if (path.basename(uri.fsPath).endsWith(".thy")) {
        folderWithRoot = IveUri.getParent(uri);
      }
      else {
        throw new Error(`Tried to calculate session for non-theory file ${uri}`);
      }
    }

    const rootFile = IveUri.appendUri(folderWithRoot, "ROOT");
    const rootContent = fs.readFileSync(rootFile.fsPath, "utf-8");
    const regexMatch = /session\s"(\w+)"/g.exec(rootContent);
    if (regexMatch) {
      return regexMatch[1];
    }
    else {
      throw new Error(`Cannot find session declaration for ${uri} in ${rootFile}`);
    }
  }

  export function getFilenameWithoutExtension(uri: Uri): string {
    return path.basename(uri.fsPath).split('.')[0];
  }

  export function appendUri(head: Uri, ...tails: string[]): Uri {
    return Uri.file(path.join(Uri.parse(head.toString()).fsPath, ...tails));
  }

  export function createUri(head: String, ...tails: string[]): Uri {
    return Uri.file(path.join(Uri.parse(head.toString()).fsPath, ...tails));
  }

  export function clearDirectory(dir: Uri) {
    if (fs.existsSync(dir.fsPath)) {
      fs.readdirSync(dir.fsPath).forEach(file => {
        if (!file.startsWith(".")) {
          fs.unlink(path.join(dir.fsPath, file), err => {
            if (err) {
              throw err;
            }
          });
        }
      });
    }
  }

  export function getFilesOfExtension(extension: string, root?: Uri, recursiveFromRoot: boolean = false): Thenable<Uri[]> {
    let globalPattern: RelativePattern | string;
    if (root) {
      if (recursiveFromRoot) {
        globalPattern = { baseUri: root, base: root.fsPath, pattern: `**/*${extension}` };
      } else {
        globalPattern = { baseUri: root, base: root.fsPath, pattern: `*${extension}` };
      }
    } else {
      globalPattern = `**/*${extension}`;
    }
    return workspace.findFiles(globalPattern).then(
      uris => {
        return uris;
      },
      () => {
        return [];
      }
    );
  }

  export function readdir(uri: Uri): Promise<Uri[]> {
    return new Promise(async (resolve, reject) => {
      if (await new Promise<boolean>(resolve => fs.access(uri.fsPath, (err) => resolve(err ? false : true)))) {
        fs.readdir(uri.fsPath, (err, filenames) => {
          return err != null ? reject(err) : resolve(filenames.map(name => IveUri.appendUri(uri, name)));
        });
      }
      else {
        return resolve([]);
      }
    });
  }
}
