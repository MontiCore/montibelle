import { Range, Uri, workspace, WorkspaceEdit } from 'vscode';

export namespace TextEditing{
    export async function replace(find: string, replace: string, file: Uri) {
        await workspace.openTextDocument(file).then(
            async textDocument => {
                let content = textDocument.getText();
                content = content.replace(find, replace);
                let firstLine = textDocument.lineAt(0);
                var lastLine = textDocument.lineAt(textDocument.lineCount - 1);
                var textRange : Range = new Range(0,
                firstLine.range.start.character,
                textDocument.lineCount - 1,
                lastLine.range.end.character);
                let edit : WorkspaceEdit = new WorkspaceEdit();
                edit.replace(file, textRange, content);
                await workspace.applyEdit(edit);
                textDocument.save();
            }
        );
    }

    export function fillEnvironmentTemplate(str: string){
        const envRegex = /[$][{]env:([^}]+)[}]/g;
        let conf = str;
        let m;

        do {
            m = envRegex.exec(conf);
            if (m) {
                let env = process.env[m[1]];
                if(env){
                    conf = conf.replace(m[0], env);
                }else{
                    console.error("Can not find environment variable " + m[1]);
                }
            }
        } while (m);

        return conf;
    }
}
