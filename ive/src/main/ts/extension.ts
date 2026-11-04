import { configure, getLogger } from 'log4js';
import { commands, ExtensionContext, Task, tasks, Uri, ViewColumn, window, workspace } from 'vscode';
import { Config } from './ive/Config';
import { Workspace } from './ive/Workspace';
import { showDependencyWarnings } from './util/DependencyCheck';
import { IveUri } from './util/IveUri';
import * as path from 'path';

let currentWorkspace: Workspace | undefined;

export function activate(context: ExtensionContext) {
  setupLog(
    Uri.file(
      path.join(
        workspace.workspaceFolders![0].uri.fsPath,
        Config.getTarget(),
        "logs"
      )
    ),
    "ive.log"
  );

  if (Config.getShowWelcome()) {
    let uri = Uri.file(context.asAbsolutePath("README.md"));
    commands.executeCommand('markdown.showPreview', uri);
  }

  if (Config.getShowAIMontibelle()) {
    openAiMontibelleWebview(context);
  }

  initializeWorkspaceIfOpen(context);

  workspace.onDidChangeWorkspaceFolders(event => {
    initializeWorkspaceIfOpen(context);
  });

  commands.registerCommand("ive.workspace.openSourceSetting", () => {
    commands.executeCommand('workbench.action.openSettings', Config.getModelLocationKey());
  });

  commands.registerCommand("ive.workspace.markAsSource", (uri: Uri) => {
    Config.setSource(IveUri.getFilenameWithoutExtension(uri)).then(() => initializeWorkspaceIfOpen(context));
  });
  commands.registerCommand("ive.workspace.markAsTarget", (uri: Uri) => {
    Config.setTarget(IveUri.getFilenameWithoutExtension(uri)).then(() => initializeWorkspaceIfOpen(context));
  });
  commands.registerCommand("ive.workspace.markAsHwls", (uri: Uri) => {
    Config.setHwls(IveUri.getFilenameWithoutExtension(uri)).then(() => initializeWorkspaceIfOpen(context));
  });
}

function openAiMontibelleWebview(context: ExtensionContext) {
  const targetUrl = 'https://ai.montibelle.se.rwth-aachen.de/';
  const panel = window.createWebviewPanel(
    'iveAiMontibelle',
    'AI MontiBelle',
    ViewColumn.One,
    {
      enableScripts: true,
      retainContextWhenHidden: true,
    }
  );

  panel.webview.html = `<!DOCTYPE html>
    <html lang="en">
    <head>
      <meta charset="UTF-8">
      <title>AI MontiBelle</title>
      <style>
        html, body {
          margin: 0;
          padding: 0;
          width: 100%;
          height: 100%;
          overflow: hidden;
        }
        iframe {
          border: 0;
          width: 100%;
          height: 100%;
        }
      </style>
    </head>
    <body>
      <iframe src="${targetUrl}"></iframe>
    </body>
    </html>`;

  context.subscriptions.push(panel);
}

function initializeWorkspaceIfOpen(context: ExtensionContext) {
  if (currentWorkspace) {
    currentWorkspace.dispose();
    currentWorkspace = undefined;
  }
  if (workspace.workspaceFolders !== undefined && workspace.workspaceFolders.length > 0) {
    if (showDependencyWarnings()) {
      currentWorkspace = new Workspace(context);
    }
  }
}

function setupLog(logPath: Uri, logName: string) {
  const clientConsole = window.createOutputChannel("Log (Ive)");

  const logFile = IveUri.appendUri(logPath, logName).fsPath;
  const logFileForAS = IveUri.appendUri(logPath, 'Autosledgi.log').fsPath;

  const customizableAppender = {
    configure: (config: any, layouts: any, findAppender: any, levels: any) => {
      return (loggingEvent: any) => {
        config.custom(loggingEvent, layouts);
      };
    }
  };

  configure({
    appenders: {
      host: { type: 'console' },
      file: { type: 'file', filename: logFile, maxLogSize: 1000000, backups: 1 },
      asLogFile: { type: 'file', filename: logFileForAS, maxLogSize: 1000000, backups: 1 },
      app: {
        type: customizableAppender,
        custom: (logEvent: any, layouts: any) => clientConsole.appendLine(layouts.basicLayout(logEvent))
      },
      info: {
        type: customizableAppender,
        custom: (loggingEvent: any, layouts: any) => {
          window.showInformationMessage(layouts.patternLayout("%m")(loggingEvent));
        }
      },
      warn: {
        type: customizableAppender,
        custom: (loggingEvent: any, layouts: any) => {
          window.showWarningMessage(layouts.patternLayout("%m")(loggingEvent));
        }
      },
      error: {
        type: customizableAppender,
        custom: (loggingEvent: any, layouts: any) => {
          window.showWarningMessage(layouts.patternLayout("%m")(loggingEvent));
        }
      },
      infoNotification: { type: 'logLevelFilter', appender: 'info', level: 'info', maxLevel: 'info' },
      warnNotification: { type: 'logLevelFilter', appender: 'warn', level: 'warn', maxLevel: 'warn' },
      errorNotification: { type: 'logLevelFilter', appender: 'error', level: 'error', maxLevel: 'error' }
    },
    categories: {
      default: { appenders: ['host', 'file', 'app'], level: 'trace' },
      user: { appenders: ['host', 'file', 'app', 'infoNotification', 'warnNotification', 'errorNotification'], level: 'trace' },
      autosledgi: { appenders: ['host', 'asLogFile', 'app'], level: 'trace' },
    }
  });

  getLogger().debug("Logger created! Will write to " + logFile);
}

export function getWorkspace(): Workspace | undefined {
  return currentWorkspace;
}

export function deactivate() {
  currentWorkspace?.dispose();
}
