import * as vscode from 'vscode';
import { ProofProgress } from "@montibelle/backbone-rpc-client/out/montibelle/backbone/proof/ProofProgress";

export class ProgressBar {
  private lastProgress = 0;
  private notification: vscode.Progress<{ message?: string; increment?: number }> | undefined;
  private cancelToken: vscode.CancellationTokenSource | undefined;

  private finishProgress: (() => void) | undefined;

  public async show() {
    this.cancelToken = new vscode.CancellationTokenSource();

    await vscode.window.withProgress(
      {
        location: vscode.ProgressLocation.Notification,
        title: "Proof Finding",
        cancellable: false
      },
      (progress, token) =>
        new Promise<void>((resolve) => {
          this.finishProgress = resolve;
          this.notification = progress;

          token.onCancellationRequested(() => this.cancel());

          progress.report({
            message:
              'Loading Sessions',
            increment: 0
          });
        })
    );
  }

  public update(updated: ProofProgress) {
    const percentage = Number(updated.progress);
    this.notification?.report({
      message: `${updated.message} (${percentage}%)`,
      increment: percentage - this.lastProgress
    });
    this.lastProgress = percentage;
  }

  public async closeWithCancel() {
    if (!this.cancelToken) {
      return;
    }

    this.cancelToken.cancel();

    await new Promise((resolve) => setTimeout(resolve, 5000));

    if (this.finishProgress) {
      this.finishProgress();
    }
  }

  private cancel() {}
}
