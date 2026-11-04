package montibelle.backbone;

import montibelle.backbone.autosledgi.AutosledgiWrapper;
import montibelle.backbone.autosledgi.IAutosledgiListener;
import montibelle.backbone.proof.ProofProgress;
import montibelle.backbone.proof.ProveDefinition;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.stream.Collectors;

public class Proof {
  private final AutosledgiWrapper autosledgiWrapper;

  private ProofState proofState = ProofState.UNKNOWN;
  private int progress = 0;
  private String progressMessage = "Loading Sessions...";

  public Proof(ProveDefinition proveDefinition, Path logFile) {
    this.autosledgiWrapper = new AutosledgiWrapper(
        Path.of(proveDefinition.getTheoryFile()),
        proveDefinition.getSession(),
        Arrays.stream(proveDefinition.getSessionDirectories()).map(Path::of).collect(Collectors.toList()),
        proveDefinition.getTimeout().orElse(5),
        false,
        logFile);

    autosledgiWrapper.addListener(new IAutosledgiListener() {
      @Override
      public void onStarted() {
        setProofState(ProofState.RUNNING);
      }

      @Override
      public void onStopped(int exitCode) {
        if (exitCode == 0)
          setProofState(ProofState.VERIFIED);
        else if (exitCode == 2)
          setProofState(ProofState.DISPROVEN);
        else
          setProofState(ProofState.UNKNOWN);

      }

      @Override
      public void onProgress(int progress, int currentLemma, int totalLemmas) {
        setProgress(progress);
        if (totalLemmas > 0) {
          setProgressMessage("Proving lemma " + currentLemma + " / "
              + totalLemmas);
        }
      }
    });
  }

  public int verify() throws IOException {
    this.autosledgiWrapper.start();
    return this.autosledgiWrapper.getId();
  }

  public void cancelVerify() {
    this.autosledgiWrapper.destroy();
  }

  public ProofProgress getProofProgress() {
    return new ProofProgress(progress, progressMessage);
  }

  public ProofState getProofState() {
    return this.proofState;
  }

  public void setProofState(ProofState state) {
    this.proofState = state;
  }

  public int getProgress() {
    return progress;
  }

  public void setProgress(int progress) {
    this.progress = progress;
  }

  public String getProgressMessage() {
    return progressMessage;
  }

  public void setProgressMessage(String progressMessage) {
    this.progressMessage = progressMessage;
  }
}
