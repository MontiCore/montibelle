package montibelle.backbone.autosledgi;

import montibelle.backbone.ProveCommand;
import montibelle.backbone.util.IProcessListener;
import montibelle.backbone.util.ProcessWrapper;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Path;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class AutosledgiWrapper extends ProcessWrapper {

  private int solvedProofs = 0;
  private int unsolvedProofs = 0;

  private int currentLemma = 0;
  private int totalLemmas = 0;
  private int progress = 0;

  private final int id;

  public AutosledgiWrapper(Path target, String session, List<Path> sessionDirectories) {
    this(target, session, sessionDirectories, 5, false, null);
  }

  public AutosledgiWrapper(Path target,
      String session,
      List<Path> sessionDirectories,
      int timeout,
      boolean cloud,
      Path logFile) {
    super("", Path.of(target.toString()));

    Path projectDir = null;
    if(!sessionDirectories.isEmpty()) {
      projectDir = sessionDirectories.get(0).resolve(".isabelle");
    }

    ProveCommand command = new ProveCommand(target, sessionDirectories, session, projectDir, timeout, cloud, logFile);

    this.setupBuilder(command.getCommand());
    this.addListener(new IProcessListener() {
      @Override
      public void onLog(String logLine) {
        processLog(logLine);
      }
    });
    this.id = hashCode();
  }

  protected void processLog() {
    try {
      BufferedReader reader = new BufferedReader(new InputStreamReader(process.getInputStream()));
      StringBuilder sb = new StringBuilder();
      String line;
      while ((line = reader.readLine()) != null) {
        synchronized (lines) {
          final String _line = line;
          this.listeners.forEach((l) -> l.onLog(_line));

          Pattern lemmaPattern = Pattern.compile("Proving lemma\\s+(\\d+)\\s*/\\s*(\\d+)\\s*$");
          Matcher lemmaMatcher = lemmaPattern.matcher(_line);
          boolean lemmaChanged = lemmaMatcher.find();
          if (lemmaChanged) {
            currentLemma = Integer.parseInt(lemmaMatcher.group(1));
            totalLemmas = Integer.parseInt(lemmaMatcher.group(2));
          }

          Pattern progressPattern = Pattern.compile("Progress:\\s*([0-9]+(?:\\.[0-9]+)?)%");
          Matcher matcher = progressPattern.matcher(_line);
          boolean progressChanged = matcher.find();
          if (progressChanged) {
            progress = (int) Math.round(Double.parseDouble(matcher.group(1)));
          }
          if (lemmaChanged || progressChanged) {
            this.listeners.forEach((l) -> {
              if (l instanceof IAutosledgiListener) {
                ((IAutosledgiListener) l).onProgress(progress, currentLemma, totalLemmas);
              }
            });
          }

          this.lines.add(line);

          if (line.startsWith("***")) {
            sb.append(line);
            sb.append(System.getProperty("line.separator"));
          }
        }
        errors = sb.toString();
      }
    }
    catch (IOException ex) {
      assert (false);
    }
  }

  private void fireProofChanged() {
    this.listeners.forEach((l) -> {
      if (l instanceof IAutosledgiListener) {
        ((IAutosledgiListener) l).onProofResultChanged(solvedProofs, unsolvedProofs);
      }
    });
  }

  private void processLog(String logLine) {
    if (logLine.endsWith("Detected finished proof. Cleaning up.")) {
      solvedProofs++;
      fireProofChanged();
    }
    else if (logLine.endsWith("There is no goal to solve. We are done here.")) {
      solvedProofs++;
      fireProofChanged();
    }
    else if (logLine.endsWith("Could not find proof in time or provers gave up.")) {
      unsolvedProofs++;
      fireProofChanged();
    }
    else if (logLine.endsWith("No proof found.")) {
      unsolvedProofs++;
      fireProofChanged();
    }
    else if (logLine.endsWith("Counterexample found.")) {
      unsolvedProofs++;
      fireProofChanged();
    }
  }

  public int getSolvedProofs() {
    return solvedProofs;
  }

  public int getUnsolvedProofs() {
    return unsolvedProofs;
  }

  public void addListener(IAutosledgiListener listener) {
    super.addListener(listener);
  }

  public void removeListener(IAutosledgiListener listener) {
    super.removeListener(listener);
  }

  public int getId() {
    return this.id;
  }

}
