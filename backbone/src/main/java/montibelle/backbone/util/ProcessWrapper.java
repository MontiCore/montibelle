package montibelle.backbone.util;

import de.se_rwth.commons.logging.Log;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.concurrent.CompletableFuture;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class ProcessWrapper {

  protected Process process;

  protected ProcessBuilder builder;

  protected ArrayList<IProcessListener> listeners = new ArrayList<>();

  protected Path theory;

  protected String errors;

  protected final ArrayList<String> lines = new ArrayList<>();

  public ProcessWrapper(String command, Path theory) {
    this.theory = theory;
    setupBuilder(command);
  }

  protected void setupBuilder(String command) {
    if (System.getProperty("os.name").startsWith("Windows")) {
      this.builder = new ProcessBuilder("powershell", "/c", command).redirectErrorStream(true);
    }
    else {
      this.builder = new ProcessBuilder("bash", "-c", command).redirectErrorStream(true);
    }
  }

  public boolean start() throws IOException {
    if (this.process != null) {
      Log.warn("Process already started.");
      return false;
    }

    this.process = this.builder.start();
    listeners.forEach((l) -> l.onStarted());

    CompletableFuture.runAsync(() -> processLog())
        .thenRun(() -> {
          try {
            int code = process.waitFor();
            listeners.forEach((l) -> l.onStopped(code));
          }
          catch (InterruptedException e) {
            Log.warn("Process for " + theory.getFileName().toString() + " was interrupted.");
          }
        });

    return true;
  }

  public ArrayList<String> getLog() {
    synchronized (lines) {
      return lines;
    }
  }

  public String getErrors() {
    return errors;
  }

  public Path getTheory() {
    return theory;
  }

  public long pid() {
    return process.pid();
  }

  public void addListener(IProcessListener listener) {
    this.listeners.add(listener);
  }

  public void removeListener(IProcessListener listener) {
    this.listeners.remove(listener);
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

  public int waitForExit() throws InterruptedException {
    return process.waitFor();
  }

  public void destroy() throws IllegalStateException {
    if (process != null) {
      process.destroy();
      ProcessHandle.allProcesses().forEach(p -> {
        if(p.info().command().isPresent()){
            if (p.info().command().get().contains("autosledgi")) {
                p.destroy();
            }
        }
      });
    } else {
      throw new IllegalStateException("Process not started.");
    }
  }

  @Override
  public boolean equals(Object other) {
    if (!(other instanceof ProcessWrapper)) {
      return false;
    }
    return ((ProcessWrapper) other).process.pid() == this.process.pid()
        && ((ProcessWrapper) other).theory.equals(this.theory);
  }
}
