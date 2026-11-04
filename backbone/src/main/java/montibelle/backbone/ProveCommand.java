package montibelle.backbone;

import java.nio.file.Path;
import java.util.List;
import java.util.Optional;

public class ProveCommand {

  private Optional<Path> location;

  private Optional<List<Path>> sessionDirs;

  private Optional<String> baseLogic;

  private Optional<Path> project;

  private Optional<Integer> proverTimeout;

  private Optional<Boolean> useCloud;

  private Optional<Path> logFile;

  public ProveCommand(
      Path location,
      List<Path> sessionDirs,
      String baseLogic,
      Path project,
      Integer timeout,
      Boolean cloud,
      Path logFile
  ) {
    this.location = Optional.ofNullable(location);
    this.sessionDirs = Optional.ofNullable(sessionDirs);
    this.baseLogic = Optional.ofNullable(baseLogic);
    this.project = Optional.ofNullable(project);
    this.proverTimeout = Optional.ofNullable(timeout);
    this.useCloud = Optional.ofNullable(cloud);
    this.logFile = Optional.ofNullable(logFile);
  }

  public ProveCommand() {
    this.location = Optional.empty();
    this.sessionDirs = Optional.empty();
    this.baseLogic = Optional.empty();
    this.project = Optional.empty();
    this.proverTimeout = Optional.empty();
    this.useCloud = Optional.empty();
    this.logFile = Optional.empty();
  }

  public String getCommand() {
    var cmd = "autosledgi prove";
    if(useCloud.isPresent() && useCloud.get()) {
      cmd +=  " --cloud";
    }
    if(sessionDirs.isPresent()) {
      for(var sessionDir: sessionDirs.get()) {
        cmd += " -d " + sessionDir.toString();
      }
    }
    if(proverTimeout.isPresent()) {
      cmd += " --prover-timeout " + proverTimeout.get();
    }
    if(project.isPresent()) {
      cmd += " --project " + project.get().toString();
    }
    if(baseLogic.isPresent()) {
      cmd += " --session " + baseLogic.get();
    }
    if(logFile.isPresent()) {
      cmd += " --log " + logFile.get().toString();
    }
    if(location.isPresent()) {
      cmd += " " + location.get().toString();
    }
    return cmd;
  }

}
