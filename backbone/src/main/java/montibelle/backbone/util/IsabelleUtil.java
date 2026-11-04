package montibelle.backbone.util;

import de.se_rwth.commons.logging.Log;

import java.nio.file.Path;
import java.util.List;
import java.util.stream.Collectors;

public class IsabelleUtil {

  private String coreLocation;

  public IsabelleUtil(Path coreLocation) {
    this.coreLocation = coreLocation.toString();
  }

  public String getCommandToVerifyRefinement(
      List<Path> sessionLocations,
      Path theory,
      String session,
      int timeout,
      Boolean useCloud)
  {
    var command = "autosledgi prove"
        + (useCloud ? " --cloud" : "")
        + sessionLocations.stream().map(d -> " -d " + d.toString()).collect(Collectors.joining())
        + " -t " + timeout
        + " -s " + session
        + " --log " + "./logs/prove/"
        + " " + theory.toString();

    Log.trace("Autosledgi command: " + command, IsabelleUtil.class.getName());
    return command;
  }

  public String getCommandToCheckAREC(List<Path> sessionLocations, Path theory, String session, int timeout) {
    var additonalSessions = sessionLocations.stream().map(p -> "-d " + p.toString()).collect(Collectors.joining(" "));

    var callAutosledgi = "autosledgi prove -arec"
        + " -r "
        + " -d " + coreLocation + " " + additonalSessions
        + " -t " + timeout
        + " -s " + "HOLCF"
        + " --log_file " + "./logs/arec/"
        + " " + theory.toString().replace(".thy", "_arec.thy");

    return callAutosledgi;
  }

  public String getCommandToBuild(List<Path> sessionLocations, String session, int timeout) {
    var additonalSessions = sessionLocations.stream().map(p -> " -d " + p.toString()).collect(Collectors.joining(""));

    var callAutosledgi = "autosledgi build"
        + " -d " + coreLocation + additonalSessions
        + " " + session
        + " --log_file " + "./logs/build/";

    Log.info("Autosledgi command: " + callAutosledgi, getClass().getName());
    return callAutosledgi;
  }

}
