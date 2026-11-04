package montibelle.backbone.services;

import com.googlecode.jsonrpc4j.spring.AutoJsonRpcServiceImpl;
import de.se_rwth.commons.logging.Log;
import montibelle.backbone.ProofState;
import montibelle.backbone.proof.Proof;
import montibelle.backbone.proof.ProveDefinition;
import montibelle.backbone.proof.ProofProgress;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Component;
import org.springframework.stereotype.Service;

import java.io.IOException;
import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Date;
import java.util.HashMap;
import java.util.Map;

@AutoJsonRpcServiceImpl
@Service
@Component
public class ProofService implements Proof {

  @Autowired
  private WorkspaceService workspaceManager;

  private Map<String, montibelle.backbone.Proof> services = new HashMap<>();

  private static final String log = ProofService.class.getName();

  @Override
  public String verify(ProveDefinition input) throws Exception {
    Log.trace("Received verify request", log);

    var workdirDefinition = workspaceManager.retrieve(input.getWorkspaceId());
    Path target;
    try {
      target = Paths.get(new URI(workdirDefinition.getTargetUri()));
    }
    catch (URISyntaxException e) {
      Log.error("The workspace target URI is malformed.", e);
      throw e;
    }

    var existingService = services.getOrDefault(input.getTheoryFile(), null);
    if (existingService != null) {
      Log.info("Canceling existing service for " + input.getTheoryFile(), log);
      existingService.cancelVerify();
      services.remove(existingService);
    }

    Path logFile = target.resolve("logs").resolve("autosledgi_" + new Date().getTime() + ".log");
    Log.trace("Setting log file to " + logFile, log);

    Log.info("Starting verification of " + input.getTheoryFile(), log);

    var service = new montibelle.backbone.Proof(input, logFile);
    services.put(input.getTheoryFile(), service);
    service.verify();

    return logFile.toAbsolutePath().toString();
  }

    @Override
    public void cancelVerify(String theoryFile){
      Log.trace("Received cancel request", log);
      var service = services.getOrDefault(theoryFile, null);
      if (service != null) {
        service.cancelVerify();
        services.remove(service);
        Log.info("Canceling verification of " + theoryFile, log);
      }
    }

  @Override
  public ProofProgress getProofProgress(String theoryFile) {
    var service = services.get(theoryFile);
    if (service == null) {
      return new ProofProgress(0, "");
    }

    return service.getProofProgress();
  }

  @Override
  public String getProofState(String theoryFile) {

    var service = services.get(theoryFile);
    if (service != null && service.getProofState() != ProofState.UNKNOWN) {
      return service.getProofState().toString();
    }

    try {
      var theoryContent = Files.readString(Path.of(theoryFile));
      if (theoryContent.contains("(* Disproven!")) {
        return ProofState.DISPROVEN.toString();
      } else if (!theoryContent.contains("(* autosledgi *) sorry")
          && theoryContent.contains("(* We are done here *)")) {
        return ProofState.VERIFIED.toString();
      }
    } catch (IOException e) {
      Log.warn("Could not read theory file "
          + theoryFile + ": " + e.getMessage()
      );
    }

    for (var otherService : services.values()) {
      if (otherService.getProofState() == ProofState.RUNNING)
        return ProofState.BLOCKED.toString();
    }

    return ProofState.UNKNOWN.toString();
  }

}
