package montibelle.backbone.services;

import com.googlecode.jsonrpc4j.spring.AutoJsonRpcServiceImpl;
import montibelle.backbone.util.RegisteredWorkspace;
import montibelle.backbone.util.YamlUtil;
import montibelle.backbone.workspace.Parameters;
import montibelle.backbone.workspace.Workspace;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.stereotype.Component;
import org.springframework.stereotype.Service;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.List;
import java.util.UUID;


@AutoJsonRpcServiceImpl
@Service
@Component
public class WorkspaceService implements Workspace {

  @Value("${backbone.workspaces.path}")
  private String workspacesPath;

  private YamlUtil<RegisteredWorkspace> workspaceYamlWrapper = new YamlUtil<>(RegisteredWorkspace.class);

  @Override
  public String register(Parameters parameters) throws IOException, URISyntaxException {
    RegisteredWorkspace workspace = new RegisteredWorkspace(parameters, UUID.randomUUID().toString());

    workspaceYamlWrapper.saveObjectInYaml(workspacesPath, workspace);

    if (parameters.getHwlUri().isPresent()) {
      File hwlsFile = new File(new URL(parameters.getHwlUri().get()).toURI());
      if (!hwlsFile.exists()) {
        hwlsFile.getParentFile().mkdirs();
        hwlsFile.createNewFile();
      }
    }

    return workspace.id;
  }

  @Override
  public Parameters retrieve(String id) throws Exception {
    List<RegisteredWorkspace> workspaces = workspaceYamlWrapper.readFromYaml(workspacesPath);
    return workspaces.stream().filter(w -> w.id.equals(id)).map(w -> w.parameters).findFirst()
        .orElseThrow(() -> new Exception("No workspace registered for id " + id));
  }

  @Override
  public void remove(String workspaceId) throws Exception {
    RegisteredWorkspace workspace = new RegisteredWorkspace(retrieve(workspaceId), workspaceId);
    workspaceYamlWrapper.removeFromYaml(workspacesPath, workspace);
  }

}
