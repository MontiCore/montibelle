package montibelle.backbone.services;

import com.googlecode.jsonrpc4j.spring.AutoJsonRpcServiceImpl;
import montibelle.backbone.hwl.Hwl;
import montibelle.backbone.hwl.OperationInput;
import montibelle.backbone.hwl.RetrievalInput;
import montibelle.transformer.generic.hwls.FilebasedHwlProvider;
import montibelle.transformer.generic.hwls.HwlType;
import montibelle.transformer.generic.hwls.InMemoryHwlProvider;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Service;
import montibelle.transformer.generic.hwls.AHwlProvider;
import montibelle.transformer.generic.hwls.HwlTheory;

import java.net.URI;
import java.net.URISyntaxException;
import java.nio.file.Paths;
import java.util.Optional;

@AutoJsonRpcServiceImpl
@Service
public class HwlService implements Hwl {

  @Autowired
  WorkspaceService workspaceManager;

  private AHwlProvider getProviderInstance(Optional<String> hwlUri) throws URISyntaxException {
    if (hwlUri.isPresent()) {
      return new FilebasedHwlProvider(Paths.get(new URI(hwlUri.get())));
    }
    return new InMemoryHwlProvider();
  }

  @Override
  public void add(OperationInput input) throws Exception {
    Optional<String> hwlUri = workspaceManager.retrieve(input.getWorkspaceId()).getHwlUri();

    HwlTheory hwl = new HwlTheory(input.getHwlName(), input.getHwlSession(), input.getHwlType() ? HwlType.PROLOGUE : HwlType.EPILOGUE);

    getProviderInstance(hwlUri).addHwl(input.getTargetTheorySession(), input.getTargetTheoryName(), hwl);
  }

  @Override
  public void remove(OperationInput input) throws Exception {
    Optional<String> hwlUri = workspaceManager.retrieve(input.getWorkspaceId()).getHwlUri();

    HwlTheory hwl = new HwlTheory(input.getHwlName(), input.getHwlSession(), input.getHwlType() ? HwlType.PROLOGUE : HwlType.EPILOGUE);

    getProviderInstance(hwlUri).removeHwl(input.getTargetTheorySession(), input.getTargetTheoryName(), hwl);
  }

  @Override
  public String[] getHwlsForTheory(RetrievalInput input) throws Exception {
    Optional<String> hwlUri = workspaceManager.retrieve(input.getWorkspaceId()).getHwlUri();

    String[] result = getProviderInstance(hwlUri)
        .getHwls(input.getTheorySession(), input.getTheoryName())
        .stream()
        .map(t -> t.getSession().getName() + "." + t.getFilename())
        .toArray(String[]::new);

    return result;
  }

}
