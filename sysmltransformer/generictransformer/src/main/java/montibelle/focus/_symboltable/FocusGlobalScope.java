package montibelle.focus._symboltable;

import java.net.URL;
import java.net.URLEncoder;
import java.nio.charset.StandardCharsets;
import java.util.Optional;

public class FocusGlobalScope extends FocusGlobalScopeTOP {

  public static String encodeSymbolName(String name) {
    return URLEncoder.encode(name, StandardCharsets.UTF_8);
  }

  @Override
  public FocusGlobalScope getRealThis() {
    return this;
  }

  @Override
  public void loadFileForModelName(String modelName){
    String encodedName = encodeSymbolName(modelName);
    Optional<URL> location = getSymbolPath().find(encodedName + getFileExt());
    if (location.isPresent() && !isFileLoaded(location.get().toString())) {
      addLoadedFile(location.get().toString());
      IFocusArtifactScope as = getSymbols2Json().load(location.get());
      addSubScope(as);
    }
  }
}
