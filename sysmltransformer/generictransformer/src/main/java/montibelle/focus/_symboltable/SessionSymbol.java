package montibelle.focus._symboltable;

import java.nio.file.Path;
import java.util.List;

public class SessionSymbol extends SessionSymbolTOP {

  public SessionSymbol(String name) {
    super(name);
  }
  public Path getPath() {
    if (!isEmptyPath()) {
      List<String> pathList = getPathList();
      return Path.of(pathList.get(0), pathList.subList(1, sizePath()).toArray(new String[0]));
    } else {
      throw new IllegalStateException("Path for session " + getName() + " is empty");
    }
  }
}
