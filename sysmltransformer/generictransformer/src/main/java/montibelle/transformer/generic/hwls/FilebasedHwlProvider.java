package montibelle.transformer.generic.hwls;

import de.se_rwth.commons.logging.Log;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

public class FilebasedHwlProvider extends AHwlProvider {

  private final HWLSAccessor hwlsAccessor;

  public FilebasedHwlProvider(Path hwlPath) {
    try {
      if (Files.notExists(hwlPath)) {
        Log.trace("Creating hwl file " + hwlPath, getClass().getSimpleName());
        if (hwlPath.getParent() != null) {
          Files.createDirectories(hwlPath.getParent());
        }
        Files.createFile(hwlPath);
      }
    } catch (IOException e) {
      throw new RuntimeException("Could not initialize hwl file " + hwlPath, e);
    }

    this.hwlsAccessor = new HWLSAccessor(hwlPath);
  }

  @Override
  public List<HwlTheory> getHwls(String sessionName, String filename) {
    return hwlsAccessor.parse(sessionName, filename);
  }

  public void addHwl(String sessionName, String filename, HwlTheory hwl) {
    throw new UnsupportedOperationException("addHwl not yet implemented for FilebasedHwlProvider");
  }

}
