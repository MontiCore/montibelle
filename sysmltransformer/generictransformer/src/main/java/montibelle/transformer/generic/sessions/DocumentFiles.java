package montibelle.transformer.generic.sessions;

import java.util.Arrays;
import java.util.List;

public class DocumentFiles {

  private String base_dir = null;
  private List <String> files;

  public DocumentFiles(String dir, List <String> files) {
    this.base_dir = dir;
    this.files = files;
  }

  public DocumentFiles(List <String> files) {
    this.files = files;
  }

  public DocumentFiles(String... files) {
    this.files = Arrays.asList(files);
  }

  public String getBase_dir() {
    return base_dir;
  }

  public void setBase_dir(String base_dir) {
    this.base_dir = base_dir;
  }

  public List<String> getFiles() {
    return files;
  }

  public void setFiles(List<String> files) {
    this.files = files;
  }
}
