package montibelle.transformer.generic.sessions;

import java.util.List;

public class ExportFiles {
  private List <String> patterns;

  private String target_dir = null;

  private Integer prune = null;

  public ExportFiles(List<String> patterns) {
    this.patterns = patterns;
  }

  public ExportFiles(String dir, List<String> patterns) {
    this.patterns = patterns;
    this.target_dir = dir;
  }

  public ExportFiles(String dir, int number, List<String> patterns) {
    this.patterns = patterns;
    this.target_dir = dir;
    this.prune = number;
  }

  public List<String> getPatterns() {
    return patterns;
  }

  public void setPatterns(List<String> patterns) {
    this.patterns = patterns;
  }

  public String getTarget_dir() {
    return target_dir;
  }

  public void setTarget_dir(String target_dir) {
    this.target_dir = target_dir;
  }

  public Integer getPrune() {
    return prune;
  }

  public void setPrune(Integer prune) {
    this.prune = prune;
  }
}

