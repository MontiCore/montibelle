package montibelle.transformer.generic.hwls;

import java.util.Objects;
public class HwlTheory {
  private final String filename;
  private final String sessionName;
  private final HwlType type;

  public HwlTheory(String filename, String sessionName, HwlType type) {
    this.filename = filename;
    this.sessionName = sessionName;
    this.type = type;
  }

  public String getFilename() {
    return filename;
  }

  public String getSessionName() {
    return sessionName;
  }

  public HwlType getType() {
    return type;
  }

  public String importFrom(String otherSessionName) {
    if (otherSessionName.equals(this.sessionName)) {
      return filename;
    } else {
      return this.sessionName + "." + this.filename;
    }
  }

  @Override
  public boolean equals(Object other) {
    if (other instanceof HwlTheory) {
      return this.toString().equals(other.toString());
    }
    return false;
  }

  @Override
  public int hashCode() {
    return toString().hashCode();
  }

  @Override
  public String toString() {
    return sessionName + "." + filename;
  }
}
