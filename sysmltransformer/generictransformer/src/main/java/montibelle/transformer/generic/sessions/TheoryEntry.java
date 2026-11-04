package montibelle.transformer.generic.sessions;

import java.util.Objects;
public class TheoryEntry {

  private String name;
  private boolean isGlobal = false;

  public TheoryEntry(String name, boolean global) {
    this.name = name;
    this.isGlobal = global;
  }

  public TheoryEntry(String name) {
    this.name = name;
  }

  public String getName() {
    return name;
  }

  public void setName(String name) {
    this.name = name;
  }

  public boolean isGlobal() {
    return isGlobal;
  }

  public void setGlobal(boolean global) {
    isGlobal = global;
  }

  @Override
  public boolean equals (Object other) {
    if (this == other) return true;
    if (!(other instanceof TheoryEntry)) return false;
    TheoryEntry that = (TheoryEntry) other;
    return isGlobal == that.isGlobal && Objects.equals(name, that.name);
  }

  @Override
  public int hashCode() {
    return Objects.hash(name, isGlobal);
  }
}
