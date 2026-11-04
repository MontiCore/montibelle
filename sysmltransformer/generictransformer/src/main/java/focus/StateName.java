package focus;

public class StateName {

  private String name;

  public StateName(String name) {
    this.name = "state__" + name;
  }

  @Override
  public boolean equals(Object other) {
    return other instanceof StateName
        && this.name.equals(((StateName) other).name);
  }

  @Override
  public String toString() {
    return this.name;
  }

  @Override
  public int hashCode() {
    return this.name.hashCode();
  }

}
