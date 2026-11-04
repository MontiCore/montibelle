package montibelle.transformer.generic.sessions;

public class Options {
  private String name;
  private String value = null;
  public Options(String name, String value) {
    this.name = name;
    this.value = value;
  }

  public Options (String name) {
    this.name = name;
  }

  public String getName() {
    return name;
  }

  public void setName(String name) {
    this.name = name;
  }

  public String getValue() {
    return value;
  }

  public void setValue(String value) {
    this.value = value;
  }
}
