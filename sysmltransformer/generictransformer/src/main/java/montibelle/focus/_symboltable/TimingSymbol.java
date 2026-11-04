package montibelle.focus._symboltable;

public class TimingSymbol extends TimingSymbolTOP {

  public TimingSymbol(String name) {
    super(name);
  }

  public boolean isEventBased() {
    return getName().equals("EVENT");
  }

  public boolean isStrictlyTimeSyncronous() {
    return getName().equals("TONE");
  }

  public boolean isTimeSyncronous() {
    return getName().equals("SYNC");
  }
}
