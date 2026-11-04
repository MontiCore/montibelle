package montibelle.transformer.generic.sessions;

import java.util.Arrays;
import java.util.List;

public class Theories {
  private List<Options> options = null;
  private List<TheoryEntry> theoryEntries;

  public Theories(List<Options> options, List<TheoryEntry> theoryEntries) {
    this.options = options;
    this.theoryEntries = theoryEntries;
  }

  public Theories(List <TheoryEntry> theoryEntries) {
    this.theoryEntries = theoryEntries;
  }

  public Theories(TheoryEntry... theoryEntries) {
    this.theoryEntries = Arrays.asList(theoryEntries);
  }

  public List<Options> getOptions() {
    return options;
  }

  public void setOptions(List<Options> options) {
    this.options = options;
  }

  public List<TheoryEntry> getTheoryEntries() {
    return theoryEntries;
  }

  public void setTheoryEntries(List<TheoryEntry> theoryEntries) {
    this.theoryEntries = theoryEntries;
  }
}
