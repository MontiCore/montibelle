package montibelle.focus._symboltable;

import montibelle.focus.FocusMill;
import montibelle.transformer.generic.hwls.AHwlProvider;

public class TheorySymbol extends TheorySymbolTOP {

  public TheorySymbol(String name) {
    super(name);
  }

  public String importFrom(TheorySymbol other) {
    AHwlProvider hwlProvider = FocusMill.getHwlProvider();
    var substitute = hwlProvider.substituteFor(getSession().getName(), getFilename());

    if (substitute != null) {
      return substitute.importFrom(other.getSession().getName());
    }

    String importString;
    if (!other.getSessionName().equals(getSessionName())) {
      importString = getSessionName() + "." + getFilename();
    } else {
      importString = getFilename();
    }

    String epilogues = String.join(
        " ",
        hwlProvider.getEpilogueImportsFor(getSession().getName(), getFilename())
    );

    if (!epilogues.isEmpty()) {
      return epilogues + " " + importString;
    }

    return importString;
  }
}
