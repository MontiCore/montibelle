import de.monticore.symbols.basicsymbols._symboltable.TypeSymbolBuilder;
import montibelle.focus.FocusMill;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

public class ScopeTests {

  @Test
  public void removeSymbolFromScopeTest() {
    FocusMill.init();
    var gs = FocusMill.globalScope();
    var ars = FocusMill.artifactScope();
    ars.setName("ts");
    var s = new TypeSymbolBuilder()
        .setName("ts")
        .build();
    ars.add(s);
    gs.addSubScope(ars);

    assertThat(gs.resolveType("ts")).isPresent();

    s.getEnclosingScope().remove(s);

    assertThat(gs.resolveType("ts")).isNotPresent();
  }

}
