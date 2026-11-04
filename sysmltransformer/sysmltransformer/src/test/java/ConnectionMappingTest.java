import de.monticore.lang.sysmlv2.SysMLv2Mill;
import de.monticore.lang.sysmlv2.SysMLv2Tool;
import de.monticore.lang.sysmlparts._symboltable.AttributeUsageSymbol;
import de.monticore.lang.sysmlv2._symboltable.SysMLv2ArtifactScope;
import de.monticore.lang.sysmlv2._symboltable.SysMLv2Scope;
import de.se_rwth.commons.logging.LogStub;
import org.junit.jupiter.api.Test;

import java.nio.file.Paths;
import java.util.Optional;

import static org.assertj.core.api.Assertions.assertThat;
import trafos.ConnectionMapping;

public class ConnectionMappingTest {

  private static final String BASE = "src/test/resources/streamConstraints";
  private static final String MODELS = BASE + "/models";

  @Test
  public void testInverterConnectionMapping() {
    LogStub.init();

    SysMLv2Tool tool = new SysMLv2Tool();
    tool.init();

    var booleansAst = tool.parse(Paths.get(MODELS + "/Booleans.sysml").toString());
    assertThat(booleansAst).isNotNull();
    tool.createSymbolTable(booleansAst);
    tool.completeSymbolTable(booleansAst);
    tool.finalizeSymbolTable(booleansAst);

    var inverterAst = tool.parse(Paths.get(MODELS + "/Inverter.sysml").toString());
    assertThat(inverterAst).isNotNull();

    var inverterScope = tool.createSymbolTable(inverterAst);
    assertThat(inverterScope).isNotNull();
    tool.completeSymbolTable(inverterAst);
    tool.finalizeSymbolTable(inverterAst);

    var traverser = SysMLv2Mill.traverser();
    traverser.add4SysMLParts(ConnectionMapping.getInstance());
    inverterAst.accept(traverser);


    Optional<AttributeUsageSymbol> iHistory = ((SysMLv2Scope) ((SysMLv2ArtifactScope) inverterScope)
        .getSubScopes().get(0)).getSubScopes().get(2).resolveAttributeUsage("i_history");
    Optional<AttributeUsageSymbol> oHistory = ((SysMLv2Scope) ((SysMLv2ArtifactScope) inverterScope)
        .getSubScopes().get(0)).getSubScopes().get(2).resolveAttributeUsage("o_history");

    assertThat(iHistory).withFailMessage("i_history attribute existiert nicht").isPresent();
    assertThat(oHistory).withFailMessage("o_history attribute existiert nicht").isPresent();

    ConnectionMapping mapping = ConnectionMapping.getInstance();

    String iPattern = mapping.getPattern(iHistory.get());
    String oPattern = mapping.getPattern(oHistory.get());

    assertThat(iPattern).isEqualTo("channel_i_val_pattern");
    assertThat(oPattern).isEqualTo("channel_o_val_pattern");
  }
}

