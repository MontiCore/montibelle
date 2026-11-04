import de.monticore.lang.sysmlv2.SysMLv2Mill;
import de.monticore.lang.sysmlv2.SysMLv2Tool;
import de.monticore.symbols.oosymbols._symboltable.OOTypeSymbol;
import de.se_rwth.commons.logging.LogStub;
import montibelle.focus.FocusMill;
import montibelle.focus.FocusTool;
import montibelle.focus._ast.ASTUserDefinedStruct;
import montibelle.transformer.sysml.printer.TypePrinter;
import org.junit.jupiter.api.Test;
import java.io.IOException;
import static cc2focus.OOTypeSymbol2FocusType.buildStruct;
import static org.assertj.core.api.Assertions.assertThat;

public class EnumTypeSymbolTests {

  @Test
  public void testBooleanListAttribute() throws IOException {
    var model = "attribute def A {\n" +
        "  attribute a: boolean[*];\n" +
        "}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    var scope = tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    OOTypeSymbol type = (OOTypeSymbol) scope.resolveTypeDown("A").get();

    var focusType = (ASTUserDefinedStruct) buildStruct(type, new TypePrinter());
    assertThat(focusType.getFieldList()).hasSize(1);

    var focusTool = new FocusTool();
    focusTool.init();
    focusTool.createSymbolTable(focusType);
    focusTool.completeSymbolTable(focusType);

    var structSym = FocusMill.globalScope().resolveUserDefinedStruct("A").get();
    assertThat(structSym.getFields().get(0)).isNotNull();
    assertThat(new TypePrinter().print(structSym.getFields().get(0).getSymType()))
        .isEqualTo("bool list");
  }

  @Test
  public void testUserDefinedStructListHasEnumTypeSymbol() throws IOException {
    var model = "attribute def A {\n" +
        "}\n" +
        "\n" +
        "attribute def B {\n" +
        "  attribute b: A[*];\n" +
        "}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    var scope = tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    OOTypeSymbol typeA = (OOTypeSymbol) scope.resolveTypeDown("A").get();
    OOTypeSymbol typeB = (OOTypeSymbol) scope.resolveTypeDown("B").get();

    var focusTool = new FocusTool();
    focusTool.init();

    var focusA = (ASTUserDefinedStruct) buildStruct(typeA, new TypePrinter());
    var focusB = (ASTUserDefinedStruct) buildStruct(typeB, new TypePrinter());

    focusTool.createSymbolTable(focusA);
    focusTool.completeSymbolTable(focusA);
    focusTool.createSymbolTable(focusB);
    focusTool.completeSymbolTable(focusB);

    var structSym = FocusMill.globalScope().resolveUserDefinedStruct("B").get();

    assertThat(structSym.getFields()).hasSize(1);
    assertThat(structSym.getFields().get(0)).isNotNull();
    assertThat(new TypePrinter().print(structSym.getFields().get(0).getSymType()))
        .isEqualTo("A list");
  }
}

