import de.monticore.types.check.SymTypeExpressionFactory;
import de.monticore.types.check.SymTypeOfObject;
import de.se_rwth.commons.logging.LogStub;
import focus.SymType2MCTypePrinter;
import montibelle.focus.FocusMill;
import montibelle.focus.FocusTool;
import montibelle.focus.symboltable.EnumType2TypeSymbolAdapter;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import java.io.IOException;
import java.util.List;

import static org.assertj.core.api.Assertions.assertThat;

class SymType2MCTypePrinterTest {

  private final SymType2MCTypePrinter printer = new SymType2MCTypePrinter();
  private final FocusTool focusTool = new FocusTool();
  private final SymTypeOfObject scalarNatural = SymTypeExpressionFactory.createTypeObject(FocusMill.typeSymbolBuilder()
      .setName("Natural").setFullName("ScalarValues.Natural").build());
  private final SymTypeOfObject scalarBoolean = SymTypeExpressionFactory.createTypeObject(FocusMill.typeSymbolBuilder()
      .setName("Boolean").setFullName("ScalarValues.Boolean").build());

  @BeforeEach
  void setUp() {
    LogStub.init();
    focusTool.init();
  }

  @ParameterizedTest
  @ValueSource(strings = {"boolean", "nat"})
  void printPrimitiveType(String name){
    var symType = SymTypeExpressionFactory.createPrimitive(name);
    String printedType = printer.print(symType);
    assertThat(printedType).isEqualTo(name);
  }

  @Test
  void printListType() {
    var intType = SymTypeExpressionFactory.createPrimitive("int");
    var symType = SymTypeExpressionFactory.createTypeArray(intType,1);
    String printedType = printer.print(symType);
    assertThat(printedType).isEqualTo("List<int>");
  }

  @Test
  void printListType2() throws IOException {
    var enumType = FocusMill.enumTypeSymbolBuilder()
        .setName("Section")
        .setFiniteChoicesList(List.of("sect1", "sect2", "sect3"))
        .build();
    var adapt = new EnumType2TypeSymbolAdapter(enumType);
    var elementType = SymTypeExpressionFactory.createTypeObject(adapt);
    var symType = SymTypeExpressionFactory.createTypeArray(elementType,1);
    String printedType = printer.print(symType);
    assertThat(printedType).isEqualTo("List<Section>");
  }

  @Test
  void printScalarValuesTuple() {
    var mappedPrinter = new SymType2MCTypePrinter();
    var tuple = SymTypeExpressionFactory.createTuple(scalarNatural, scalarBoolean);

    assertThat(mappedPrinter.print(tuple)).isEqualTo("(nat, boolean)");
  }

  @Test
  void printScalarValuesInNestedGenerics() {
    var mappedPrinter = new SymType2MCTypePrinter();
    var listSymbol = FocusMill.typeSymbolBuilder().setName("List").setFullName("List").build();
    var list = SymTypeExpressionFactory.createGenerics(listSymbol, scalarBoolean);
    var nestedList = SymTypeExpressionFactory.createGenerics(listSymbol, list);

    assertThat(mappedPrinter.print(list)).isEqualTo("List<boolean>");
    assertThat(mappedPrinter.print(nestedList)).isEqualTo("List<List<boolean>>");
  }

  @Test
  void printScalarValuesInFunctions() throws IOException {
    var mappedPrinter = new SymType2MCTypePrinter();
    var function = SymTypeExpressionFactory.createFunction(scalarNatural, List.of(scalarBoolean, scalarNatural));
    var higherOrder = SymTypeExpressionFactory.createFunction(scalarBoolean, List.of(function));

    assertThat(mappedPrinter.print(function)).isEqualTo("(boolean, nat) -> nat");
    String printed = mappedPrinter.print(higherOrder);
    assertThat(printed).isEqualTo("(((boolean, nat) -> nat)) -> boolean");
    assertThat(FocusMill.parser().parse_StringMCType(printed)).isPresent();
    assertThat(mappedPrinter.print(SymTypeExpressionFactory.createFunction(
        SymTypeExpressionFactory.createTypeVoid(), List.of())))
        .isEqualTo("() -> void");
  }
}
