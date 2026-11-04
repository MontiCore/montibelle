package focus;

import de.monticore.types.check.SymTypeExpressionFactory;
import de.se_rwth.commons.logging.LogStub;
import montibelle.focus.FocusMill;
import montibelle.focus.FocusTool;
import montibelle.focus.symboltable.EnumType2TypeSymbolAdapter;
import montibelle.transformer.generic.Constants;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.assertj.core.api.Assertions.assertThat;

public class FiniteTest {

  private final FocusTool tool = new FocusTool();
  @BeforeEach
  void setUp() {
    LogStub.init();
    tool.init();
  }

  @Test
  public void testPrimitives() {
    var boolType = SymTypeExpressionFactory.createPrimitive("boolean");
    assertThat(Constants.isTypeFinite(boolType)).isTrue();
    var natType = SymTypeExpressionFactory.createPrimitive("nat");
    assertThat(Constants.isTypeFinite(natType)).isFalse();
  }

  @Test
  public void testTuple() {
    var boolType = SymTypeExpressionFactory.createPrimitive("boolean");
    var tuple = SymTypeExpressionFactory.createTuple(boolType, boolType);
    assertThat(Constants.isTypeFinite(tuple)).isTrue();

    var natType = SymTypeExpressionFactory.createPrimitive("nat");
    var arr = SymTypeExpressionFactory.createTuple(natType, boolType);
    assertThat(Constants.isTypeFinite(arr)).isFalse();
  }

  @Test
  public void testStructFinite() throws Exception {
    var finiteAst = FocusMill.parser()
        .parse_String("struct FiniteStruct { boolean first ( firstPattern ); boolean second ( secondPattern ); }")
        .orElseThrow();
    var finiteScope = tool.createSymbolTable(finiteAst);
    tool.completeSymbolTable(finiteAst);
    var finiteSymbol = finiteScope.resolveType("FiniteStruct").orElseThrow();
    assertThat(Constants.isTypeFinite(SymTypeExpressionFactory.createTypeObject(finiteSymbol))).isTrue();
  }

  @Test
  public void testStructInfinite() throws Exception {
    var infiniteAst = FocusMill.parser()
        .parse_String("struct InfiniteStruct { boolean first ( firstPattern ); nat second ( secondPattern ); }")
        .orElseThrow();
    var infiniteScope = tool.createSymbolTable(infiniteAst);
    tool.completeSymbolTable(infiniteAst);
    var infiniteSymbol = infiniteScope.resolveType("InfiniteStruct").orElseThrow();
    assertThat(Constants.isTypeFinite(SymTypeExpressionFactory.createTypeObject(infiniteSymbol))).isFalse();
  }

  @Test
  public void testEnum() {
    var scope = FocusMill.scope();
    scope.setEnclosingScope(FocusMill.globalScope());
    var enumType = FocusMill.enumTypeSymbolBuilder()
        .setName("Section")
        .setFiniteChoicesList(List.of("sect1", "sect2", "sect3"))
        .build();
    scope.add(enumType);

    var enumSymbol = new EnumType2TypeSymbolAdapter(enumType);
    assertThat(Constants.isTypeFinite(SymTypeExpressionFactory.createTypeObject(enumSymbol))).isTrue();
  }
}
