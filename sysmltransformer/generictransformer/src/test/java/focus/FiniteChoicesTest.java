package focus;

import de.monticore.types.check.SymTypeExpression;
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

public class FiniteChoicesTest {

  @BeforeEach
  void setUp() {
    LogStub.init();
    new FocusTool().init();
  }

  @Test
  void testNullReturnsNoChoices() {
    assertThat(Constants.getFiniteChoices(null)).isEmpty();
  }

  @Test
  void testBooleanChoices() {
    var boolType = SymTypeExpressionFactory.createPrimitive("boolean");
    assertThat(Constants.getFiniteChoices(boolType)).containsExactly("True", "False");
  }

  @Test
  void testInfinitePrimitiveReturnsNoChoices() {
    var natType = SymTypeExpressionFactory.createPrimitive("nat");
    assertThat(Constants.getFiniteChoices(natType)).isEmpty();
  }

  @Test
  void testBooleanTupleChoices() {
    var boolType = SymTypeExpressionFactory.createPrimitive("boolean");
    var tuple = SymTypeExpressionFactory.createTuple(boolType, boolType);

    assertThat(Constants.getFiniteChoices(tuple)).containsExactlyInAnyOrder(
        "(True, True)", "(True, False)", "(False, True)", "(False, False)");
  }

  @Test
  void testTupleWithInfiniteElementReturnsNoChoices() {
    var boolType = SymTypeExpressionFactory.createPrimitive("boolean");
    var natType = SymTypeExpressionFactory.createPrimitive("nat");
    var tuple = SymTypeExpressionFactory.createTuple(boolType, natType);

    assertThat(Constants.getFiniteChoices(tuple)).isEmpty();
  }

  @Test
  void testEnumChoices() {
    var scope = FocusMill.scope();
    scope.setEnclosingScope(FocusMill.globalScope());
    var focusType = FocusMill.enumTypeSymbolBuilder()
        .setName("Section")
        .setFiniteChoicesList(List.of("sect1", "sect2", "sect3"))
        .build();
    scope.add(focusType);

    var enumType = SymTypeExpressionFactory.createTypeObject(new EnumType2TypeSymbolAdapter(focusType));
    assertThat(Constants.getFiniteChoices(enumType)).containsExactly("sect1", "sect2", "sect3");
  }
}
