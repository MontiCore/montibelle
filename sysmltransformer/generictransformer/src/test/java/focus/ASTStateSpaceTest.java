package focus;

import de.monticore.types.check.SymTypeOfFunction;
import de.monticore.types.check.SymTypeOfObject;
import de.monticore.types.check.SymTypePrimitive;
import de.monticore.types.mcbasictypes._ast.ASTMCPrimitiveType;
import de.monticore.types.mcbasictypes._ast.ASTMCQualifiedType;
import de.monticore.types.mcfunctiontypes._ast.ASTMCUnaryFunctionType;
import de.se_rwth.commons.logging.LogStub;
import montibelle.focus.FocusMill;
import montibelle.focus.FocusTool;
import montibelle.transformer.generic.Constants;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.assertj.core.api.Assertions.assertThat;

public class ASTStateSpaceTest {
  private final FocusTool focusTool = new FocusTool();

  @BeforeEach
  void setUp() {
    LogStub.init();
    focusTool.init();
  }

  @Test
  void parseASTStateSpaceTest() throws Exception {
    var parsed = FocusMill.parser()
        .parse_StringStateSpace("TestStates S TestTheory");
    assertThat(parsed).isPresent();
  }

  @Test
  void countableASTStateSpaceTestPrimitive() throws Exception {
    var scope = FocusMill.scope();
    scope.setEnclosingScope(FocusMill.globalScope());
    scope.add(FocusMill.enumTypeSymbolBuilder().setName("int").build());

    var parsed = FocusMill.parser().parse_StringStateSpace(
        "TestStates S (test \"test_pattern\" int) TestTheory");
    assertThat(parsed).isPresent();

    var space = parsed.get();
    var variable = space.getStateVariable(0);
    assertThat(variable.getName()).isEqualTo("test");
    assertThat(variable.getMCType()).isInstanceOf(ASTMCPrimitiveType.class);
    variable.getMCType().setEnclosingScope(FocusMill.globalScope());
    FocusTypeCheck3.init();
    var symType = FocusTypeCheck3.symTypeFromAST(variable.getMCType());
    assertThat(symType).isInstanceOf(SymTypePrimitive.class);
    variable.setEnclosingScope(scope);
    assertThat(Constants.isTypeCountable(symType)).isTrue();
  }

  @Test
  void countableASTStateSpaceTestEnum() throws Exception {
    var scope = FocusMill.scope();
    scope.setEnclosingScope(FocusMill.globalScope());
    scope.add(FocusMill.enumTypeSymbolBuilder()
        .setName("Section")
        .setFiniteChoicesList(List.of("sect1", "sect2", "sect3"))
        .build());

    var parsed = FocusMill.parser().parse_StringStateSpace(
        "TestStates S (section \"section_pattern\" Section) TestTheory");
    assertThat(parsed).isPresent();
    var space = parsed.get();
    assertThat(space.getStateVariableList()).hasSize(1);

    var variable = space.getStateVariable(0);
    assertThat(variable.getName()).isEqualTo("section");
    assertThat(variable.getMCType()).isInstanceOf(ASTMCQualifiedType.class);

    var mcType = (ASTMCQualifiedType) variable.getMCType();
    assertThat(mcType.printType()).isEqualTo("Section");
    mcType.setEnclosingScope(scope);
    mcType.getMCQualifiedName().setEnclosingScope(scope);

    FocusTypeCheck3.init();
    var symType = FocusTypeCheck3.symTypeFromAST(mcType);
    assertThat(symType).isInstanceOf(SymTypeOfObject.class);
    variable.setEnclosingScope(scope);
    System.out.println(Constants.getFiniteChoices(symType));
    assertThat(Constants.isTypeCountable(symType)).isTrue();
  }

  @Test
  void countableASTStateSpaceTestFunction() throws Exception {
    var parsed = FocusMill.parser().parse_StringStateSpace(
        "TestStates S (function \"function_pattern\" int -> int) TestTheory");
    assertThat(parsed).isPresent();

    var space = parsed.get();
    assertThat(space.getStateVariableList()).hasSize(1);

    var variable = space.getStateVariable(0);
    assertThat(variable.getName()).isEqualTo("function");
    assertThat(variable.getMCType()).isInstanceOf(ASTMCUnaryFunctionType.class);

    var functionType = (ASTMCUnaryFunctionType) variable.getMCType();
    var globalScope = FocusMill.globalScope();
    functionType.setEnclosingScope(globalScope);
    functionType.getMCType().setEnclosingScope(globalScope);
    functionType.getMCReturnType().setEnclosingScope(globalScope);
    functionType.getMCReturnType().getMCType().setEnclosingScope(globalScope);

    FocusTypeCheck3.init();
    var symType = FocusTypeCheck3.symTypeFromAST(functionType);
    assertThat(symType).isInstanceOf(SymTypeOfFunction.class);
    assertThat(functionType.printType()).isEqualTo("int->int");

    assertThat(Constants.isTypeCountable(symType)).isFalse();
  }
}
