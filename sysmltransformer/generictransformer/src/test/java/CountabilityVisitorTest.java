import de.monticore.lang.sysmlv2.SysMLv2Mill;
import de.monticore.lang.sysmlv2.SysMLv2Tool;
import de.monticore.lang.sysmlv2.types3.SysMLTypeCheck3;
import de.monticore.symbols.basicsymbols.BasicSymbolsMill;
import de.monticore.symbols.basicsymbols._symboltable.TypeSymbol;
import de.monticore.symbols.oosymbols._symboltable.OOTypeSymbol;
import de.monticore.types.check.SymTypeExpression;
import de.monticore.types.check.SymTypeExpressionFactory;
import de.monticore.types.check.SymTypeOfFunction;
import de.monticore.types.check.SymTypeOfGenerics;
import de.monticore.types.check.SymTypePrimitive;
import de.monticore.types3.TypeCheck3;
import de.se_rwth.commons.logging.LogStub;
import focus.FocusTypeCheck3;
import montibelle.focus.FocusMill;
import montibelle.focus.FocusTool;
import montibelle.focus._ast.ASTUserDefinedStruct;
import montibelle.transformer.generic.Constants;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class CountabilityVisitorTest {
  @BeforeEach
  void setUp() {
    FocusMill.init();
    FocusTypeCheck3.init();
  }

  @Test
  void primitivesTest() {
    LogStub.init();
    var tool = new FocusTool();
    tool.init();

    SymTypeExpression primitive = SymTypeExpressionFactory.createPrimitive(
        "int");
    assertTrue(Constants.isTypeCountable(primitive));
  }

  @Test
  void tupleTestWithCountableTypes() {
    LogStub.init();
    var tool = new FocusTool();
    tool.init();

    SymTypeExpression primitive = SymTypeExpressionFactory.createPrimitive(
        "boolean");
    SymTypeExpression primitive2 = SymTypeExpressionFactory.createPrimitive(
        "nat");
    SymTypeExpression tuple = SymTypeExpressionFactory.createTuple(primitive,
        primitive2);
    assertTrue(Constants.isTypeCountable(tuple));
  }

  @Test
  @Disabled
  void tupleTestWithoutCountableTypes() {
    LogStub.init();
    var tool = new FocusTool();
    tool.init();

    SymTypeExpression primitive = SymTypeExpressionFactory.createPrimitive(
        "boolean");
    SymTypeExpression primitive2 = SymTypeExpressionFactory.createPrimitive(
        "nat");
    SymTypeExpression primitive3 = SymTypeExpressionFactory.createPrimitive(
        "short");
    SymTypeExpression tuple2 = SymTypeExpressionFactory.createTuple(primitive,
        primitive2, primitive3);
    assertFalse(Constants.isTypeCountable(tuple2));
  }

  @Test
  @Disabled
  void genericTestWithCountableTypes() {
    LogStub.init();
    var tool = new FocusTool();
    tool.init();

    SymTypePrimitive intType = SymTypeExpressionFactory.createPrimitive("int");
    SymTypeOfGenerics listOfInt = SymTypeExpressionFactory.createGenerics(
        BasicSymbolsMill.globalScope().resolveTypeLocally("List").get(),
        intType);

    assertTrue(Constants.isTypeCountable(listOfInt));
  }

  @Test
  @Disabled
  void genericTestWithoutCountableTypes() {
    LogStub.init();
    var tool = new FocusTool();
    tool.init();

    SymTypePrimitive intType = SymTypeExpressionFactory.createPrimitive("int");
    SymTypeOfGenerics mapOfInt = SymTypeExpressionFactory.createGenerics(
        BasicSymbolsMill.globalScope().resolveTypeLocally("Map").get(),
        intType);
    assertFalse(Constants.isTypeCountable(mapOfInt));
  }

  @Test
  @Disabled
  public void testStructWithOnlyCountableFields() throws Exception {
    var model =
        "enum def Section {\n" +
            "  enum s1;\n" +
            "  enum s2;\n" +
            "}\n" +
            "\n" +
            "attribute def Access_Point {\n" +
            "  attribute sect: Section;\n" +
            "  attribute isOpen: boolean;\n" +
            "  attribute isGreen: boolean;\n" +
            "}\n";

    var tool = new FocusTool();
    tool.init();

    var ast = FocusMill.parser().parse_String(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);

    var gs = SysMLv2Mill.globalScope();
    var accessPoint = (OOTypeSymbol) gs.resolveType("Access_Point").get();

    SymTypeExpression type = SymTypeExpressionFactory.createTypeObject(
        accessPoint);

    assertTrue(Constants.isTypeCountable(type));
  }

  @Test
  public void testParseFields() throws IOException {
    var ast = FocusMill.parser()
        .parse_StringField("nat f (f_pattern);");
    assertThat(ast).isPresent();
  }

  @Test
  public void testStruct() throws IOException {
    var tool = new FocusTool();
    tool.init();
    var ast = FocusMill.parser()
        .parse_String("struct A { nat f ( fpattern ) ; }").get();
    assertThat(ast).isInstanceOf(ASTUserDefinedStruct.class);
    assertThat(((ASTUserDefinedStruct) ast).getFieldList()).isNotEmpty();
    var as = tool.createSymbolTable(ast);

    tool.completeSymbolTable(ast);
    TypeSymbol typeSym = as.resolveType("A").get();
    var symType = SymTypeExpressionFactory.createTypeObject(typeSym);
    var result = Constants.isTypeCountable(symType);
    assertThat(result).isTrue();
    FocusMill.reset();
  }

  @Test
  public void testStructsIntPrimitive() throws IOException {
    var tool = new FocusTool();
    tool.init();
    var ast = FocusMill.parser()
        .parse_String("struct A { int f ( fpattern ) ; }").get();
    assertThat(ast).isInstanceOf(ASTUserDefinedStruct.class);
    assertThat(((ASTUserDefinedStruct) ast).getFieldList()).isNotEmpty();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    var mcType = ((ASTUserDefinedStruct) ast).getField(0).getMCType();
    var symType = TypeCheck3.symTypeFromAST(mcType);
    assertThat(symType).isInstanceOf(SymTypePrimitive.class);
  }

  @Test
  public void testStructsNatPrimitive() throws IOException {
    var tool = new FocusTool();
    tool.init();
    var ast = FocusMill.parser()
        .parse_String("struct A { nat f ( fpattern ) ; }").get();
    assertThat(ast).isInstanceOf(ASTUserDefinedStruct.class);
    assertThat(((ASTUserDefinedStruct) ast).getFieldList()).isNotEmpty();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    var mcType = ((ASTUserDefinedStruct) ast).getField(0).getMCType();
    var symType = TypeCheck3.symTypeFromAST(mcType);
    assertThat(symType).isInstanceOf(SymTypePrimitive.class);
  }

  @Test
  public void testFunctions() {
    LogStub.init();
    var tool = new FocusTool();
    tool.init();

    var booleanType = SymTypeExpressionFactory.createPrimitive("boolean");
    var natType = SymTypeExpressionFactory.createPrimitive("nat");
    
    SymTypeOfFunction countableFunction = SymTypeExpressionFactory.createFunction(
        natType, booleanType, booleanType);
    assertTrue(Constants.isTypeCountable(countableFunction));

    SymTypeOfFunction infiniteDomainFunction = SymTypeExpressionFactory.createFunction(
        natType, booleanType, natType);
    assertFalse(Constants.isTypeCountable(infiniteDomainFunction));
  }
}
