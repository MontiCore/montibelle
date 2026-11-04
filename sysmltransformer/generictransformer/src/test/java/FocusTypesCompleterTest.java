import de.monticore.symbols.basicsymbols.BasicSymbolsMill;
import de.monticore.types.check.SymTypeExpressionFactory;
import de.monticore.types.check.SymTypeOfGenerics;
import de.monticore.types.mcbasictypes._ast.ASTMCQualifiedType;
import de.monticore.types.mccollectiontypes._ast.ASTMCListType;
import de.se_rwth.commons.logging.LogStub;
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

public class FocusTypesCompleterTest {

  @BeforeEach
  void setUp() {
    LogStub.init();
    FocusMill.init();
    BasicSymbolsMill.initializePrimitives();
  }

  @ParameterizedTest
  @ValueSource(strings = {"int", "boolean"})
  void completesPrimitiveFieldType(String typeName) throws IOException {
    var field = FocusMill.parser()
        .parse_StringField(typeName + " name (value_pattern);")
        .orElseThrow();
    field.setSymbol(FocusMill.fieldSymbolBuilder().setName("name").build());

    field.getMCType().setEnclosingScope(FocusMill.globalScope());
    new FocusCompleter().visit(field);

    assertThat(field.getSymbol().getSymType().isPrimitive()).isTrue();
    assertThat(typeName).isEqualTo(field.getSymbol().getSymType().printFullName());
  }

  @Test
  void completesStructFieldType() throws IOException {
    var scope = FocusMill.scope();
    var member = FocusMill.fieldSymbolBuilder()
        .setName("length")
        .setSymType(SymTypeExpressionFactory.createPrimitive("int"))
        .build();
    scope.add(member);
    var structType = FocusMill.userDefinedStructSymbolBuilder()
        .setName("Packet")
        .setFieldNamesList(List.of("length"))
        .build();
    scope.add(structType);

    var field = FocusMill.parser()
        .parse_StringField("Packet packet (value_pattern);")
        .orElseThrow();
    field.setSymbol(FocusMill.fieldSymbolBuilder().setName("packet").build());
    field.getMCType().setEnclosingScope(scope);
    var qualifiedType = (ASTMCQualifiedType) field.getMCType();
    qualifiedType.getMCQualifiedName().setEnclosingScope(scope);

    new FocusCompleter().visit(field);

    var resolvedType = field.getSymbol().getSymType().getTypeInfo();
    var resolvedMember = resolvedType.getVariableList().get(0);
    assertThat(resolvedMember.getName()).isEqualTo("length");
    assertThat(resolvedMember.getType().isPrimitive()).isTrue();
    assertThat(resolvedMember.getType().printFullName()).isEqualTo("int");
    assertThat(LogStub.getFindings()).isEmpty();
  }

  @Test
  void completesEnumFieldType() throws IOException {
    var scope = FocusMill.scope();
    var enumType = FocusMill.enumTypeSymbolBuilder()
        .setName("Section")
        .setFiniteChoicesList(List.of("sect1", "sect2", "sect3"))
        .build();
    scope.add(enumType);

    var field = FocusMill.parser()
        .parse_StringField("Section section (value_pattern);")
        .orElseThrow();
    field.setSymbol(FocusMill.fieldSymbolBuilder().setName("section").build());
    field.getMCType().setEnclosingScope(scope);

    var qualifiedType = (ASTMCQualifiedType) field.getMCType();
    qualifiedType.getMCQualifiedName().setEnclosingScope(scope);

    new FocusCompleter().visit(field);

    var resolvedType = field.getSymbol().getSymType().getTypeInfo();
    assertThat(resolvedType).isInstanceOf(EnumType2TypeSymbolAdapter.class);
    assertThat(resolvedType.getFullName()).isEqualTo(enumType.getFullName());
    assertThat(resolvedType.getEnclosingScope()).isSameAs(scope);
    assertThat(LogStub.getFindings()).isEmpty();
  }

  @Test
  void parseMCTypesForListTest() throws IOException {
    var parsed = FocusMill.parser().parse_StringMCType("List<int>").get();
    assertThat(parsed).isInstanceOf(ASTMCListType.class);
  }

  @Test
  void listCompleteTest() throws IOException {
    new FocusTool().init();
    var scope = FocusMill.scope();
    scope.setEnclosingScope(FocusMill.globalScope());
    var enumType = FocusMill.enumTypeSymbolBuilder()
        .setName("Section")
        .setFiniteChoicesList(List.of("sect1", "sect2", "sect3"))
        .build();
    scope.add(enumType);

    var parsedField = FocusMill.parser()
        .parse_StringField("List<Section> sections (value_pattern);");
    assertThat(parsedField).
        as("\"List<Section> field should parse; findings: %s",
            LogStub.getFindings()).isPresent();
    var field = parsedField.orElseThrow();
    field.setSymbol(FocusMill.fieldSymbolBuilder().setName("sections").build());

    assertThat(field.getMCType()).isInstanceOf(ASTMCListType.class);
    var listType = (ASTMCListType) field.getMCType();
    listType.setEnclosingScope(scope);
    var elementType =
        (ASTMCQualifiedType) listType.getMCTypeArgument().getMCTypeOpt().get();
    elementType.setEnclosingScope(scope);
    elementType.getMCQualifiedName().setEnclosingScope(scope);

    new FocusCompleter().visit(field);
    var symType = field.getSymbol().getSymType();
    assertThat(symType).isInstanceOf(SymTypeOfGenerics.class);
    var resolvedElementType = symType.asGenericType().getArgument(0).getTypeInfo();
    assertThat(resolvedElementType).isInstanceOf(EnumType2TypeSymbolAdapter.class);
  }
}
