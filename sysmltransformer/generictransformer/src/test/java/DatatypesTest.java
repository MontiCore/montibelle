import de.monticore.lang.sysmlv2.SysMLv2Mill;
import de.monticore.symbols.oosymbols._symboltable.FieldSymbolBuilder;
import de.monticore.symbols.oosymbols._symboltable.OOTypeSymbolBuilder;
import de.monticore.types.check.SymTypeExpressionFactory;
import montibelle.focus.FocusMill;
import montibelle.focus.FocusTool;
import montibelle.focus._ast.ASTFocusElement;
import montibelle.focus._symboltable.EnumTypeSymbolBuilder;
import montibelle.transformer.generic.Constants;
import org.junit.jupiter.api.Test;
import trafos.GenericTypePrinter;

import static cc2focus.OOTypeSymbol2FocusType.buildStruct;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class DatatypesTest {

  @Test
  public void testBuildStruct() {
    SysMLv2Mill.init();
    SysMLv2Mill.initializePrimitives();
    var field = new FieldSymbolBuilder()
        .setName("field")
        .setType(SymTypeExpressionFactory.createPrimitive("int"))
        .build();

    var scope = SysMLv2Mill.scope();
    scope.add(field);

    var ts = new OOTypeSymbolBuilder()
        .setName("ts")
        .setSpannedScope(scope)
        .build();

    var typePrinter = new GenericTypePrinter();

    FocusMill.init();
    var struct = buildStruct(ts, typePrinter);
    var gs = FocusMill.globalScope();
    if (gs.resolveEnumType("int").isEmpty()) {
      var bool = new EnumTypeSymbolBuilder()
          .setName("int")
          .build();
      gs.add(bool);
    }
    new FocusTool().createSymbolTable( (ASTFocusElement) struct);
    new FocusTool().completeSymbolTable( (ASTFocusElement) struct);
    var structSym = FocusMill.globalScope().resolveUserDefinedStruct("ts").get();

    assertTrue(
        structSym.getFields().stream()
            .allMatch(fieldVar -> Constants.isTypeCountable(fieldVar.getSymType())),
        "All struct fields should be countable"
    );
  }

}
