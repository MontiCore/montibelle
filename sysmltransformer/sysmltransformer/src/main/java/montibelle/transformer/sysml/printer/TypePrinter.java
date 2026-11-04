package montibelle.transformer.sysml.printer;

import de.monticore.lang.sysmlv2._symboltable.ISysMLv2Scope;
import de.monticore.symboltable.ISymbol;
import de.monticore.types.check.SymTypeArray;
import de.monticore.types.check.SymTypeOfObject;
import de.se_rwth.commons.logging.Log;
import montibelle.transformer.generic.meta.IIdentifiable;
import montibelle.transformer.sysml.Constants;
import montibelle.transformer.sysml.extensions.ISymbolKt;
import trafos.GenericTypePrinter;

import java.util.Arrays;
import java.util.List;

public class TypePrinter extends GenericTypePrinter {

  public TypePrinter() {
    super(Constants.BASIC_TYPES);
  }

  @Override
  public void visit(SymTypeOfObject object) {
    List<String> candidates = Arrays.asList(
        object.print(),
        object.printFullName(),
        object.getTypeInfo().getName(),
        object.getTypeInfo().getFullName()
    );
    for (String candidate : candidates) {
      if (Constants.BASIC_TYPES.containsKey(candidate)) {
        printer.print(Constants.BASIC_TYPES.get(candidate));
        return;
      }
    }

    var scope = object.getTypeInfo().getEnclosingScope();
    if (!(scope instanceof ISysMLv2Scope)) {
      super.visit(object);
      return;
    }
    var sysmlScope = (ISysMLv2Scope) scope;

    var enumDef = sysmlScope.resolveEnumDef(object.printFullName());
    var attrDef = sysmlScope.resolveAttributeDef(object.printFullName());

    if (enumDef.isPresent()) {
      printer.print(fullyQualifiedName(enumDef.get()));
      return;
    }

    if (attrDef.isPresent()) {
      printer.print(fullyQualifiedName(attrDef.get()));
      return;
    }

    Log.debug(
        "Unknown SysML type name: \"" + object.print() + "\". Proceed with caution.",
        this.getClass().getSimpleName()
    );

    super.visit(object);
  }

  @Override
  public void visit(SymTypeArray type) {
    type.getArgument().accept(this);
    printer.print(" list");
  }

  private static String fullyQualifiedName(ISymbol symbol) {
    IIdentifiable identifiable = new IIdentifiable() {
      @Override
      public String getName() {
        return symbol.getName();
      }

      @Override
      public List<String> getPackage() {
        return ISymbolKt.getPackageNameFromScope(symbol);
      }
    };
    return identifiable.getIdentifier();
  }
}
