package montibelle.focus.symboltable;

import com.google.common.base.Preconditions;
import de.monticore.symbols.basicsymbols._symboltable.IBasicSymbolsScope;
import de.monticore.symbols.basicsymbols._symboltable.VariableSymbol;
import de.monticore.types.check.SymTypeExpression;
import de.se_rwth.commons.SourcePosition;
import montibelle.focus._symboltable.FieldSymbol;

public class Field2VariableSymbolAdapter extends VariableSymbol {
  protected FieldSymbol adaptee;

  public Field2VariableSymbolAdapter(FieldSymbol adaptee) {
    super(adaptee.getName());
    this.adaptee = adaptee;
  }

  protected FieldSymbol getAdaptee() {
    return adaptee;
  }

  @Override
  public SymTypeExpression getType() {
    return getAdaptee().getSymType();
  }

  @Override
  public void setName(String name) {
    Preconditions.checkNotNull(name);
    Preconditions.checkArgument(!name.isBlank());
    this.getAdaptee().setName(name);
  }

  @Override
  public String getName() {
    return this.getAdaptee().getName();
  }

  @Override
  public String getFullName() {
    return this.getAdaptee().getFullName();
  }

  @Override
  public IBasicSymbolsScope getEnclosingScope() {
    return this.getAdaptee().getEnclosingScope();
  }

  @Override
  public SourcePosition getSourcePosition() {
    return this.getAdaptee().getSourcePosition();
  }
}
