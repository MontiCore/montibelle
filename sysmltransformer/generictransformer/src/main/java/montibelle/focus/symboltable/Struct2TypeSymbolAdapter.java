package montibelle.focus.symboltable;

import com.google.common.base.Preconditions;
import de.monticore.symbols.basicsymbols._symboltable.IBasicSymbolsScope;
import de.monticore.symbols.basicsymbols._symboltable.TypeSymbol;
import de.monticore.symbols.basicsymbols._symboltable.VariableSymbol;
import de.se_rwth.commons.SourcePosition;
import montibelle.focus.FocusMill;
import montibelle.focus._symboltable.UserDefinedStructSymbol;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class Struct2TypeSymbolAdapter extends TypeSymbol {

  protected UserDefinedStructSymbol adaptee;

  public Struct2TypeSymbolAdapter(UserDefinedStructSymbol adaptee) {
    super(Preconditions.checkNotNull(adaptee.getName()));
    this.adaptee = adaptee;
    this.spannedScope = FocusMill.scope();
  }

  protected UserDefinedStructSymbol getAdaptee() {
    return adaptee;
  }

  @Override
  public List<VariableSymbol> getVariableList() {

    var fields = getAdaptee().getFields();
    return fields.stream()
        .map(f -> new Field2VariableSymbolAdapter(f))
        .collect(Collectors.toList());
  }

  @Override
  public void setName(String name) {
    Preconditions.checkNotNull(name);
    Preconditions.checkArgument(!name.isBlank());
    getAdaptee().setName(name);
  }

  @Override
  public String getName() {
    return getAdaptee().getName();
  }

  @Override
  public String getFullName() {
    return getAdaptee().getFullName();
  }

  @Override
  public IBasicSymbolsScope getEnclosingScope() {
    return getAdaptee().getEnclosingScope();
  }

  @Override
  public SourcePosition getSourcePosition() {
    return getAdaptee().getSourcePosition();
  }

}
