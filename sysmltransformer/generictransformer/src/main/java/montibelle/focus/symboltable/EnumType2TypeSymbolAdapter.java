package montibelle.focus.symboltable;

import com.google.common.base.Preconditions;
import de.monticore.symbols.basicsymbols._symboltable.IBasicSymbolsScope;
import de.monticore.symbols.basicsymbols._symboltable.TypeSymbol;
import de.monticore.symbols.basicsymbols._symboltable.VariableSymbol;
import de.se_rwth.commons.SourcePosition;
import montibelle.focus.FocusMill;
import montibelle.focus._symboltable.EnumTypeSymbol;
import montibelle.focus._symboltable.UserDefinedStructSymbol;

import java.util.List;
import java.util.stream.Collectors;

public class EnumType2TypeSymbolAdapter extends TypeSymbol {

  protected EnumTypeSymbol adaptee;

  public EnumType2TypeSymbolAdapter(EnumTypeSymbol adaptee) {
    super(Preconditions.checkNotNull(adaptee.getName()));
    this.adaptee = adaptee;
    this.spannedScope = FocusMill.scope();
  }

  protected EnumTypeSymbol getAdaptee() {
    return adaptee;
  }

  @Override
  public void setName(String name) {
    Preconditions.checkNotNull(name);
    Preconditions.checkArgument(!name.isBlank());
    getAdaptee().setName(name);
  }

  public List<String> getFiniteChoicesList() {
    return adaptee.getFiniteChoicesList();
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
