package montibelle.focus._ast;

import montibelle.focus._symboltable.ChannelTypeSymbol;
import montibelle.focus._symboltable.EnumTypeSymbol;
import montibelle.focus._symboltable.UserDefinedStructSymbol;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

public class ASTDatatypes extends ASTDatatypesTOP {

  public  List<ChannelTypeSymbol> getChannelTypes() {
    return getChannelTypesSymbolList().stream()
        .filter(Optional::isPresent)
        .map(Optional::get)
        .collect(Collectors.toList());
  }

  public List<UserDefinedStructSymbol> getStructs() {
    return getUserDefinedStructsSymbolList().stream()
        .map(ts -> ts.get())
        .collect(Collectors.toList());
  }

  public List<EnumTypeSymbol> getEnums() {
    return getUserDefinedEnumsSymbolList().stream()
        .map(ts -> ts.get())
        .collect(Collectors.toList());
  }

}
