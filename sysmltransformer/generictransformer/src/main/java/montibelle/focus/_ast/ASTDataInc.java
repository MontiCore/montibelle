package montibelle.focus._ast;

import montibelle.focus._symboltable.ChannelTypeSymbol;

import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

public class ASTDataInc extends ASTDataIncTOP {

  public List<ChannelTypeSymbol> getChannelTypes() {
    return getChannelTypesSymbolList().stream()
        .filter(Optional::isPresent)
        .map(Optional::get)
        .sorted()
        .collect(Collectors.toList());
  }

}
