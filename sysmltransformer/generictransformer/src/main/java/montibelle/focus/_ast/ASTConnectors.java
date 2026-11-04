package montibelle.focus._ast;

import montibelle.focus._symboltable.ChannelSymbol;
import java.util.LinkedHashMap;
import java.util.Map;

public class ASTConnectors extends ASTConnectorsTOP {

  @Override
  public Map<ChannelSymbol, ChannelSymbol> getMap() {
    Map<ChannelSymbol, ChannelSymbol> result = new LinkedHashMap<>();

    for (var it : getChannelMappingList()) {
      result.put(
          getEnclosingScope().resolveChannel(it.getKey()).get(),
          getEnclosingScope().resolveChannel(it.getValue()).get()
      );
    }

    return result;
  }
}
