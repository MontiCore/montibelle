package montibelle.focus._ast;

import montibelle.focus._symboltable.ChannelSymbol;

import java.util.List;
import java.util.Map;

public class ASTInstance extends ASTInstanceTOP {

  @Override
  public Map<ChannelSymbol, ChannelSymbol> get_inputMap() {
    return getInputConnectors().getMap();
  }

  @Override
  public Map<ChannelSymbol, ChannelSymbol> get_outputMap() {
    return getOutputConnectors().getMap();
  }

  @Override
  public List<ASTParameterValue> getParameterValues() {
    return getParameterValueList();
  }
}
