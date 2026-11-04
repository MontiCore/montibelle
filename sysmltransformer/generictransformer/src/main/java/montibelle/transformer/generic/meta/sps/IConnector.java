package montibelle.transformer.generic.meta.sps;

import montibelle.focus._ast.ASTParameter;
import montibelle.focus._symboltable.ChannelSymbol;
import montibelle.focus._symboltable.TimingSymbol;
import montibelle.transformer.generic.meta.bundle.IBundle;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static montibelle.transformer.generic.Constants.SEP;

public interface IConnector extends ISps {

  Map<ChannelSymbol, ChannelSymbol> getMap();

  @Override
  default IBundle getInput() {
    return new IBundle() {
      @Override
      public String getName() {
        return IConnector.this.getIdentifier() + SEP + "Input";
      }

      @Override
      public List<String> getPackage() {
        List<String> result = new ArrayList<>(IConnector.this.getPackage());
        result.add(IConnector.this.getName());
        return result;
      }

      @Override
      public List<ChannelSymbol> getChannels() {
        return getMap().values().stream().distinct().sorted().collect(Collectors.toList());
      }

      @Override
      public TimingSymbol getTimingSymbol() {
        return getMap().keySet().iterator().next().getTypeSymbol().getTimingSymbol();
      }
    };
  }

  @Override
  default IBundle getOutput() {
    return new IBundle() {
      @Override
      public String getName() {
        return IConnector.this.getIdentifier() + SEP + "Output";
      }

      @Override
      public List<String> getPackage() {
        List<String> result = new ArrayList<>(IConnector.this.getPackage());
        result.add(IConnector.this.getName());
        return result;
      }

      @Override
      public List<ChannelSymbol> getChannels() {
        return getMap().keySet().stream().distinct().sorted().collect(Collectors.toList());
      }

      @Override
      public TimingSymbol getTimingSymbol() {
        return getMap().keySet().iterator().next().getTypeSymbol().getTimingSymbol();
      }
    };
  }

  @Override
  default boolean isStrongCausal() {
    return false;
  }

  @Override
  default List<ASTParameter> getParameters() {
    return Collections.emptyList();
  }

}
