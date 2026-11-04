package montibelle.transformer.generic.meta.sps;

import montibelle.focus._ast.ASTParameterValue;
import montibelle.focus._symboltable.ChannelSymbol;
import montibelle.focus._symboltable.TimingSymbol;
import montibelle.transformer.generic.meta.bundle.IBundle;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public interface IInstance extends ISps {

  default Map<ChannelSymbol, ChannelSymbol> get_inputMap() {
    return getInputMap().getMap();
  }

  default IConnector getInputMap() {
    return new IConnector() {
      private final Map<ChannelSymbol, ChannelSymbol> map = get_inputMap();
      private final IBundle input = IInstance.this.getInput();
      private final IBundle output = getSps().getInput();

      @Override
      public String getName() {
        return "InputMap";
      }

      @Override
      public List<String> getPackage() {
        List<String> result = new ArrayList<>(IInstance.this.getPackage());
        result.add(IInstance.this.getName());
        return result;
      }

      @Override
      public Map<ChannelSymbol, ChannelSymbol> getMap() {
        return map;
      }

      @Override
      public IBundle getInput() {
        return input;
      }

      @Override
      public IBundle getOutput() {
        return output;
      }
    };
  }

  ISps getSps();

  default Map<ChannelSymbol, ChannelSymbol> get_outputMap() {
    return getOutputMap().getMap();
  }

  default IConnector getOutputMap() {
    return new IConnector() {
      private final Map<ChannelSymbol, ChannelSymbol> map = get_outputMap();
      private final IBundle input = getSps().getOutput();
      private final IBundle output = IInstance.this.getOutput();

      @Override
      public String getName() {
        return "OutputMap";
      }

      @Override
      public List<String> getPackage() {
        List<String> result = new ArrayList<>(IInstance.this.getPackage());
        result.add(IInstance.this.getName());
        return result;
      }

      @Override
      public Map<ChannelSymbol, ChannelSymbol> getMap() {
        return map;
      }

      @Override
      public IBundle getInput() {
        return input;
      }

      @Override
      public IBundle getOutput() {
        return output;
      }
    };
  }

  List<ASTParameterValue> getParameterValues();

  @Override
  default boolean isStrongCausal() {
    return getSps().isStrongCausal();
  }

  @Override
  default IBundle getInput() {
    return new IBundle() {
      @Override
      public String getName() {
        return "Input";
      }

      @Override
      public List<String> getPackage() {
        List<String> result = new ArrayList<>(IInstance.this.getPackage());
        result.add(IInstance.this.getName());
        return result;
      }

      @Override
      public TimingSymbol getTimingSymbol() {
        return getSps().getTiming();
      }

      @Override
      public List<ChannelSymbol> getChannels() {
        return get_inputMap().values().stream().distinct().sorted().collect(Collectors.toList());
      }
    };
  }

  @Override
  default IBundle getOutput() {
    return new IBundle() {
      @Override
      public String getName() {
        return "Output";
      }

      @Override
      public List<String> getPackage() {
        List<String> result = new ArrayList<>(IInstance.this.getPackage());
        result.add(IInstance.this.getName());
        return result;
      }

      @Override
      public TimingSymbol getTimingSymbol() {
        return getSps().getTiming();
      }

      @Override
      public List<ChannelSymbol> getChannels() {
        return get_outputMap().keySet().stream().distinct().sorted().collect(Collectors.toList());
      }
    };
  }

}
