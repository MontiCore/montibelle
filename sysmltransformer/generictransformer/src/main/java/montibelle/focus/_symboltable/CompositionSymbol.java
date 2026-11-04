package montibelle.focus._symboltable;

import java.util.ArrayList;
import java.util.List;

public class CompositionSymbol extends CompositionSymbolTOP {
  public CompositionSymbol(String name) {
    super(name);
  }

  public List<SpsSymbol> getAllSpses() {
    List<SpsSymbol> result = new ArrayList<>();
    result.add(getConnectors());
    result.addAll(getParts());
    return result;
  }

  public ChannelSymbol getInternalChannel(ChannelSymbol outerChannel) {
    for (SpsSymbol part : getParts()) {
      InstanceSymbol instance = (InstanceSymbol) part;
      for (ChannelMappingSymbol channelMapping : instance.getInputMap().getChannelMappings()) {
        if (channelMapping.getValueChannel().equals(outerChannel)) {
          return channelMapping.getKeyChannel();
        }
      }
      for (ChannelMappingSymbol channelMapping : instance.getOutputMap().getChannelMappings()) {
        if (channelMapping.getKeyChannel().equals(outerChannel)) {
          return channelMapping.getValueChannel();
        }
      }
    }

    return outerChannel;
  }
}

