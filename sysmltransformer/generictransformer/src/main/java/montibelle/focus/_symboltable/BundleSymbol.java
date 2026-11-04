package montibelle.focus._symboltable;

import montibelle.focus.FocusMill;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

public class BundleSymbol extends BundleSymbolTOP {
  public BundleSymbol(String name) {
    super(name);
  }

  public TimingSymbol getTiming() {
    return FocusMill.globalScope().resolveTiming(getTimingName()).get();
  }

  public List<ChannelSymbol> getChannels() {
    List<ChannelSymbol> result = new ArrayList<>();
    for (String channelName : getChannelNamesList()) {
      result.add(getEnclosingScope().resolveChannel(channelName).get());
    }
    return result;
  }

  public TheorySymbol getCodeTheorySymbol() {
    return getEnclosingScope().resolveTheory(getCodeTheory()).get();
  }

  public List<ChannelSymbol> decardinalizedChannels() {
    List<ChannelSymbol> result = new ArrayList<>();

    for (ChannelSymbol c : getChannels()) {
      if (c.getCardinality() > 1) {
        for (int i = 1; i <= c.getCardinality(); i++) {
          result.add(new ChannelSymbolBuilder()
              .setName(c.getName() + "_" + i)
              .setTypeName(c.getTypeName())
              .setCardinality(1)
              .setLocalName(c.getLocalName() + "_" + i)
              .setPattern(c.getPattern() + "_" + i)
              .build());
        }
      } else {
        result.add(c);
      }
    }

    return result;
  }

  public List<ChannelTypeSymbol> uniqueTypes() {
    Set<ChannelTypeSymbol> unique = new LinkedHashSet<>();

    for (ChannelSymbol channel : getChannels()) {
      unique.add(channel.getTypeSymbol());
    }

    List<ChannelTypeSymbol> result = new ArrayList<>(unique);
    result.sort(null);
    return result;
  }
}
