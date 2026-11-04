package montibelle.transformer.generic.meta.bundle;

import montibelle.focus._symboltable.ChannelSymbol;
import montibelle.focus._symboltable.TimingSymbol;

import java.util.List;

import static montibelle.transformer.generic.theories.DatatypeHelpers.orderedIntersection;

public class FeedbackBundle implements IBundle {

  private final String name;
  private final List<String> packageName;
  private final TimingSymbol timingSymbol;
  private final List<ChannelSymbol> channels;

  public FeedbackBundle(
      List<ChannelSymbol> inputs,
      List<ChannelSymbol> outputs,
      String name,
      List<String> packageName,
      TimingSymbol timingSymbol) {
    this.name = name;
    this.packageName = packageName;
    this.timingSymbol = timingSymbol;
    this.channels = orderedIntersection(inputs, outputs);
  }

  @Override
  public String getName() {
    return name;
  }

  @Override
  public List<String> getPackage() {
    return packageName;
  }

  @Override
  public TimingSymbol getTimingSymbol() {
    return timingSymbol;
  }

  @Override
  public List<ChannelSymbol> getChannels() {
    return channels;
  }

}
