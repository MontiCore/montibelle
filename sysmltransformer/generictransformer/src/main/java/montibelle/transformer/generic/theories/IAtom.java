package montibelle.transformer.generic.theories;

import montibelle.focus._symboltable.ChannelSymbol;
import montibelle.transformer.generic.meta.sps.ISps;

import java.util.List;

public interface IAtom extends IElement {
  ISps getInstance();

  void setInstance(ISps instance);

  @Override
  default String getName() {
    return getInstance().getName();
  }

  @Override
  default List<ChannelSymbol> getInputChannels() {
    return getInstance().getInput().getChannels();
  }

  @Override
  default List<ChannelSymbol> getOutputChannels() {
    return getInstance().getOutput().getChannels();
  }

  default int getDepth() {
    return this.toFinal().size() - 1;
  }

}
