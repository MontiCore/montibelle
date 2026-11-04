package montibelle.transformer.generic.theories;

import montibelle.focus._symboltable.ChannelSymbol;
import montibelle.transformer.generic.meta.sps.ISps;

import java.util.List;

public class Atom extends Element implements IAtom {

  private ISps instance;

  private final String name;

  public Atom(ISps instance) {
    this.instance = instance;
    this.name = instance.getName();
  }

  @Override
  public ISps getInstance() {
    return instance;
  }

  @Override
  public void setInstance(ISps instance) {
    this.instance = instance;
  }

  @Override
  public String getName() {
    return name;
  }

  @Override
  public List<ChannelSymbol> getInputChannels() {
    return instance.getInput().getChannels();
  }

  @Override
  public List<ChannelSymbol> getOutputChannels() {
    return instance.getOutput().getChannels();
  }

  @Override
  public int getDepth() {
    return this.toFinal().size() - 1;
  }

}
