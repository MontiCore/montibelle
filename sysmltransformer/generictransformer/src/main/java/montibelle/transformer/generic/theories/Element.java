package montibelle.transformer.generic.theories;

import montibelle.focus._symboltable.ChannelSymbol;

import java.util.ArrayList;
import java.util.List;

public abstract class Element implements IElement {

  @Override
  public abstract String getName();

  @Override
  public abstract List<ChannelSymbol> getInputChannels();

  @Override
  public abstract List<ChannelSymbol> getOutputChannels();

  private IRoute toFinal = null;

  private boolean isOuterElement = false;

  @Override
  public IRoute getToFinal() {
    return toFinal;
  }

  @Override
  public void setToFinal(IRoute toFinal) {
    this.toFinal = toFinal;
  }

  @Override
  public boolean isOuterElement() {
    return isOuterElement;
  }

  @Override
  public void setOuterElement(boolean isOuterElement) {
    this.isOuterElement = isOuterElement;
  }

  @Override
  public List<IRoute> toFinal() {
    List<IRoute> accu = new ArrayList<>();
    IElement subj = this;
    while (subj.getToFinal() != null) {
      accu.add(subj.getToFinal());
      subj = subj.getToFinal().getFinal();
    }
    return accu;
  }
}
