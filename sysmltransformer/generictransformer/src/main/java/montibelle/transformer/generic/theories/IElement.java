package montibelle.transformer.generic.theories;

import montibelle.focus._symboltable.ChannelSymbol;

import java.util.ArrayList;
import java.util.List;

public interface IElement {
  String getName();

  List<ChannelSymbol> getInputChannels();

  List<ChannelSymbol> getOutputChannels();

  IRoute getToFinal();

  void setToFinal(IRoute toFinal);

  boolean isOuterElement();

  void setOuterElement(boolean isOuterElement);

  default boolean isInnerElement() {
    return !isOuterElement();
  }

  default List<IRoute> toFinal() {
    List<IRoute> accu = new ArrayList<>();
    IElement subj = this;
    while (subj.getToFinal() != null) {
      accu.add(subj.getToFinal());
      subj = subj.getToFinal().getFinal();
    }
    return accu;
  }
}
