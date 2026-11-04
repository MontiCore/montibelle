package montibelle.transformer.generic.theories;

import montibelle.focus._symboltable.ChannelSymbol;

import java.util.ArrayList;
import java.util.List;

import static montibelle.transformer.generic.theories.DatatypeHelpers.orderedUnion;

public interface IBinding extends IElement {
  IElement getInner();

  IAtom getOuter();

  @Override
  default String getName() {
    if (getToFinal() == null) return "";
    int counter = 1;
    IBinding subj = this;
    while (subj.getInner() instanceof IBinding) {
      counter++;
      subj = (IBinding) subj.getInner();
    }
    return "_h" + counter;
  }

  @Override
  default List<ChannelSymbol> getInputChannels() {
    return orderedUnion(getOuter().getInputChannels(), getInner().getInputChannels());
  }

  @Override
  default List<ChannelSymbol> getOutputChannels() {
    return orderedUnion(getOuter().getOutputChannels(), getInner().getOutputChannels());
  }

  default List<? extends IAtom> getAtomsFinalToRaw() {
    List<IAtom> atoms = new ArrayList<>();
    atoms.add(this.getOuter());
    IElement element = this.getInner();
    while (element instanceof IBinding) {
      atoms.add(((IBinding) element).getOuter());
      element = ((IBinding) element).getInner();
    }
    atoms.add((IAtom) element);
    return atoms;
  }

}
