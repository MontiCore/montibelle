package montibelle.transformer.generic.theories;

import montibelle.focus._symboltable.ChannelSymbol;

import java.util.ArrayList;
import java.util.List;

import static montibelle.transformer.generic.theories.DatatypeHelpers.orderedUnion;

public class Binding extends Element implements IBinding {

  private final Element inner;

  private final Atom outer;

  public Binding(Element inner, Atom outer) {
    this.inner = inner;
    this.outer = outer;

    Route innerRoute = new Route(inner, this);
    Route outerRoute = new Route(outer, this);
    outer.setOuterElement(true);
    inner.setOuterElement(false);
    outer.setToFinal(innerRoute);
    inner.setToFinal(outerRoute);
  }

  @Override
  public Element getInner() {
    return inner;
  }

  @Override
  public Atom getOuter() {
    return outer;
  }

  @Override
  public String getName() {
    if (getToFinal() == null) return "";
    int counter = 1;
    Binding subj = this;
    while (subj.getInner() instanceof Binding) {
      counter++;
      subj = (Binding) subj.getInner();
    }
    return "_h" + counter;
  }

  @Override
  public List<ChannelSymbol> getInputChannels() {
    return orderedUnion(outer.getInputChannels(), inner.getInputChannels());
  }

  @Override
  public List<ChannelSymbol> getOutputChannels() {
    return orderedUnion(outer.getOutputChannels(), inner.getOutputChannels());
  }

  @Override
  public List<Atom> getAtomsFinalToRaw() {
    List<Atom> atoms = new ArrayList<>();
    atoms.add(this.outer);
    Element element = this.inner;
    while (element instanceof Binding) {
      atoms.add(((Binding) element).getOuter());
      element = ((Binding) element).getInner();
    }
    atoms.add((Atom) element);
    return atoms;
  }

}
