package montibelle.focus._ast;

import de.se_rwth.commons.Names;
import montibelle.focus._symboltable.ChannelSymbol;
import montibelle.focus._symboltable.SpsSymbol;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import static montibelle.transformer.generic.theories.DatatypeHelpers.orderedUnion;

public class ASTComposition extends ASTCompositionTOP {

  public List<ASTSps> _allSpses() {
    List<ASTSps> result = new ArrayList<>();
    result.add(getConnectors());
    result.addAll(getPartsDefinitionListUnsafe());
    return result;
  }

  private Element get_tree() {
    Element res = null;

    if (_allSpses().size() >= 2) {
      boolean initial = true;
      List<ASTSps> reversed = new ArrayList<>(_allSpses());
      Collections.reverse(reversed);

      for (ASTSps sps : reversed) {
        SpsSymbol instance = sps.getSymbol();
        if (initial) {
          res = new Atom(instance);
          initial = false;
        } else {
          Element inner = res;
          Atom outer = new Atom(instance);
          res = new Binding(inner, outer);
        }
      }
    }

    if (res == null) {
      throw new IllegalStateException("Tree could not be constructed");
    }
    return res;
  }

  public List<Atom> _fromFinalToRaw() {
    if (_allSpses().size() >= 2) {
      Element tmp = get_tree();
      List<Atom> atoms = new ArrayList<>();

      while (tmp instanceof Binding) {
        Binding binding = (Binding) tmp;
        atoms.add(binding.getOuter());
        tmp = binding.getInner();
      }
      atoms.add((Atom) tmp);

      return atoms;
    } else {
      throw new Error("Datatype composition does not make sense with just one instance");
    }
  }

  public List<Binding> _bindingsRawToFinal() {
    List<Binding> bindings = new ArrayList<>();
    Element element = get_tree();

    while (element instanceof Binding) {
      Binding binding = (Binding) element;
      bindings.add(0, binding);
      element = binding.getInner();
    }

    return bindings;
  }

  public Binding get_finalBinding() {
    return (Binding) get_tree();
  }

  public static class Atom extends Element {
    private final SpsSymbol instance;
    private final String name;

    public Atom(SpsSymbol instance) {
      this.instance = instance;
      this.name = Names.getSimpleName(instance.getName());
    }

    public SpsSymbol getInstance() {
      return instance;
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

    public int getDepth() {
      return toFinal().size() - 1;
    }
  }

  public static abstract class Element {
    private Route toFinal;
    private boolean isOuterElement = false;

    public abstract String getName();

    public abstract List<ChannelSymbol> getInputChannels();

    public abstract List<ChannelSymbol> getOutputChannels();

    public Route getToFinal() {
      return toFinal;
    }

    public void setToFinal(Route toFinal) {
      this.toFinal = toFinal;
    }

    public boolean isOuterElement() {
      return isOuterElement;
    }

    public void setOuterElement(boolean outerElement) {
      isOuterElement = outerElement;
    }

    public boolean isInnerElement() {
      return !isOuterElement;
    }

    public List<Route> toFinal() {
      List<Route> accu = new ArrayList<>();
      Element subj = this;

      while (subj.getToFinal() != null) {
        accu.add(subj.getToFinal());
        subj = subj.getToFinal().getFinal();
      }

      return accu;
    }
  }

  public static class Binding extends Element {
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

    public Element getInner() {
      return inner;
    }

    public Atom getOuter() {
      return outer;
    }

    @Override
    public String getName() {
      if (getToFinal() == null) {
        return "";
      }

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

    public List<Atom> getAtomsFinalToRaw() {
      List<Atom> atoms = new ArrayList<>();
      atoms.add(this.outer);

      Element element = this.inner;
      while (element instanceof Binding) {
        Binding binding = (Binding) element;
        atoms.add(binding.getOuter());
        element = binding.getInner();
      }

      atoms.add((Atom) element);
      return atoms;
    }
  }

  public static class Route {
    private final Element raw;
    private final Binding fin;

    public Route(Element raw, Binding fin) {
      this.raw = raw;
      this.fin = fin;
    }

    public Element getRaw() {
      return raw;
    }

    public Binding getFinal() {
      return fin;
    }
  }
}
