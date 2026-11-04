package montibelle.transformer.generic.meta.sps;

import montibelle.focus._symboltable.ChannelSymbol;
import montibelle.focus._symboltable.ChannelSymbolBuilder;
import montibelle.transformer.generic.meta.bundle.FeedbackBundle;
import montibelle.transformer.generic.meta.bundle.IBundle;
import montibelle.transformer.generic.theories.Atom;
import montibelle.transformer.generic.theories.Binding;
import montibelle.transformer.generic.theories.Element;
import montibelle.transformer.generic.theories.IAtom;
import montibelle.transformer.generic.theories.IBinding;
import montibelle.transformer.generic.theories.IElement;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import static montibelle.transformer.generic.theories.DatatypeHelpers.orderedUnion;

public interface IComposition extends ISps {

  List<IInstance> getParts();

  IConnector getConnectors();

  default List<ISps> getAllSpses() {
    List<ISps> result = new ArrayList<>();
    result.add(getConnectors());
    result.addAll(getParts());
    return result;
  }

  default IBundle getFeedback() {
    List<ChannelSymbol> inputs = Collections.emptyList();
    List<ChannelSymbol> outputs = Collections.emptyList();
    for (ISps inst : getAllSpses()) {
      inputs = orderedUnion(inputs, inst.getInput().getChannels().stream().map(it ->
        new ChannelSymbolBuilder()
          .setName(it.getName())
          .setLocalName(it.getName())
          .setTypeName(it.getTypeName())
          .build()
      ).collect(Collectors.toList()));
      outputs = orderedUnion(outputs, inst.getOutput().getChannels().stream().map(it ->
        new ChannelSymbolBuilder()
          .setName(it.getName())
          .setLocalName(it.getName())
          .setTypeName(it.getTypeName())
          .build()
      ).collect(Collectors.toList()));
    }
    List<String> packageName = new ArrayList<>(this.getPackage());
    packageName.add(this.getName());
    return new FeedbackBundle(inputs, outputs, "Feedback", packageName, this.getInput().getTimingSymbol());
  }

  default IElement getTree() {
    Element res = null;
    if (getAllSpses().size() >= 2) {
      boolean initial = true;
      List<ISps> reversed = new ArrayList<>(getAllSpses());
      Collections.reverse(reversed);
      for (ISps instance : reversed) {
        if (initial) {
          res = new Atom(instance);
          initial = false;
        }
        else {
          Element inner = res;
          Atom outer = new Atom(instance);
          res = new Binding(Objects.requireNonNull(inner), outer);
        }
      }
    }
    return Objects.requireNonNull(res);
  }

  default List<IAtom> fromFinalToRaw() {
    if (getAllSpses().size() >= 2) {
      IElement tmp = getTree();
      List<IAtom> atoms = new ArrayList<>();
      while (tmp instanceof IBinding) {
        atoms.add(((IBinding) tmp).getOuter());
        tmp = ((IBinding) tmp).getInner();
      }
      atoms.add((IAtom) tmp);

      return atoms;
    }
    else {
      throw new Error("Datatype composition does not make sense with just one instance");
    }
  }

  default List<IBinding> bindingsRawToFinal() {
    List<IBinding> bindings = new ArrayList<>();
    IElement element = getTree();
    while (element instanceof IBinding) {
      bindings.add(0, (IBinding) element);
      element = ((IBinding) element).getInner();
    }
    return bindings;
  }

  default IBinding getFinalBinding() {
    return (IBinding) getTree();
  }
}
