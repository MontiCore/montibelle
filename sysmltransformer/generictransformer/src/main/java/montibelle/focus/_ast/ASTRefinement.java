package montibelle.focus._ast;

import de.se_rwth.commons.logging.Log;
import montibelle.focus.FocusMill;
import montibelle.focus._symboltable.*;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

public class ASTRefinement extends ASTRefinementTOP {


  private DatatypesSymbol datatypes;

  public DatatypesSymbol getDatatypes() {
    if (datatypes == null) {
      datatypes = FocusMill.globalScope().resolveDatatypes("Datatypes").get();
    }
    return datatypes;
  }

  public List<RefinementSymbol> getTransitiveRefinements() {
    return getTransitiveRefinementSymbolList()
        .stream()
        .map(Optional::get)
        .collect(Collectors.toList());
  }

  public List<RefinementSymbol> getSubComponentRefinements() {
    return calculateSubComponentRefinements();
  }

  public boolean hasMatchingEventAutomata() {
    return getRefined() instanceof AutomatonSymbol
        && getRough() instanceof AutomatonSymbol
        && getRefined().getInput().getTiming().equals(getRough().getInput().getTiming())
        && getRefined().getInput().getTiming().isEventBased();
  }

  public boolean hasMatchingTimesliceAutomata() {
    return false;
  }

  public boolean isAutomaticHlrNarrowing() {
    if (!(getRough() instanceof SpecificationSymbol) || !(getRefined() instanceof SpecificationSymbol)) {
      return false;
    }

    SpecificationSymbol r = (SpecificationSymbol) getRefined();
    SpecificationSymbol o = (SpecificationSymbol) getRough();

    return r.isStrong() == o.isStrong()
        && r.getInput().getTiming().getName().equals(o.getInput().getTiming().getName())
        && r.getPredicatesLen() >= o.getPredicatesLen();
  }

  public boolean isCompositeHlrNarrowing() {
    return checkAutomaticRefinement();
  }

  public boolean isHlrDecomposition() {
    if (!(getRefined() instanceof CompositionSymbol) || !(getRough() instanceof SpecificationSymbol)) {
      return false;
    }

    CompositionSymbol comp = (CompositionSymbol) getRefined();
    SpecificationSymbol spec = (SpecificationSymbol) getRough();

    if (!comp.getInput().getTiming().equals(spec.getInput().getTiming())) {
      return false;
    }

    boolean allSpecs = comp.getParts().stream()
        .allMatch(p -> p.getSps() instanceof SpecificationSymbol);

    boolean anySpecs = comp.getParts().stream()
        .anyMatch(p -> p.getSps() instanceof SpecificationSymbol);

    return allSpecs && anySpecs;
  }

  public boolean isLlrRefinementEvent() {
    return getRefined() instanceof EventAutomatonSymbol
        && getRough() instanceof SpecificationSymbol;
  }

  public boolean checkAutomaticRefinement() {

    if (!(getRough() instanceof CompositionSymbol) || !(getRefined() instanceof CompositionSymbol)) {
      return false;
    }

    CompositionSymbol roughComp = (CompositionSymbol) getRough();
    CompositionSymbol refinedComp = (CompositionSymbol) getRefined();

    for (var instanceToFind : roughComp.getParts()) {
      boolean found = false;

      for (var part : refinedComp.getParts()) {
        if (part.getSimpleName().equals(instanceToFind.getSimpleName())) {
          found = true;
        }
      }

      if (!found) {
        return false;
      }
    }

    for (var instanceToFind : refinedComp.getParts()) {
      boolean found = false;

      for (var part : roughComp.getParts()) {
        if (part.getSimpleName().equals(instanceToFind.getSimpleName())) {
          found = true;
        }
      }

      if (!found) {
        return false;
      }
    }

    for (var connectionToFind : roughComp.getConnectors().getChannelMappings()) {
      boolean found = false;

      for (var mapping : refinedComp.getConnectors().getChannelMappings()) {

        if (refinedComp.getInternalChannel(mapping.getKeyChannel()).getName()
            .equals(roughComp.getInternalChannel(connectionToFind.getKeyChannel()).getName())
            &&
            refinedComp.getInternalChannel(mapping.getValueChannel()).getName()
                .equals(roughComp.getInternalChannel(connectionToFind.getValueChannel()).getName())) {

          found = true;
        }
      }

      if (!found) {
        return false;
      }
    }

    for (var connectionToFind : refinedComp.getConnectors().getChannelMappings()) {
      boolean found = false;

      for (var mapping : roughComp.getConnectors().getChannelMappings()) {

        if (refinedComp.getInternalChannel(connectionToFind.getKeyChannel()).getName()
            .equals(roughComp.getInternalChannel(mapping.getKeyChannel()).getName())
            &&
            refinedComp.getInternalChannel(connectionToFind.getValueChannel()).getName()
                .equals(roughComp.getInternalChannel(mapping.getValueChannel()).getName())) {

          found = true;
        }
      }

      if (!found) {
        return false;
      }
    }

    return true;
  }

  public  List<RefinementSymbol> calculateSubComponentRefinements() {
    List<RefinementSymbol> subRefs = new ArrayList<>();

    if (isCompositeHlrNarrowing()) {

      CompositionSymbol refinedComp = (CompositionSymbol) getRefined();
      CompositionSymbol roughComp = (CompositionSymbol) getRough();

      for (var refPart : refinedComp.getParts()) {
        for (var roughPart : roughComp.getParts()) {

          if (refPart.getSimpleName().equals(roughPart.getSimpleName())
              && !refPart.getSpsName().equals(roughPart.getSpsName())) {

            String name = roughPart.getSpsName() + ".ref." + refPart.getSpsName();
            Optional<RefinementSymbol> symbol = FocusMill.globalScope().resolveRefinement(name);

            if (symbol.isPresent()) {

              if (!subRefs.contains(symbol.get())) {
                subRefs.add(symbol.get());
              }

            } else {
              Log.error("0xFFF01 Could not resolve the refinement symbol " + name);
            }
          }
        }
      }
    }

    return subRefs;
  }
}
