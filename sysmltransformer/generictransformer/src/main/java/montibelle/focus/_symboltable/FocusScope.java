package montibelle.focus._symboltable;

import de.monticore.symboltable.modifiers.AccessModifier;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Predicate;

public class FocusScope extends FocusScopeTOP {
  public FocusScope() {
    super();
  }

  public FocusScope(boolean shadowing) {
    super();
    this.shadowing = shadowing;
    this.name = Optional.empty();
  }

  public FocusScope(IFocusScope enclosingScope) {
    super(enclosingScope);
  }

  public FocusScope(IFocusScope enclosingScope, boolean shadowing) {
    super();
    this.setEnclosingScope(enclosingScope);
    this.shadowing = shadowing;
    this.name = Optional.empty();
  }

  @Override
  public List<ElementSymbol> resolveElementSubKinds(
      boolean foundSymbols,
      String name,
      AccessModifier modifier,
      Predicate<ElementSymbol> predicate) {

    List<ElementSymbol> res =
        new ArrayList<>(super.resolveElementSubKinds(foundSymbols, name, modifier, predicate));

    res.addAll(resolveBundleLocallyMany(foundSymbols, name, modifier, x -> predicate.test(x)));
    res.addAll(resolveSpsLocallyMany(foundSymbols, name, modifier, x -> predicate.test(x)));
    res.addAll(resolveDatatypesLocallyMany(foundSymbols, name, modifier, x -> predicate.test(x)));
    res.addAll(resolveDataIncLocallyMany(foundSymbols, name, modifier, x -> predicate.test(x)));
    res.addAll(resolveRefinementLocallyMany(foundSymbols, name, modifier, x -> predicate.test(x)));

    res.addAll(resolveStateSpaceLocallyMany(foundSymbols, name, modifier, x -> predicate.test(x)));
    res.addAll(resolveAutomatonLocallyMany(foundSymbols, name, modifier, x -> predicate.test(x)));
    res.addAll(resolveEventAutomatonLocallyMany(foundSymbols, name, modifier, x -> predicate.test(x)));

    return res;
  }

  @Override
  public List<SpsSymbol> resolveSpsSubKinds(
      boolean foundSymbols,
      String name,
      AccessModifier modifier,
      Predicate<SpsSymbol> predicate) {

    List<SpsSymbol> res = new ArrayList<>();

    res.addAll(resolveSpecificationLocallyMany(foundSymbols, name, modifier, x -> predicate.test(x)));
    res.addAll(resolveCompositionLocallyMany(foundSymbols, name, modifier, x -> predicate.test(x)));
    res.addAll(resolveInstanceLocallyMany(foundSymbols, name, modifier, x -> predicate.test(x)));
    res.addAll(resolveConnectorsLocallyMany(foundSymbols, name, modifier, x -> predicate.test(x)));
    res.addAll(resolveAutomatonLocallyMany(foundSymbols, name, modifier, x -> predicate.test(x)));

    return res;
  }

  @Override
  public List<AutomatonSymbol> resolveAutomatonSubKinds(
      boolean foundSymbols,
      String name,
      AccessModifier modifier,
      Predicate<AutomatonSymbol> predicate) {

    return new ArrayList<>(
        resolveEventAutomatonLocallyMany(foundSymbols, name, modifier, x -> predicate.test(x))
    );
  }
}

