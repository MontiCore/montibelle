package montibelle.focus._symboltable;

import com.google.common.collect.LinkedListMultimap;
import de.monticore.lang.sysmlparts.symboltable.adapters.AttributeDef2TypeSymbolAdapter;
import de.monticore.symbols.basicsymbols._symboltable.TypeSymbol;
import de.monticore.symboltable.ISymbol;
import de.monticore.symboltable.modifiers.AccessModifier;
import montibelle.focus.symboltable.EnumType2TypeSymbolAdapter;
import montibelle.focus.symboltable.Struct2TypeSymbolAdapter;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.Predicate;

public interface IFocusScope extends IFocusScopeTOP {

  @Override
  default List<TypeSymbol> resolveAdaptedTypeLocallyMany(
      boolean foundSymbols,
      String name,
      AccessModifier modifier,
      Predicate<TypeSymbol> predicate
  ) {
    var adapted = new ArrayList<TypeSymbol>();

    var struct = resolveUserDefinedStructLocally(name);
    if (struct.isPresent()) {
      adapted.add(new Struct2TypeSymbolAdapter(struct.get()));
    }
    else {
      var enumType = resolveEnumTypeLocally(name);
      if (enumType.isPresent()) {
        adapted.add(new EnumType2TypeSymbolAdapter(enumType.get()));
      }
    }

    return adapted;
  }

  default <E extends ISymbol> Optional<E> filterSymbolName(
      String name,
      LinkedListMultimap<String, E> symbols) {

    Set<E> resolvedSymbols = new LinkedHashSet<>();

    if (symbols.containsKey(name)) {
      for (E symbol : symbols.get(name)) {
        if (symbol.getName().equals(name) || symbol.getFullName().equals(name)) {
          resolvedSymbols.add(symbol);
        }
      }
    }
    return getResolvedOrThrowException(resolvedSymbols);
  }

  @Override
  default Optional<TheorySymbol> filterTheory(
      String name,
      LinkedListMultimap<String, TheorySymbol> symbols) {
    return filterSymbolName(name, symbols);
  }

  @Override
  default Optional<ElementSymbol> filterElement(
      String name,
      LinkedListMultimap<String, ElementSymbol> symbols) {
    return filterSymbolName(name, symbols);
  }

  @Override
  default Optional<SpecificationSymbol> filterSpecification(
      String name,
      LinkedListMultimap<String, SpecificationSymbol> symbols) {
    return filterSymbolName(name, symbols);
  }

  @Override
  default Optional<SpsSymbol> filterSps(
      String name,
      LinkedListMultimap<String, SpsSymbol> symbols) {
    return filterSymbolName(name, symbols);
  }

  @Override
  default Optional<InstanceSymbol> filterInstance(
      String name,
      LinkedListMultimap<String, InstanceSymbol> symbols) {
    return filterSymbolName(name, symbols);
  }

  @Override
  default Optional<CompositionSymbol> filterComposition(
      String name,
      LinkedListMultimap<String, CompositionSymbol> symbols) {
    return filterSymbolName(name, symbols);
  }

  @Override
  default Optional<RefinementSymbol> filterRefinement(
      String name,
      LinkedListMultimap<String, RefinementSymbol> symbols) {
    return filterSymbolName(name, symbols);
  }

  @Override
  default Optional<BundleSymbol> filterBundle(
      String name,
      LinkedListMultimap<String, BundleSymbol> symbols) {
    return filterSymbolName(name, symbols);
  }

  @Override
  default Optional<ChannelSymbol> filterChannel(
      String name,
      LinkedListMultimap<String, ChannelSymbol> symbols) {
    return filterSymbolName(name, symbols);
  }

  @Override
  default Optional<ChannelMappingSymbol> filterChannelMapping(
      String name,
      LinkedListMultimap<String, ChannelMappingSymbol> symbols) {
    return filterSymbolName(name, symbols);
  }

  @Override
  default Optional<ChannelTypeSymbol> filterChannelType(
      String name,
      LinkedListMultimap<String, ChannelTypeSymbol> symbols) {
    return filterSymbolName(name, symbols);
  }

  @Override
  default Optional<EnumTypeSymbol> filterEnumType(
      String name,
      LinkedListMultimap<String, EnumTypeSymbol> symbols) {
    return filterSymbolName(name, symbols);
  }

  @Override
  default Optional<UserDefinedStructSymbol> filterUserDefinedStruct(
      String name,
      LinkedListMultimap<String, UserDefinedStructSymbol> symbols) {
    return filterSymbolName(name, symbols);
  }

  @Override
  default Optional<FieldSymbol> filterField(
      String name,
      LinkedListMultimap<String, FieldSymbol> symbols) {
    return filterSymbolName(name, symbols);
  }

  @Override
  default Optional<StateSpaceSymbol> filterStateSpace(
      String name,
      LinkedListMultimap<String, StateSpaceSymbol> symbols) {
    return filterSymbolName(name, symbols);
  }

  @Override
  default Optional<EventAutomatonSymbol> filterEventAutomaton(
      String name,
      LinkedListMultimap<String, EventAutomatonSymbol> symbols) {
    return filterSymbolName(name, symbols);
  }
}
