package montibelle.focus._ast;

import montibelle.focus.FocusMill;
import montibelle.focus._symboltable.ChannelSymbol;
import montibelle.focus._symboltable.DatatypesSymbol;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static java.util.Collections.emptyList;
import static java.util.stream.Collectors.toList;

public class ASTEventAutomaton extends ASTEventAutomatonTOP {

    public boolean getNeedsCatchAll() {
      Optional<DatatypesSymbol> datatypesOpt =
        FocusMill.globalScope().resolveDatatypes("Datatypes");
      boolean hasMultipleGlobalChannelTypes =
        datatypesOpt.isPresent() && datatypesOpt.get().sizeChannelTypes() > 1;
      boolean hasMultipleInputChannels = getInputBundleSymbol().getChannels().size() > 1;
      return hasMultipleGlobalChannelTypes || hasMultipleInputChannels;
    }

    @Override
    public boolean isFinite() {
      boolean eventTransitionsFinite =
        getEventTransitionsMap().values().stream().flatMap(List::stream).noneMatch(
          t -> t.getResult().getOutputList().stream().anyMatch(
            ASTOutput::isIsComprehension)
          || t.getResult().getState().getVariableValueList().stream().anyMatch(
            ASTVariableValue::isIsComprehension)
        );
      boolean tickTransitionsFinite =
        tickTransitions.stream().noneMatch(
          t -> t.getResult().getOutputList().stream().anyMatch(
            ASTOutput::isIsComprehension)
          || t.getResult().getState().getVariableValueList().stream().anyMatch(
            ASTVariableValue::isIsComprehension)
        );
      boolean initialFinite =
        initial.stream().noneMatch(
          c -> c.getOutputList().stream().anyMatch(
            ASTOutput::isIsComprehension)
          || c.getState().getVariableValueList().stream().anyMatch(
            ASTVariableValue::isIsComprehension)
        );

      return eventTransitionsFinite && tickTransitionsFinite && initialFinite;
    }

    @Override
    public List<ASTConfiguration> getInitialList() {
      if(isStrongCausal() && (getInputBundleSymbol().getTiming().isTimeSyncronous()
          || getInputBundleSymbol().getTiming().isTimeSyncronous())) {
        return super.getInitialList().stream().flatMap(
          it -> it.chaosCompletion(getOutputBundleSymbol().getChannels(),
          getStates().getStateVariableList()).stream()
        ).collect(toList());
      }
      else {
        return super.getInitialList().stream().flatMap( it ->
          it.chaosCompletion(emptyList(), getStates().getStateVariableList()).stream()
        ).collect(toList());
      }
    }

    private ASTTransition defaultTransition(ASTTransition transition, ASTConfiguration result) {
      return new ASTTransitionBuilder()
        .setStart(transition.getStart())
        .setGuard(transition.getGuard())
        .setDocumentation(transition.getDocumentation())
        .setResult(result)
        .build();
    }

    public Map<ChannelSymbol, List<ASTTransition>> getEventTransitionsMap() {
      Map<ChannelSymbol, List<ASTTransition>> eventTransitionsMap = new LinkedHashMap<>();
      for (ASTEventTransition item : getEventTransitionList()) {
        eventTransitionsMap.put(
          getEnclosingScope().resolveChannel(item.getKey()).get(),
          item.getValueList()
        );
      }
      return eventTransitionsMap;
    }

    public Map<ChannelSymbol, List<ASTTransition>> getEventTransitions() {
      Map<ChannelSymbol, List<ASTTransition>> eventTransitions = new LinkedHashMap<>();
      for (ChannelSymbol key: getEventTransitionsMap().keySet()){
        List<ASTTransition> transitions = getEventTransitionsMap().get(key).stream()
          .flatMap(transition -> {
            List<ChannelSymbol> channelsInUse = transition.getResult()
              .getOutputList().stream()
              .map(ASTOutput::getChannelSymbol)
              .collect(toList());
            return transition.getResult().chaosCompletion(channelsInUse,
              getStates().getStateVariableList(), true).stream()
              .map(config -> defaultTransition(transition, config));
          })
          .collect(toList());
        eventTransitions.put(key, transitions);
      }
      return eventTransitions;
    }

    public List<ASTTransition> getTickTransitionsListCompleted() {
      return super.getTickTransitionsList().stream().flatMap( transition -> {
        List<ChannelSymbol> channelsInUse = transition.getResult().getOutputList().stream().map(
          ASTOutput::getChannelSymbol
        ).collect(toList());
        return transition.getResult().chaosCompletion(channelsInUse,
          getStates().getStateVariableList(), true).stream().map(
          config -> defaultTransition(transition, config)
        );
      }).collect(toList());
    }
}
