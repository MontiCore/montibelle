package montibelle.focus._ast;

import focus.StateName;
import montibelle.focus._symboltable.ChannelSymbol;
import montibelle.transformer.generic.Constants;
import trafos.IExpressionPrinter;
import trafos.SourceMap;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class ASTConfiguration extends ASTConfigurationTOP {

  public static ASTConfiguration transformConfiguration
      (de.monticore.lang.componentconnector._ast.ASTConfiguration mildConfig,
       IExpressionPrinter expressionPrinter){

    return new ASTConfigurationBuilder()
        .setState(
            new ASTStateBuilder()
                .setName(new StateName(mildConfig.getState().getName()).toString())
                .setVariableValuesList(
                    mildConfig.getState().getVariableValueList().stream()
                        .map(it -> new ASTVariableValueBuilder()
                            .setDefinition(it.getVariable())
                            .setIsComprehension(false)
                            .setValue(expressionPrinter.print(it.getValue()))
                            .build())
                        .collect(Collectors.toList()))
                .build())
        .setOutputsList(
            mildConfig.getOutputList().stream()
                .map(it -> new ASTOutputBuilder()
                    .setValue(expressionPrinter.print(it.getValue()))
                    .setChannel(SourceMap.mapToFocus(it.getPortSymbol()))
                    .setIsComprehension(it.isComprehension())
                    .setIsListValue(it.isListValue())
                    .build())
                .collect(Collectors.toList()))
        .build();
  }

  private ASTVariableValue defaultVariableValue(
      ASTStateVariable variable,
      String value,
      boolean isComprehension
  ) {
    return new ASTVariableValueBuilder()
        .setDefinition(variable.getName())
        .setValue(value)
        .setIsComprehension(isComprehension)
        .build();
  }

  private ASTOutput defaultOutput(
      ChannelSymbol channel,
      String value,
      boolean isComprehension,
      boolean isListValue
  ) {
    return new ASTOutputBuilder()
        .setChannel(channel.getName())
        .setValue(value)
        .setIsComprehension(isComprehension)
        .setIsListValue(isListValue)
        .build();
  }

  private ASTState defaultState (
      String name,
      List<ASTVariableValue> variableValues
  ) {
    return new ASTStateBuilder()
        .setName(name)
        .setVariableValuesList(variableValues)
        .build();
  }

  private ASTConfiguration defaultConfiguration(
      String stateName,
      List<ASTVariableValue> variableValues,
      List<ASTOutput> outputs
  ) {
    ASTState astState = defaultState(stateName, variableValues);

    return new ASTConfigurationBuilder()
        .setState(astState)
        .setOutputsList(outputs)
        .build();
  }

  private ASTConfiguration defaultConfiguration(ASTState state, List<ASTOutput> outputs) {
    return new ASTConfigurationBuilder()
        .setState(state)
        .setOutputsList(outputs)
        .build();
  }

    public List<ASTConfiguration> chaosCompletion(
        List<ChannelSymbol> channels,
        List<ASTStateVariable> variables,
        boolean fixVariables
    ) {
      List<ASTConfiguration> configurations = new ArrayList<>();
      configurations.add(this);

      List<ASTOutput> originalOutputs = getOutputList();
      setOutputList(new ArrayList<>());

      List<ASTVariableValue> originalVariableValues = getState().getVariableValueList();
      getState().setVariableValueList(new ArrayList<>());

      for (ChannelSymbol channel : channels) {
        List<ASTConfiguration> next = new ArrayList<>();
        for (ASTConfiguration configuration : configurations) {
          next.addAll(configuration.chaosCompletionPerChannel(channel, originalOutputs));
        }
        configurations = next;
      }

      for (ASTStateVariable variable : variables) {
        List<ASTConfiguration> next = new ArrayList<>();
        for (ASTConfiguration configuration : configurations) {
          next.addAll(configuration.chaosCompletionPerVariable(variable, originalVariableValues, fixVariables));
        }
        configurations = next;
      }

      return configurations;
    }

  public List<ASTConfiguration> chaosCompletion(
      List<ChannelSymbol> channels,
      List<ASTStateVariable> variables) {
    return chaosCompletion(channels, variables, false);
  }

  private List<ASTConfiguration> chaosCompletionPerVariable(
      ASTStateVariable variable,
      List<ASTVariableValue> originalValues,
      boolean fixVariables
  ) {
    List<ASTConfiguration> partialConfigurations = new ArrayList<>();

    ASTVariableValue existingValueForVariable = null;
    for (ASTVariableValue it : originalValues) {
      if (it.getDefinition().equals(variable.getName())) {
        existingValueForVariable = it;
        break;
      }
    }

    if (existingValueForVariable != null) {
      List<ASTVariableValue> values = new ArrayList<>(getState().getVariableValueList());
      values.add(existingValueForVariable);
      getState().setVariableValueList(values);
      partialConfigurations.add(this);
    } else {
      if (fixVariables) {
        List<ASTVariableValue> values = new ArrayList<>(getState().getVariableValueList());
        values.add(defaultVariableValue(variable, variable.getPattern(), false));
        getState().setVariableValueList(values);
        partialConfigurations.add(this);
      } else if (Constants.isTypeFinite(variable.getSymbol().getSymType())) {
        for (String choice : Constants.getFiniteChoices(variable.getSymbol().getSymType())) {
          List<ASTVariableValue> valuesWithThisChoice =
              new ArrayList<>(getState().getVariableValueList());
          valuesWithThisChoice.add(defaultVariableValue(variable, choice, false));
          partialConfigurations.add(
              defaultConfiguration(getState().getName(), valuesWithThisChoice, getOutputList()));
        }
      } else {
        List<ASTVariableValue> values = new ArrayList<>(getState().getVariableValueList());
        values.add(defaultVariableValue(variable, Constants.ISABELLE_TRUE, true));
        getState().setVariableValueList(values);
        partialConfigurations.add(this);
      }
    }

    return partialConfigurations;
  }

  private List<ASTConfiguration> chaosCompletionPerChannel(
      ChannelSymbol channel,
      List<ASTOutput> originalOutputs
  ) {
    List<ASTConfiguration> partialConfigurations = new ArrayList<>();

    ASTOutput existingOutputForChannel = null;
    for (ASTOutput it : originalOutputs) {
      if (it.getChannelSymbol().getName().equals(channel.getName())) {
        existingOutputForChannel = it;
        break;
      }
    }

    if (existingOutputForChannel != null) {
      List<ASTOutput> outputs = new ArrayList<>(getOutputList());
      outputs.add(existingOutputForChannel);
      setOutputList(outputs);
      partialConfigurations.add(this);
    } else {
      if (channel.getTypeSymbol().getTimingSymbol().isTimeSyncronous()) {
        List<ASTOutput> outputs = new ArrayList<>(getOutputList());
        outputs.add(defaultOutput(channel, Constants.ISABELLE_NULL, false, false));
        setOutputList(outputs);
        partialConfigurations.add(this);
      } else if (Constants.isTypeFinite(channel.getTypeSymbol().getSymType())) {
        for (String choice : Constants.getFiniteChoices(channel.getTypeSymbol().getSymType())) {
          List<ASTOutput> outputsWithThisChoice = new ArrayList<>(getOutputList());
          outputsWithThisChoice.add(defaultOutput(channel, choice, false, false));
          partialConfigurations.add(defaultConfiguration(getState(), outputsWithThisChoice));
        }
      } else {
        List<ASTOutput> outputs = new ArrayList<>(getOutputList());
        outputs.add(defaultOutput(channel, Constants.ISABELLE_TRUE, true, false));
        setOutputList(outputs);
        partialConfigurations.add(this);
      }
    }

    return partialConfigurations;
  }
}



