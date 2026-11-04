package montibelle.focus;

import de.monticore.lang.componentconnector.ComponentConnectorMill;
import de.monticore.lang.componentconnector._ast.ASTConnector;
import de.monticore.lang.componentconnector._symboltable.MildComponentSymbol;
import de.monticore.lang.componentconnector._symboltable.MildInstanceSymbol;
import de.monticore.lang.componentconnector._visitor.ComponentConnectorTraverser;
import de.monticore.symbols.compsymbols._symboltable.PortSymbol;
import de.monticore.symbols.compsymbols._symboltable.SubcomponentSymbol;
import de.monticore.types.mcbasictypes._ast.ASTMCType;
import de.se_rwth.commons.logging.Log;
import focus.Bundles;
import focus.Sps;
import focus.SymType2MCTypePrinter;
import montibelle.focus._ast.ASTBundle;
import montibelle.focus._ast.ASTBundleBuilder;
import montibelle.focus._ast.ASTChannelMapping;
import montibelle.focus._ast.ASTChannelMappingBuilder;
import montibelle.focus._ast.ASTComposition;
import montibelle.focus._ast.ASTCompositionBuilder;
import montibelle.focus._ast.ASTConnectors;
import montibelle.focus._ast.ASTConnectorsBuilder;
import montibelle.focus._ast.ASTInstance;
import montibelle.focus._ast.ASTInstanceBuilder;
import montibelle.focus._ast.ASTParameter;
import montibelle.focus._ast.ASTParameterBuilder;
import montibelle.focus._ast.ASTParameterValueBuilder;
import montibelle.focus._ast.ASTSession;
import montibelle.focus._ast.ASTTheory;
import montibelle.focus._symboltable.BundleSymbol;
import montibelle.focus._symboltable.ChannelSymbol;
import montibelle.focus._symboltable.InstanceSymbol;
import montibelle.focus._symboltable.SessionSymbol;
import montibelle.focus._symboltable.SpsSymbol;
import montibelle.transformer.generic.Constants;
import montibelle.transformer.generic.sessions.SessionGenerator;
import montibelle.transformer.util.FreemarkerInterface;
import trafos.IExpressionPrinter;
import trafos.ITypePrinter;
import trafos.Ports2BundleTrafo;
import trafos.SourceMap;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static montibelle.transformer.generic.theories.DatatypeHelpers.orderedIntersection;
import static montibelle.transformer.generic.theories.DatatypeHelpers.orderedUnion;

public class Transformer {

  public static void transformComp(
    Path target,
    MildComponentSymbol component,
    BundleSymbol input,
    BundleSymbol output,
    ITypePrinter typePrinter,
    boolean comment,
    SessionGenerator sessionGenerator) {

    List<ASTParameter> params = component.getParameterList().stream()
        .map(it -> {
          ASTMCType mcType;
          try {
            mcType = FocusMill.parser().parse_StringMCType(
                new SymType2MCTypePrinter().print(it.getType())).get();
          }
          catch (IOException e) {
            throw new RuntimeException(e);
          }
          return new ASTParameterBuilder()
              .setName("var_" + it.getName())
              .setMCType(mcType)
              .build();
        })
      .collect(Collectors.toList());

    List<InstanceSymbol> parts = new ArrayList<>();
    boolean hasMissing = false;

    for (SubcomponentSymbol subcomp : component.getSubcomponents()) {
      String name = SourceMap.INSTANCE.mapToFocus((MildInstanceSymbol) subcomp);
      Optional<InstanceSymbol> resolved = FocusMill.globalScope().resolveInstance(name);
      if (resolved.isPresent()) {
        parts.add(resolved.get());
      } else {
        hasMissing = true;
      }
    }
    if (hasMissing) {
      Log.error(
          "While buildind the composition " + component.getName() + ", " +
              "some instances could not be resolved. They should have been " +
              "created beforehand?"
      );
    }

    List<ASTChannelMapping> channelMappings = new ArrayList<ASTChannelMapping>();
    for(ASTConnector connector : component.getConnectorsList()){

      ChannelSymbol src;
      if (connector.getTarget().sizeParts() == 2) {

        src = input.getEnclosingScope().resolveChannel(
            SourceMap.mapToFocus(component.getPort(connector.getTarget().getQName()).get())
          ).get();
      } else {
        MildInstanceSymbol mildInstance = (MildInstanceSymbol) component
          .getSubcomponents(connector.getTarget().getPartsList().get(0)).get();
        String portName = String.join(".", connector.getTarget().subListParts(1, 3) );
        PortSymbol portSymbol = mildInstance.getType().getTypeInfo().getPort(portName).get();

        src = input.getEnclosingScope()
            .resolveChannel(SourceMap.INSTANCE.mapToFocus(portSymbol,mildInstance))
            .get();
      }

      ChannelSymbol tgt;
      if (connector.getSource().sizeParts() == 2) {
        tgt = input.getEnclosingScope().resolveChannel(
          SourceMap.mapToFocus(
            component.getPort(connector.getSource().getQName()).get()
          )
        ).get();
      } else {
        MildInstanceSymbol mildInstance = (MildInstanceSymbol) component
          .getSubcomponents(connector.getSource().getPartsList().get(0))
          .get();

        String portName = String.join(".", connector.getSource().subListParts(1, 3));
        PortSymbol portSymbol = mildInstance.getType().getTypeInfo().getPort(portName).get();

        tgt = input.getEnclosingScope()
          .resolveChannel(SourceMap.INSTANCE.mapToFocus(portSymbol, mildInstance))
          .get();
      }
      ASTChannelMapping channelMapping = new ASTChannelMappingBuilder()
        .setKey(src.getName())
        .setValue(tgt.getName())
        .build();
      channelMappings.add( channelMapping);
    }

    String connectorFqn = component.getFullName() + ".connector";
    String connectorInputName = connectorFqn + "." +
        connectorFqn.replace('.', '_') + "_Input";
    String connectorOutputName = connectorFqn + "." +
        connectorFqn.replace('.', '_') + "_Output";

    List<ChannelSymbol> inputChannels = combineAndDistinctChannels(
      input.getChannels(),
      parts.stream()
        .flatMap(p -> p.getOutput().getChannels().stream())
        .collect(Collectors.toList())
    );

    List<ChannelSymbol> outputChannels = combineAndDistinctChannels(
      output.getChannels(),
      parts.stream()
        .flatMap(p -> p.getInput().getChannels().stream())
        .collect(Collectors.toList())
    );

    List<List<ChannelSymbol>> inputLists = new ArrayList<>();
    inputLists.add(inputChannels);
    for (InstanceSymbol p : parts) {
      inputLists.add(p.getInput().getChannels());
    }
    List<List<ChannelSymbol>> outputLists = new ArrayList<>();
    outputLists.add(outputChannels);
    for (InstanceSymbol p : parts) {
      outputLists.add(p.getOutput().getChannels());
    }

    List<ChannelSymbol> allInputs = inputLists.get(0);
    for (int i = 1; i < inputLists.size(); i++) {
      allInputs = orderedUnion(allInputs, inputLists.get(i));
    }

    List<ChannelSymbol> allOutputs = outputLists.get(0);
    for (int i = 1; i < outputLists.size(); i++) {
      allOutputs = orderedUnion(allOutputs, outputLists.get(i));
    }

    List<String> names = orderedIntersection(allInputs, allOutputs).stream()
      .map(ChannelSymbol::getName)
      .collect(Collectors.toList());

    ASTBundle feedback = new ASTBundleBuilder()
      .setName(component.getFullName() + ".Feedback")
      .setChannelsList(names)
      .setTiming(input.getTimingName())
      .uncheckedBuild();

    ASTConnectors connector = new ASTConnectorsBuilder()
      .setFqn(connectorFqn)
      .setChannelMappingsList(channelMappings)
      .setStrongCausal(false)
      .setInputBundle(connectorInputName)
      .setOutputBundle(connectorOutputName)
      .uncheckedBuild();

    ASTBundle connectorInput = new ASTBundleBuilder()
      .setName(connectorInputName)
      .setChannelsList(inputChannels.stream()
        .map(ChannelSymbol::getName)
        .collect(Collectors.toList())
      )
      .setTiming(input.getTimingName())
      .uncheckedBuild();

    FocusTool focusTool = new FocusTool();
    focusTool.createSymbolTable(connectorInput);
    ASTSession sessionC = Bundles.createSession(connectorInput);
    focusTool.createSymbolTable(sessionC);
    ASTTheory theoryI = Bundles.createTheory(connectorInput, sessionC.getName());
    focusTool.createSymbolTable(theoryI);
    focusTool.completeSymbolTable(connectorInput);
    focusTool.completeSymbolTable(sessionC);
    focusTool.completeSymbolTable(theoryI);

    if (!theoryI.isSubstituted()) {
      FreemarkerInterface.instance.generate(
        Constants.BUNDLE_DEF,
        target.resolve(theoryI.getSession().getPath()
          .resolve(theoryI.getFilename() + ".thy")).toAbsolutePath(),
        comment,
        theoryI,
        connectorInput
      );

      sessionGenerator.add(theoryI);
      sessionGenerator
        .addDependency(theoryI, FocusMill.globalScope()
          .resolveTheory("data_inc.Data_inc").get())
        .addDependency(theoryI, FocusMill.globalScope()
          .resolveTheory("user.Datatypes").get());
    }

    ASTBundle connectorOutput = new ASTBundleBuilder()
      .setName(connectorOutputName)
      .setChannelsList(
        outputChannels.stream()
          .map(ChannelSymbol::getName)
          .collect(Collectors.toList())
      )
      .setTiming(output.getTimingName())
      .uncheckedBuild();

    focusTool.createSymbolTable(connectorOutput);
    ASTTheory theoryO = Bundles.createTheory(connectorOutput, sessionC.getName());
    focusTool.createSymbolTable(theoryO);
    focusTool.completeSymbolTable(connectorOutput);
    focusTool.completeSymbolTable(theoryO);

    if (!theoryO.isSubstituted()) {
      FreemarkerInterface.instance.generate(
          Constants.BUNDLE_DEF,
          target.resolve(theoryO.getSession().getPath()
                  .resolve(theoryO.getFilename() + ".thy"))
              .toAbsolutePath(),
          comment,
          theoryO,
          connectorOutput
      );
      sessionGenerator.add(theoryO);
    }

    ASTComposition comp = new ASTCompositionBuilder()
      .setInputBundle(input.getName())
      .setOutputBundle(output.getName())
      .setFqn(component.getFullName())
      .setPartsList(parts.stream().map(InstanceSymbol::getName).collect(Collectors.toList()))
      .setConnectors(connector)
      .setFeedbackBundle(feedback.getName())
      .setStrongCausal(component.isStrongCausal())
      .setParametersList(params)
      .uncheckedBuild();

    focusTool.createSymbolTable(comp);
    ASTSession sess = Sps.createSession(comp);
    focusTool.createSymbolTable(sess);
    ASTTheory th = Sps.createTheory(comp, sess.getName());
    focusTool.createSymbolTable(th);

    ASTSession conSess = Sps.createSession(connector);
    focusTool.createSymbolTable(conSess);
    ASTTheory conTh = Sps.createTheory(connector, conSess.getName());
    focusTool.createSymbolTable(conTh);

    focusTool.completeSymbolTable(conSess);
    focusTool.completeSymbolTable(conTh);

    focusTool.completeSymbolTable(comp);
    focusTool.completeSymbolTable(sess);
    focusTool.completeSymbolTable(th);

    if (!conTh.isSubstituted()) {
      FreemarkerInterface.instance.generate(
        Constants.CONNECTOR,
        target.resolve(conTh.getSession().getPath().resolve(conTh.getFilename() + ".thy"))
          .toAbsolutePath(),
        comment,
        conTh,
        connector
      );

      sessionGenerator
        .add(conTh)
        .addDependency(conTh, FocusMill.globalScope().resolveTheory("data_inc.Data_inc").get())
        .addDependency(conTh, FocusMill.globalScope().resolveTheory("user.Datatypes").get());
      if(!theoryI.isSubstituted()) {
        sessionGenerator.addDependency(conTh, theoryI);
      }
      if(!theoryO.isSubstituted()) {
        sessionGenerator.addDependency(conTh, theoryO);
      }
    }

    focusTool.createSymbolTable(feedback);
    ASTSession sessF = Bundles.createSession(feedback);
    ASTTheory theoryF = Bundles.createTheory(feedback, sessF.getName());
    focusTool.createSymbolTable(theoryF);
    Optional<SessionSymbol> potSess = FocusMill.globalScope().resolveSession(sessF.getName());

    if (potSess.isEmpty() || !potSess.get().isPresentAstNode()) {
      potSess.ifPresent(s -> {
        s.getEnclosingScope().remove(s);
        s.setEnclosingScope(null);
      });
      focusTool.createSymbolTable(sessF);
      focusTool.completeSymbolTable(sessF);
    }

    focusTool.completeSymbolTable(feedback);
    focusTool.completeSymbolTable(theoryF);

    if (!theoryF.isSubstituted()) {
      FreemarkerInterface.instance.generate(
        Constants.BUNDLE_DEF,
        target.resolve(theoryF.getSession().getPath().resolve(theoryF.getFilename() + ".thy"))
            .toAbsolutePath(),
        comment,
        theoryF,
        feedback
      );

      if(!potSess.isPresent() || !potSess.get().isPresentAstNode()) {
        sessionGenerator
          .addDependency(theoryF, FocusMill.globalScope().resolveTheory("data_inc.Data_inc").get())
          .addDependency(theoryF, FocusMill.globalScope().resolveTheory("user.Datatypes").get());
      }

      sessionGenerator.add(theoryF);
    }

    if (!th.isSubstituted()) {
      FreemarkerInterface.instance.generate(
        Constants.COMPOSITION,
        target.resolve(th.getSession().getPath().resolve(th.getFilename() + ".thy"))
            .toAbsolutePath(),
        comment,
        th,
        comp
      );

      sessionGenerator
        .add(th)
        .addDependency(th, FocusMill.globalScope().resolveTheory("data_inc.Data_inc").get())
        .addDependency(th, FocusMill.globalScope().resolveTheory("user.Datatypes").get())
        .addDependency(th, input.getTheorySymbol())
        .addDependency(th, output.getTheorySymbol());
      if(!conTh.isSubstituted()) {
        sessionGenerator.addDependency(th, conTh);
      }
      sessionGenerator.addDependenciesOnSymbol(th, comp.getPartsSymbolList().stream()
        .map(opt -> opt.get().getTheorySymbol())
        .collect(Collectors.toList()));
      if(!theoryF.isSubstituted()) {
        sessionGenerator.addDependency(th, theoryF);
      }
    }
  }

  private static List<ChannelSymbol> combineAndDistinctChannels(
      List<ChannelSymbol> channels1,
      List<ChannelSymbol> channels2) {

    return Stream.concat(channels1.stream(), channels2.stream())
        .collect(Collectors.collectingAndThen(
            Collectors.toMap(
                ChannelSymbol::getName,
                c -> c,
                (a, b) -> a,
                LinkedHashMap::new
            ),
            m -> new ArrayList<>(m.values())
        ))
        .stream()
        .sorted(Comparator.comparing(ChannelSymbol::getLocalName))
        .collect(Collectors.toList());
  }

  public static ASTInstance generateInstance(
      Path target,
      MildInstanceSymbol instance,
      MildComponentSymbol composition,
      IExpressionPrinter expressionPrinter,
      ITypePrinter typePrinter,
      boolean comment,
      SessionGenerator sessionGenerator) {

    Ports2BundleTrafo trafo = new Ports2BundleTrafo(
        new ASTBundleBuilder().setName(instance.getFullName() + ".Input").setTiming("EVENT"),
        new ASTBundleBuilder().setName(instance.getFullName() + ".Output").setTiming("EVENT"),
        typePrinter,
        false,
        instance
    );

    ComponentConnectorTraverser traverser = ComponentConnectorMill.inheritanceTraverser();
    traverser.add4CompSymbols(trafo);
    instance.getType().getTypeInfo().getPorts().forEach(p -> p.accept(traverser));

    trafo.getInputBuilder().getChannelsList().sort(null);
    trafo.getOutputBuilder().getChannelsList().sort(null);

    String definitionName = instance.getType().printFullName();
    SpsSymbol definition = FocusMill.globalScope().resolveSps(definitionName).get();

    List<ASTParameter> params = composition.getParameterList().stream()
        .map(it -> {
          ASTMCType mcType;
          try {
            mcType = FocusMill.parser().parse_StringMCType(
                new SymType2MCTypePrinter().print(it.getType())).get();
          }
          catch (IOException e) {
            throw new RuntimeException(e);
          }
          return new ASTParameterBuilder()
              .setName("var_" + it.getName())
              .setMCType(mcType)
              .build();
        })
        .collect(Collectors.toList());

    ASTInstance inst = new ASTInstanceBuilder()
        .setFqn(instance.getFullName())
        .setSSps(definitionName)
        .setParametersList(params)
        .setInputBundle(instance.getFullName() + ".Input")
        .setOutputBundle(instance.getFullName() + ".Output")
        .setStrongCausal(definition.isStrong())
        .setParameterValuesList(instance.getParameterValuesList().stream()
            .map(it -> new ASTParameterValueBuilder()
                .setValue(expressionPrinter.print(it.getValue()))
                .setDefinition(SourceMap.INSTANCE.mapToFocus(it.getVariableSymbol()))
                .setName("val_" + it.getVariable())
                .build())
            .collect(Collectors.toList()))
        .setInputConnectors(new ASTConnectorsBuilder()
            .setFqn(instance.getFullName() + ".InputMap")
            .setInputBundle(instance.getFullName() + ".Input")
            .setOutputBundle(definition.getInputName())
            .setChannelMappingsList(instance.getType().getTypeInfo().getIncomingPorts().stream()
                .map(it -> new ASTChannelMappingBuilder()
                    .setKey(SourceMap.INSTANCE.mapToFocus(it))
                    .setValue(SourceMap.INSTANCE.mapToFocus(it, instance))
                    .build())
                .collect(Collectors.toList()))
            .build())
        .setOutputConnectors(new ASTConnectorsBuilder()
            .setFqn(instance.getFullName() + ".OutputMap")
            .setInputBundle(definition.getOutputName())
            .setOutputBundle(instance.getFullName() + ".Output")
            .setChannelMappingsList(instance.getType().getTypeInfo().getOutgoingPorts().stream()
                .map(it -> new ASTChannelMappingBuilder()
                    .setKey(SourceMap.INSTANCE.mapToFocus(it, instance))
                    .setValue(SourceMap.INSTANCE.mapToFocus(it))
                    .build())
                .collect(Collectors.toList()))
            .build())
        .uncheckedBuild();

    FocusTool focusTool = new FocusTool();
    ASTBundle bundleI = trafo.getInputBuilder().uncheckedBuild();
    focusTool.createSymbolTable(bundleI);
    ASTSession sessI = Bundles.createSession(bundleI);
    focusTool.createSymbolTable(sessI);
    ASTTheory thI = Bundles.createTheory(bundleI, sessI.getName());
    focusTool.createSymbolTable(thI);

    focusTool.completeSymbolTable(bundleI);
    focusTool.completeSymbolTable(sessI);
    focusTool.completeSymbolTable(thI);

    if (!thI.isSubstituted()) {
      FreemarkerInterface.instance.generate(
          Constants.BUNDLE_DEF,
          target.resolve(thI.getSession().getPath().resolve(thI.getFilename() + ".thy")).toAbsolutePath(),
          comment,
          thI,
          bundleI
      );

      sessionGenerator.add(thI);
      sessionGenerator
          .addDependency(thI, FocusMill.globalScope().resolveTheory("data_inc.Data_inc").get())
          .addDependency(thI, FocusMill.globalScope().resolveTheory("user.Datatypes").get());
    }

    ASTBundle bundleO = trafo.getOutputBuilder().uncheckedBuild();
    focusTool.createSymbolTable(bundleO);
    ASTTheory thO = Bundles.createTheory(bundleO, sessI.getName());
    focusTool.createSymbolTable(thO);

    focusTool.completeSymbolTable(bundleO);
    focusTool.completeSymbolTable(thO);

    if (!thO.isSubstituted()) {
      FreemarkerInterface.instance.generate(
          Constants.BUNDLE_DEF,
          target.resolve(thO.getSession().getPath().resolve(thO.getFilename() + ".thy")).toAbsolutePath(),
          comment,
          thO,
          bundleO
      );

      sessionGenerator.add(thO);
    }

    focusTool.createSymbolTable(inst);
    ASTSession sess = Sps.createSession(inst);
    ASTSession sessCI = Sps.createSession(inst.getInputConnectors());
    ASTSession sessCO = Sps.createSession(inst.getOutputConnectors());
    focusTool.createSymbolTable(sess);
    focusTool.createSymbolTable(sessCI);
    focusTool.createSymbolTable(sessCO);
    ASTTheory th = Sps.createTheory(inst, sess.getName());
    ASTTheory thCI = Sps.createTheory(inst.getInputConnectors(), sessCI.getName());
    ASTTheory thCO = Sps.createTheory(inst.getOutputConnectors(), sessCO.getName());
    focusTool.createSymbolTable(th);
    focusTool.createSymbolTable(thCI);
    focusTool.createSymbolTable(thCO);

    focusTool.completeSymbolTable(inst);
    focusTool.completeSymbolTable(sess);
    focusTool.completeSymbolTable(sessCI);
    focusTool.completeSymbolTable(sessCO);
    focusTool.completeSymbolTable(th);
    focusTool.completeSymbolTable(thCI);
    focusTool.completeSymbolTable(thCO);

    if (!thCI.isSubstituted()) {
      FreemarkerInterface.instance.generate(
          Constants.CONNECTOR,
          target.resolve(thCI.getSession().getPath().resolve(thCI.getFilename() + ".thy")).toAbsolutePath(),
          comment,
          thCI,
          inst.getInputConnectors()
      );

      sessionGenerator
          .add(thCI)
          .addDependency(thCI, FocusMill.globalScope().resolveTheory("data_inc.Data_inc").get())
          .addDependency(thCI, FocusMill.globalScope().resolveTheory("user.Datatypes").get())
          .addDependency(thCI, inst.getInputConnectors().getInputBundleSymbol().getTheorySymbol())
          .addDependency(thCI, inst.getInputConnectors().getOutputBundleSymbol().getTheorySymbol());
    }

    if (!thCO.isSubstituted()) {
      FreemarkerInterface.instance.generate(
          Constants.CONNECTOR,
          target.resolve(thCO.getSession().getPath().resolve(thCO.getFilename() + ".thy")).toAbsolutePath(),
          comment,
          thCO,
          inst.getOutputConnectors()
      );

      sessionGenerator
          .add(thCO)
          .addDependency(thCO, FocusMill.globalScope().resolveTheory("data_inc.Data_inc").get())
          .addDependency(thCO, FocusMill.globalScope().resolveTheory("user.Datatypes").get())
          .addDependency(thCO, inst.getOutputConnectors().getInputBundleSymbol().getTheorySymbol())
          .addDependency(thCO, inst.getOutputConnectors().getOutputBundleSymbol().getTheorySymbol());
    }

    if (!th.isSubstituted()) {
      FreemarkerInterface.instance.generate(
          Constants.INSTANCE,
          target.resolve(th.getSession().getPath().resolve(th.getFilename() + ".thy")).toAbsolutePath(),
          comment,
          th,
          inst
      );

      sessionGenerator
          .add(th)
          .addDependency(th, FocusMill.globalScope().resolveTheory("data_inc.Data_inc").get())
          .addDependency(th, FocusMill.globalScope().resolveTheory("user.Datatypes").get())
          .addDependency(th, thI)
          .addDependency(th, thO);

      if (!thCI.isSubstituted()) {
        sessionGenerator.addDependency(th, thCI);
      }
      if (!thCO.isSubstituted()) {
        sessionGenerator.addDependency(th, thCO);
      }
      sessionGenerator.addDependency(th, inst.getSSpsSymbol().getTheorySymbol());
    }

    return inst;
  }

}
