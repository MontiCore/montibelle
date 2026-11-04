package montibelle.focus;

import de.monticore.lang.componentconnector._symboltable.MildComponentSymbol;
import de.monticore.types.mcbasictypes._ast.ASTMCType;
import de.se_rwth.commons.logging.Log;
import focus.Sps;
import focus.StateName;
import focus.SymType2MCTypePrinter;
import montibelle.focus._ast.ASTEventAutomatonBuilder;
import montibelle.focus._ast.ASTEventTransitionBuilder;
import montibelle.focus._ast.ASTParameterBuilder;
import montibelle.focus._ast.ASTStateSpaceBuilder;
import montibelle.focus._ast.ASTStateVariableBuilder;
import montibelle.focus._ast.ASTTransitionBuilder;
import montibelle.focus._symboltable.BundleSymbol;
import montibelle.transformer.generic.Constants;
import montibelle.transformer.generic.sessions.ExportFiles;
import montibelle.transformer.generic.sessions.SessionGenerator;
import montibelle.transformer.generic.sessions.Theories;
import montibelle.transformer.generic.sessions.TheoryEntry;
import montibelle.transformer.generic.theories.TheoryGenerator;
import montibelle.transformer.util.FreemarkerInterface;
import trafos.IExpressionPrinter;
import trafos.ITypePrinter;
import trafos.SourceMap;

import java.io.IOException;
import java.nio.file.Path;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

import static montibelle.focus._ast.ASTConfiguration.transformConfiguration;
import static montibelle.transformer.generic.Constants.INCR_CODE_BUNDLE_TEMPLATE;
import static montibelle.transformer.generic.Constants.INCR_CODE_EVENTAUT_TEMPLATE;
import static montibelle.transformer.generic.Constants.INCR_SIMULATOR_TEMPLATE;
import static montibelle.transformer.generic.Constants.ROOTS_TEMPLATE;
import static montibelle.transformer.generic.Constants.ROOT_TEMPLATE;

public class EventAutomaton {

  public static void transformEventAutomaton(
      Path target,
      MildComponentSymbol component,
      BundleSymbol input,
      BundleSymbol output,
      IExpressionPrinter expressionPrinter,
      ITypePrinter typePrinter,
      SessionGenerator sessionGenerator,
      Boolean comment) {

    Log.info("Transforming and printing " + component.getName(),
        EventAutomaton.class.getSimpleName());

    var automaton = component.getEventAutomaton();

    var variableDefinitionsList = automaton.getStateSpace().getVariablesSymbolList().stream()
        .map(it-> it.get())
      .map(it -> {
        var printer = new SymType2MCTypePrinter();
        ASTMCType mcType;
        try {
          mcType = FocusMill.parser().
              parse_StringMCType(printer.print(it.getType())).get();
        }
        catch (IOException e) {
          throw new RuntimeException(e);
        }
        return new ASTStateVariableBuilder()
            .setName(it.getName())
            .setPattern("var_" + it.getName())
            .setMCType(mcType)
            .build();
      }).collect(Collectors.toList());

    var astStateSpace = new ASTStateSpaceBuilder()
        .setName(automaton.getFullName() + ".States")
        .setStatesList(automaton.getStateSpace().getStatesList().stream().map(
                it -> new StateName(it.getBaseName()).toString()
            )
            .collect(Collectors.toList()))
        .setStateVariablesList(variableDefinitionsList)
        .uncheckedBuild();

    var initialConfig = automaton.getInitialConfigurationList().stream().map( it->
        transformConfiguration(it, expressionPrinter)
    ).collect(Collectors.toList());

    var eventTransitions = automaton.getEventTransitionsList().stream().map(
        astTransition ->
            new ASTEventTransitionBuilder()
                .setKey(SourceMap.mapToFocus(astTransition.getPortSymbol()))
                .setValueList(astTransition.getTransitionList().stream().map(transition ->
                    new ASTTransitionBuilder()
                        .setGuard(expressionPrinter.print(transition.getGuard()))
                        .setStart(new StateName(transition.getStart().getQName()).toString())
                        .setResult(transformConfiguration(transition.getResult(), expressionPrinter))
                        .setDocumentation(transition.getDocumentation())
                        .build()
                ).collect(Collectors.toList()))
                .build()
    ).collect(Collectors.toList());

    var astEventAutomaton = new ASTEventAutomatonBuilder()
        .setFqn(automaton.getFullName())
        .setInputBundle(input.getName())
        .setOutputBundle(output.getName())
        .setStrongCausal(component.isStrongCausal())
        .setParametersList(component.streamParameter().map(it -> {
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
                .collect(Collectors.toList())
        )
        .setStates(astStateSpace)
        .setInitialList(initialConfig)
        .setEventTransitionsList(eventTransitions)
        .setTickTransitionsList(automaton.streamTickTransitions().map(it ->
            new ASTTransitionBuilder()
                .setGuard(expressionPrinter.print(it.getGuard()))
                .setStart(new StateName(it.getStart().getQName()).toString())
                .setResult(transformConfiguration(it.getResult(), expressionPrinter))
                .setDocumentation(it.getDocumentation())
                .build()
        ).collect(Collectors.toList()))
        .uncheckedBuild();

    var result = Automaton.createTheoryFrom(astStateSpace);
    var stateTheory = result.getFirst();
    var stateSession = result.getSecond();

    var spsTheory = Sps.createTheory(astEventAutomaton, stateSession.getName());
    var ft = new FocusTool();
    ft.createSymbolTable(astEventAutomaton);
    ft.createSymbolTable(stateSession);
    ft.createSymbolTable(stateTheory);
    ft.createSymbolTable(spsTheory);
    ft.completeSymbolTable(astEventAutomaton);
    ft.completeSymbolTable(stateSession);
    ft.completeSymbolTable(stateTheory);
    ft.completeSymbolTable(spsTheory);

    if(astEventAutomaton.isFinite()) {
      stateSession.addExportFiles(
          new ExportFiles("export", 2, List.of("*:**scalaExec.scala")));
    }

    if(!spsTheory.isSubstituted()) {
      FreemarkerInterface.instance.generate(
          Constants.EVENT_AUTOMATON,
          target.resolve(
              stateSession.getPath().resolve(spsTheory.getFilename() + ".thy")
          ).toAbsolutePath(),
          comment,
          spsTheory,
          astEventAutomaton
      );

      sessionGenerator.add(spsTheory);
      sessionGenerator
          .addDependency(spsTheory,
              FocusMill.globalScope().resolveTheory("data_inc.Data_inc").get())
          .addDependency(spsTheory,
              FocusMill.globalScope().resolveTheory("user.Datatypes").get());
      if(!stateTheory.isSubstituted()) {
        sessionGenerator.addDependency(spsTheory, stateTheory);
      }
      sessionGenerator
          .addDependency(spsTheory, input.getTheorySymbol())
          .addDependency(spsTheory, output.getTheorySymbol());
    }

    if(!stateTheory.isSubstituted()) {
      FreemarkerInterface.instance.generate(
          Constants.STATES,
          target.resolve(
              stateSession.getPath().resolve(stateTheory.getFilename() + ".thy")
          ).toAbsolutePath(),
          comment,
          stateTheory,
          astStateSpace,
          Constants.instance
      );

      sessionGenerator.add(stateTheory);
    }

    Log.info("Finished transforming and printing " + component.getName(),
        EventAutomaton.class.getSimpleName());

    if(astEventAutomaton.isFinite()) {
      Log.info("Building and printing executable " + component.getName(),
          EventAutomaton.class.getSimpleName());

      var theoryIn = ft.buildCodeTheoryAndSessionFor(input);
      var inputTheory = theoryIn.getFirst();
      var codeBundleSession = theoryIn.getSecond();
      var outputTheory = ft.buildCodeTheoryAndSessionFor(output).getFirst();

      var astTheory = ft.buildCodeTheoryAndSessionFor(
          astEventAutomaton);
      var codeTheory = astTheory.getFirst();
      var codeSession = astTheory.getSecond();

      ft.createSymbolTable(codeBundleSession);
      ft.createSymbolTable(inputTheory);
      ft.createSymbolTable(outputTheory);
      if(!codeSession.getName().equals(codeBundleSession.getName())){
        ft.createSymbolTable(codeSession);
      }
      ft.createSymbolTable(codeTheory);
      ft.completeSymbolTable(codeBundleSession);
      ft.completeSymbolTable(inputTheory);
      ft.completeSymbolTable(outputTheory);
      ft.completeSymbolTable(astEventAutomaton);
      if(!codeSession.getName().equals(codeBundleSession.getName())) {
        ft.completeSymbolTable(codeSession);
      }
      ft.completeSymbolTable(codeTheory);

      TheoryGenerator.print(input, inputTheory, target, comment,
          INCR_CODE_BUNDLE_TEMPLATE);
      TheoryGenerator.print(output, outputTheory, target, comment,
          INCR_CODE_BUNDLE_TEMPLATE);
      TheoryGenerator.print(astEventAutomaton, codeTheory, target, comment,
          INCR_CODE_EVENTAUT_TEMPLATE);

      Log.info(
          "Manually building and printing sessions for executable " + component.getName(),
          EventAutomaton.class.getSimpleName());


      var dataInc = FocusMill.globalScope().resolveTheory(
          "data_inc.Data_inc").get();
      var datatypes = FocusMill.globalScope().resolveTheory(
          "user.Datatypes").get();
      SessionGenerator.Companion.addDependency(codeBundleSession, dataInc);
      SessionGenerator.Companion.addDependency(codeBundleSession, datatypes);

      if(codeSession.getName().equals(codeBundleSession.getName())) {
        Log.info("Just one session, integrating the executable automaton",
            EventAutomaton.class.getSimpleName());
        codeBundleSession.setParent("component");
        SessionGenerator.Companion.addDependency(codeBundleSession, spsTheory.getSymbol());
      }
      SessionGenerator.Companion.addDependency(codeBundleSession, input.getTheorySymbol());
      SessionGenerator.Companion.addDependency(codeBundleSession, output.getTheorySymbol());

      if(!codeSession.getName().equals(codeBundleSession.getName())){
        codeBundleSession.addTheory(
            new Theories(
                new TheoryEntry(inputTheory.getFilename()),
                new TheoryEntry(outputTheory.getFilename())
            )
        );
      }
      else {
        codeBundleSession.addTheory(
            new Theories(
                new TheoryEntry(codeTheory.getFilename()),
                new TheoryEntry(inputTheory.getFilename()),
                new TheoryEntry(outputTheory.getFilename())
            )
        );
      }

      for(String it: inputTheory.getPrologueSessions()){
        if(!codeBundleSession.getImportSessions().contains(it)){
          codeBundleSession.addImportSession(it);
        }
      }
      for(String it: outputTheory.getPrologueSessions()){
        if(!codeBundleSession.getImportSessions().contains(it)){
          codeBundleSession.addImportSession(it);
        }
      }
      if(!codeSession.getName().equals(codeBundleSession.getName())) {
        for(String it: codeTheory.getPrologueSessions()){
          if(!codeBundleSession.getImportSessions().contains(it)){
            codeBundleSession.addImportSession(it);
          }
        }
      }

      try {
        FreemarkerInterface.instance.generate(
            ROOT_TEMPLATE,
            target.resolve(codeBundleSession.getPath()).resolve(
                "ROOT").toAbsolutePath(),
            List.of(codeBundleSession)
        );
      }
      catch (Exception ex){
        Log.error(
            "Exception occurred while generating ROOT-files: " + ex.getMessage(), ex);
      }
      try {
        FreemarkerInterface.instance.generate(
            ROOTS_TEMPLATE,
            target.resolve(codeBundleSession.getPath()).resolve(
                "ROOTS").toAbsolutePath(),
            codeBundleSession.getImportSessions().stream()
                .map(it->
                    codeBundleSession.getEnclosingScope().resolveSession(it).get()
                )
                .map (it->
                    codeBundleSession.getPath().relativize(it.getPath())
                )
                .map (it->
                    it.toString().replace("\\", "/")
                )
                .sorted().collect(Collectors.toList())
        );
      }
      catch (Exception ex){
        Log.error(
            "Exception occurred while generating ROOTS-files: " + ex.getMessage(),
            ex);
      }

      if(!codeSession.getName().equals(codeBundleSession.getName())){
        Log.info(
            "Two sessions, one in ${codeBundleSession.path}, the other in " + codeSession.getPath(),
            EventAutomaton.class.getSimpleName());


        SessionGenerator.Companion.addDependency(codeSession, dataInc);
        SessionGenerator.Companion.addDependency(codeSession, datatypes);
        SessionGenerator.Companion.addDependency(codeSession, inputTheory.getSymbol());
        SessionGenerator.Companion.addDependency(codeSession, outputTheory.getSymbol());
        SessionGenerator.Companion.addDependency(codeSession, spsTheory.getSymbol());

        codeSession.addTheory(new Theories(
            new TheoryEntry(codeTheory.getFilename())
        ));

        for( String it: codeTheory.getPrologueSessions()){
          if(!codeSession.getImportSessions().contains(it)) codeSession.addImportSession(it);
        }

        try {
          FreemarkerInterface.instance.generate(
              ROOT_TEMPLATE,
              target.resolve(codeSession.getPath()).resolve("ROOT").toAbsolutePath(),
              List.of(codeSession)
          );
        }
        catch (Exception ex){
          Log.error(
              "Exception occurred while generating ROOT-files: " + ex.getMessage(),
              ex);
        }

        try {
          FreemarkerInterface.instance.generate(
              ROOTS_TEMPLATE,
              target.resolve(codeSession.getPath()).resolve(
                  "ROOTS").toAbsolutePath(),
              codeSession.getImportSessions().stream()
                  .map(it ->
                      codeSession.getEnclosingScope().resolveSession(it).get()
                  )
                  .map (it->
                      codeSession.getPath().relativize(it.getPath())
                  )
                  .map(it->
                      it.toString().replace("\\", "/")
                  )
                  .sorted().collect(Collectors.toList())
          );
        }
        catch (Exception ex){
          Log.error(
              "Exception occurred while generating ROOTS-files: " + ex.getMessage(),
              ex);
        }
      }

      var className = codeTheory.getFilename() + "Simulator";
      try {
        FreemarkerInterface.instance.generate(
            INCR_SIMULATOR_TEMPLATE,
            target.resolve(codeSession.getPath()).resolve("export")
                .resolve(className + ".scala").toAbsolutePath(),
            comment,
            className,
            codeTheory.getFilename(),
            astEventAutomaton);
      }
      catch (Exception ex){
        Log.error(
            "Exception occurred while generating the simulator " + className + ": "
                + ex.getMessage(), ex);
      }
    }

    Log.info("Finished transforming and printing executable " + component.getName(),
        EventAutomaton.class.getSimpleName());
  }

}
