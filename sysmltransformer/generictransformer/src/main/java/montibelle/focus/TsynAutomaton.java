package montibelle.focus;

import de.monticore.lang.componentconnector._symboltable.MildComponentSymbol;
import de.monticore.types.mcbasictypes._ast.ASTMCType;
import de.se_rwth.commons.logging.Log;
import focus.Sps;
import focus.StateName;
import focus.SymType2MCTypePrinter;
import kotlin.Pair;
import montibelle.focus._ast.ASTAutomaton;
import montibelle.focus._ast.ASTAutomatonBuilder;
import montibelle.focus._ast.ASTConfiguration;
import montibelle.focus._ast.ASTParameterBuilder;
import montibelle.focus._ast.ASTSession;
import montibelle.focus._ast.ASTStateSpace;
import montibelle.focus._ast.ASTStateSpaceBuilder;
import montibelle.focus._ast.ASTStateVariable;
import montibelle.focus._ast.ASTStateVariableBuilder;
import montibelle.focus._ast.ASTTheory;
import montibelle.focus._ast.ASTTransition;
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

import java.io.IOException;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class TsynAutomaton {

  public static void transformTSynAutomaton(
      Path target,
      MildComponentSymbol component,
      BundleSymbol input,
      BundleSymbol output,
      IExpressionPrinter expressionPrinter,
      ITypePrinter typePrinter,
      SessionGenerator sessionGenerator,
      boolean comment) {

    Log.info("Transforming and printing " + component.getName(),
        Transformer.class.getSimpleName());

    var automaton = component.getAutomaton();

    List<ASTStateVariable> variableDefinitionsList = automaton.getStateSpace().getVariablesSymbolList().stream()
        .map(opt -> opt.get())
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

    ASTStateSpace astStateSpace = new ASTStateSpaceBuilder()
        .setName(automaton.getFullName() + ".States")
        .setStatesList(
            automaton.getStateSpace().getStatesList().stream()
                .map(state -> new StateName(state.getBaseName()).toString())
                .collect(Collectors.toList())
        )
        .setStateVariablesList(variableDefinitionsList)
        .uncheckedBuild();

    List<ASTConfiguration> initialConfig = automaton.getInitialConfigurationList().stream()
        .map(it -> ASTConfiguration.transformConfiguration(it,
            expressionPrinter))
        .collect(Collectors.toList());

    List<ASTTransition> transitions = automaton.getTransitionsList().stream()
        .map(it -> new ASTTransitionBuilder()
            .setGuard(expressionPrinter.print(it.getGuard()))
            .setStart(new StateName(it.getStart().getQName()).toString())
            .setResult(ASTConfiguration.transformConfiguration(it.getResult(),
                expressionPrinter))
            .setDocumentation(it.getDocumentation())
            .build())
        .collect(Collectors.toList());

    ASTAutomaton astAutomaton = new ASTAutomatonBuilder()
        .setFqn(automaton.getFullName())
        .setInputBundle(input.getName())
        .setOutputBundle(output.getName())
        .setStrongCausal(component.isStrongCausal())
        .setParametersList(component.getParameterList().stream()
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
            .collect(Collectors.toList()))
        .setStates(astStateSpace)
        .setInitialList(initialConfig)
        .setTransitionsList(transitions)
        .setFinite(true)
        .uncheckedBuild();

    FocusTool focusTool = new FocusTool();
    focusTool.createSymbolTable(astAutomaton);

    var stateTheorySessionPair = Automaton.createTheoryFrom(astStateSpace);
    ASTTheory stateTheory = stateTheorySessionPair.getFirst();
    ASTSession stateSession = stateTheorySessionPair.getSecond();

    stateSession.addImportSession("expressions");
    ASTTheory spsTheory = Sps.createTheory(astAutomaton,
        stateSession.getName());

    if(astAutomaton.isFinite()) {
      stateSession.addExportFiles(
          new ExportFiles("export", 2, List.of("*:**scalaExec.scala")));
    }

    focusTool.createSymbolTable(stateSession);
    focusTool.createSymbolTable(stateTheory);
    focusTool.createSymbolTable(spsTheory);
    focusTool.completeSymbolTable(astAutomaton);
    focusTool.completeSymbolTable(stateSession);
    focusTool.completeSymbolTable(stateTheory);
    focusTool.completeSymbolTable(spsTheory);

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
    }

    if(!spsTheory.isSubstituted()) {
      FreemarkerInterface.instance.generate(
          Constants.TSYN_AUT,
          target.resolve(
              stateSession.getPath().resolve(spsTheory.getFilename() + ".thy")
          ).toAbsolutePath(),
          comment,
          spsTheory,
          astAutomaton
      );
    }

    sessionGenerator.addAll(Arrays.asList(spsTheory, stateTheory));
    sessionGenerator.addDependency(spsTheory, stateTheory);
    sessionGenerator.addDependency(spsTheory, input.getTheorySymbol());
    sessionGenerator.addDependency(spsTheory, output.getTheorySymbol());

    Log.info("Finished transforming and printing " + component.getName(),
        Transformer.class.getSimpleName());

    if(astAutomaton.isFinite()) {
      Log.info("Building and printing executable " + component.getName(),
          Transformer.class.getSimpleName());

      Pair<ASTTheory, ASTSession> inputCodePair = focusTool.buildCodeTheoryAndSessionFor(
          input);
      ASTTheory inputTheory = inputCodePair.getFirst();
      ASTSession codeBundleSession = inputCodePair.getSecond();

      Pair<ASTTheory, ASTSession> outputCodePair = focusTool.buildCodeTheoryAndSessionFor(
          output);
      ASTTheory outputTheory = outputCodePair.getFirst();

      Pair<ASTTheory, ASTSession> codeAutPair = focusTool.buildCodeTheoryAndSessionFor(
          astAutomaton);
      ASTTheory codeTheory = codeAutPair.getFirst();
      ASTSession codeSession = codeAutPair.getSecond();

      focusTool.createSymbolTable(codeBundleSession);
      focusTool.createSymbolTable(inputTheory);
      focusTool.createSymbolTable(outputTheory);
      if(!codeSession.getName().equals(codeBundleSession.getName())) {
        focusTool.createSymbolTable(codeSession);
      }
      focusTool.createSymbolTable(codeTheory);
      focusTool.completeSymbolTable(codeBundleSession);
      focusTool.completeSymbolTable(inputTheory);
      focusTool.completeSymbolTable(outputTheory);
      focusTool.completeSymbolTable(astAutomaton);
      if(!codeSession.getName().equals(codeBundleSession.getName())) {
        focusTool.completeSymbolTable(codeSession);
      }
      focusTool.completeSymbolTable(codeTheory);

      TheoryGenerator.print(input, inputTheory, target, comment,
          Constants.INCR_CODE_BUNDLE_TEMPLATE);
      TheoryGenerator.print(output, outputTheory, target, comment,
          Constants.INCR_CODE_BUNDLE_TEMPLATE);
      TheoryGenerator.print(astAutomaton, codeTheory, target, comment,
          Constants.INCR_CODE_TSYNAUT_TEMPLATE);

      Log.info("Manually building and printing sessions for executable "
          + component.getName(), Transformer.class.getSimpleName());


      var dataInc = FocusMill.globalScope().resolveTheory(
          "data_inc.Data_inc").get();
      var datatypes = FocusMill.globalScope().resolveTheory(
          "user.Datatypes").get();
      SessionGenerator.Companion.addDependency(codeBundleSession, dataInc);
      SessionGenerator.Companion.addDependency(codeBundleSession, datatypes);

      if(codeSession.getName().equals(codeBundleSession.getName())) {
        Log.info("Just one session, integrating the executable automaton",
            Transformer.class.getSimpleName());
        codeBundleSession.setParent("component");
        SessionGenerator.Companion.addDependency(codeBundleSession,
            spsTheory.getSymbol());
      }
      SessionGenerator.Companion.addDependency(codeBundleSession,
          input.getTheorySymbol());
      SessionGenerator.Companion.addDependency(codeBundleSession,
          output.getTheorySymbol());

      if(!codeSession.getName().equals(codeBundleSession.getName())) {
        codeBundleSession.addTheory(
            new Theories(
                new TheoryEntry(inputTheory.getFilename()),
                new TheoryEntry(outputTheory.getFilename())
            )
        );
      }
      else {
        codeBundleSession.addTheory(new Theories(
            new TheoryEntry(codeTheory.getFilename()),
            new TheoryEntry(inputTheory.getFilename()),
            new TheoryEntry(outputTheory.getFilename())
        ));
      }

      for (String session : inputTheory.getPrologueSessions()) {
        if(!codeBundleSession.getImportSessions().contains(session)) {
          codeBundleSession.addImportSession(session);
        }
      }
      for (String session : outputTheory.getPrologueSessions()) {
        if(!codeBundleSession.getImportSessions().contains(session)) {
          codeBundleSession.addImportSession(session);
        }
      }
      if(codeSession.getName().equals(codeBundleSession.getName())) {
        for (String session : codeTheory.getPrologueSessions()) {
          if(!codeBundleSession.getImportSessions().contains(session)) {
            codeBundleSession.addImportSession(session);
          }
        }
      }

      try {
        FreemarkerInterface.instance.generate(
            Constants.ROOT_TEMPLATE,
            target.resolve(codeBundleSession.getPath()).resolve(
                "ROOT").toAbsolutePath(),
            Arrays.asList(codeBundleSession)
        );
      }
      catch (Exception ex) {
        Log.error("Exception occurred while generating ROOT-files: "
            + ex.getMessage(), ex);
      }
      try {
        FreemarkerInterface.instance.generate(
            Constants.ROOTS_TEMPLATE,
            target.resolve(codeBundleSession.getPath()).resolve(
                "ROOTS").toAbsolutePath(),
            codeBundleSession.getImportSessions().stream()
                .map(s -> codeBundleSession.getEnclosingScope().resolveSession(
                    s).get())
                .map(s -> codeBundleSession.getPath().relativize(s.getPath()))
                .map(p -> p.toString().replace("\\", "/"))
                .sorted()
                .collect(Collectors.toList())
        );
      }
      catch (Exception ex) {
        Log.error("Exception occurred while generating ROOTS-files: "
            + ex.getMessage(), ex);
      }

      if(!codeSession.getName().equals(codeBundleSession.getName())) {
        Log.info("Two sessions, one in " + codeBundleSession.getPath()
                + ", the other in " + codeSession.getPath(),
            Transformer.class.getSimpleName());
        SessionGenerator.Companion.addDependency(codeSession, dataInc);
        SessionGenerator.Companion.addDependency(codeSession, datatypes);
        SessionGenerator.Companion.addDependency(codeSession,
            inputTheory.getSymbol());
        SessionGenerator.Companion.addDependency(codeSession,
            outputTheory.getSymbol());
        SessionGenerator.Companion.addDependency(codeSession,
            spsTheory.getSymbol());

        codeSession.addTheory(new Theories(
            new TheoryEntry(codeTheory.getFilename())
        ));

        for (String session : codeTheory.getPrologueSessions()) {
          if(!codeSession.getImportSessions().contains(session)) {
            codeSession.addImportSession(session);
          }
        }

        try {
          FreemarkerInterface.instance.generate(
              Constants.ROOT_TEMPLATE,
              target.resolve(codeSession.getPath()).resolve(
                  "ROOT").toAbsolutePath(),
              Arrays.asList(codeSession)
          );
        }
        catch (Exception ex) {
          Log.error("Exception occurred while generating ROOT-files: "
              + ex.getMessage(), ex);
        }

        try {
          FreemarkerInterface.instance.generate(
              Constants.ROOTS_TEMPLATE,
              target.resolve(codeSession.getPath()).resolve(
                  "ROOTS").toAbsolutePath(),
              codeSession.getImportSessions().stream()
                  .map(s -> codeSession.getEnclosingScope().resolveSession(
                      s).get())
                  .map(s -> codeSession.getPath().relativize(s.getPath()))
                  .map(p -> p.toString().replace("\\", "/"))
                  .sorted()
                  .collect(Collectors.toList())
          );
        }
        catch (Exception ex) {
          Log.error("Exception occurred while generating ROOTS-files: "
              + ex.getMessage(), ex);
        }
      }

      String className = codeTheory.getFilename() + "Simulator";
      try {
        FreemarkerInterface.instance.generate(
            Constants.INCR_SIMULATOR_TEMPLATE,
            target.resolve(codeSession.getPath()).resolve("export")
                .resolve(className + ".scala").toAbsolutePath(),
            comment,
            className,
            codeTheory.getFilename(),
            astAutomaton
        );
      }
      catch (Exception ex) {
        Log.error(
            "Exception occurred while generating the simulator " + className
                + ": " + ex.getMessage(), ex);
      }
    }

    Log.info(
        "Finished transforming and printing executable " + component.getName(),
        Transformer.class.getSimpleName());
  }
}
