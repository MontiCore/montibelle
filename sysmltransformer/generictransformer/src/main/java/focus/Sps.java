package focus;

import cc2focus.Specification2Sps;
import de.monticore.lang.componentconnector._symboltable.MildComponentSymbol;
import de.monticore.types.mcbasictypes._ast.ASTMCType;
import montibelle.focus.FocusMill;
import montibelle.focus.FocusTool;
import montibelle.focus._ast.ASTAutomaton;
import montibelle.focus._ast.ASTInstance;
import montibelle.focus._ast.ASTParameter;
import montibelle.focus._ast.ASTParameterBuilder;
import montibelle.focus._ast.ASTSession;
import montibelle.focus._ast.ASTSessionBuilder;
import montibelle.focus._ast.ASTSpecification;
import montibelle.focus._ast.ASTSpecificationBuilder;
import montibelle.focus._ast.ASTSps;
import montibelle.focus._ast.ASTTheory;
import montibelle.focus._ast.ASTTheoryBuilder;
import montibelle.focus._symboltable.BundleSymbol;
import montibelle.transformer.generic.Constants;
import montibelle.transformer.generic.sessions.SessionGenerator;
import montibelle.transformer.util.FreemarkerInterface;
import trafos.IExpressionPrinter;
import trafos.ITypePrinter;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

import static montibelle.transformer.generic.Constants.SEP;
import static montibelle.transformer.generic.Constants.SPS_PRFX;

public class Sps {

  public static ASTSession createSession(ASTSps node) {
    var pathList = new ArrayList<String>();
    pathList.add(SPS_PRFX);
    pathList.addAll(node.getPackage());
    pathList.add(node.getName());

    var session = new ASTSessionBuilder()
        .setName(SPS_PRFX + SEP + node.getIdentifier().replace(".", "_"))
        .setPathList(pathList)
        .build();

    if(node instanceof ASTAutomaton) {
      var eventBased = node.getInputBundleSymbol().getTiming().isEventBased();
      session.setParent(eventBased ? "eventcomponent" : "tscomponent");
    }
    else if(node instanceof ASTInstance) {
      var eventBased = node.getInputBundleSymbol().getTiming().isEventBased();
      session.setParent(eventBased ? "eventcomponent" : "tscomponent");
    }
    else {
      session.setParent("component");
    }
    session.addGroup("system");

    return session;
  }

  public static ASTTheory createTheory(ASTSps node, String sessionName) {
    var theory = new ASTTheoryBuilder()
        .setSessionName(sessionName)
        .setFilename("def_" + node.getFqn().replace('.', SEP))
        .build();
    node.setTheory(theory.getName());
    return theory;
  }

  public static void transformSpec(Path target,
                                   MildComponentSymbol component,
                                   BundleSymbol input,
                                   BundleSymbol output,
                                   IExpressionPrinter expressionPrinter,
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

    ASTSpecificationBuilder specBuilder = new ASTSpecificationBuilder();

    if (component.isHistoryBased()) {
      specBuilder = Specification2Sps
          .buildSpecificaton(component.getSpecification(), expressionPrinter)
          .setInputBundle(input.getName())
          .setOutputBundle(output.getName())
          .setFqn(component.getFullName())
          .setStrongCausal(component.isStrongCausal())
          .setParametersList(params);
    } else {
      specBuilder = specBuilder
          .setInputBundle(input.getName())
          .setOutputBundle(output.getName())
          .setFqn(component.getFullName())
          .setStrongCausal(component.isStrongCausal())
          .setParametersList(params);
    }

    FocusTool focusTool = new FocusTool();
    ASTSpecification spec = specBuilder.build();
    focusTool.createSymbolTable(spec);
    ASTSession sess = createSession(spec);
    focusTool.createSymbolTable(sess);
    ASTTheory th = createTheory(spec, sess.getName());
    focusTool.createSymbolTable(th);

    focusTool.completeSymbolTable(spec);
    focusTool.completeSymbolTable(sess);
    focusTool.completeSymbolTable(th);

    if (!th.isSubstituted()) {
      FreemarkerInterface.instance.generate(
          Constants.SPEC,
          target.resolve(th.getSession().getPath().resolve(th.getFilename() + ".thy"))
              .toAbsolutePath(),
          comment,
          th,
          spec
      );
      sessionGenerator
          .add(th)
          .addDependency(th, FocusMill.globalScope().resolveTheory("data_inc.Data_inc").get())
          .addDependency(th, FocusMill.globalScope().resolveTheory("user.Datatypes").get())
          .addDependency(th, input.getTheorySymbol())
          .addDependency(th, output.getTheorySymbol());
    }
  }
}
