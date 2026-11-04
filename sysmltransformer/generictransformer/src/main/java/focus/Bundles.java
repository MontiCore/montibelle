package focus;

import de.se_rwth.commons.logging.Log;
import montibelle.focus.FocusMill;
import montibelle.focus.FocusTool;
import montibelle.focus._ast.ASTBundle;
import montibelle.focus._ast.ASTSession;
import montibelle.focus._ast.ASTSessionBuilder;
import montibelle.focus._ast.ASTTheory;
import montibelle.focus._ast.ASTTheoryBuilder;
import montibelle.transformer.generic.Constants;
import montibelle.transformer.generic.sessions.SessionGenerator;
import montibelle.transformer.util.FreemarkerInterface;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;

public class Bundles {

  public static ASTSession createSession(ASTBundle node) {
    var pathList = new ArrayList<String>();
    pathList.add(Constants.BNDL_PRFX);
    pathList.addAll(node.getPackage());

    var session = new ASTSessionBuilder()
        .setName(Constants.BNDL_PRFX + Constants.SEP + String.join("" + Constants.SEP, node.getPackage()))
        .setPathList(pathList)
        .build();

    session.setParent("sps");
    session.addGroup("system");

    return session;
  }

  public static ASTTheory createTheory(ASTBundle node, String sessionName) {
    var theory = new ASTTheoryBuilder()
        .setSessionName(sessionName)
        .setFilename("def_" + node.getName().replace('.', Constants.SEP))
        .build();

    node.setTheory(theory.getName());

    return theory;
  }

  public static ASTBundle transformBundles(
      String bundleModel,
      Path target,
      SessionGenerator sessionGenerator,
      boolean comment
  ) {
    ASTBundle astBundle = null;
    try {
      astBundle = FocusMill.parser().parse_StringBundle(bundleModel).get();
    }
    catch (IOException e) {
      Log.error("0xFF125 TODO");
    }
    var tool = new FocusTool();
    tool.createSymbolTable(astBundle);

    ASTSession inSession = createSession(astBundle);
    ASTTheory inTheory = createTheory(astBundle, inSession.getName());

    tool.createSymbolTable(inTheory);
    tool.completeSymbolTable(astBundle);
    tool.completeSymbolTable(inTheory);

    var existingSession = FocusMill.globalScope().resolveSession(inSession.getName());
    if (existingSession.isEmpty()) {
      tool.createSymbolTable(inSession);
      tool.completeSymbolTable(inSession);
    } else if (!existingSession.get().isPresentAstNode()) {
      var sessionSymbol = existingSession.get();
      inSession.setSymbol(sessionSymbol);
      inSession.setEnclosingScope(sessionSymbol.getEnclosingScope());
      sessionSymbol.setAstNode(inSession);
    }

    if (!inTheory.isSubstituted()) {
      FreemarkerInterface.instance.generate(
          Constants.BUNDLE_DEF,
          target.resolve(inSession.getPath().resolve(inTheory.getFilename() + ".thy")).toAbsolutePath(),
          comment,
          inTheory,
          astBundle
      );
      sessionGenerator
          .addDependency(inTheory, FocusMill.globalScope().resolveTheory("data_inc.Data_inc").get())
          .addDependency(inTheory, FocusMill.globalScope().resolveTheory("user.Datatypes").get());
    }

    sessionGenerator.add(astBundle.getTheoryDefinition());

    return astBundle;
  }
}
