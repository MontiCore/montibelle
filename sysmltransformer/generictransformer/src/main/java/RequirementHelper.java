import montibelle.focus.FocusTool;
import montibelle.focus._ast.ASTRequirement;
import montibelle.focus._ast.ASTSession;
import montibelle.focus._ast.ASTSessionBuilder;
import montibelle.focus._ast.ASTTheory;
import montibelle.focus._ast.ASTTheoryBuilder;

import java.util.Arrays;

import static montibelle.transformer.generic.Constants.REQ_PRFX;
import static montibelle.transformer.generic.Constants.SEP;

public class RequirementHelper {

  public static ASTSession createSession(ASTRequirement node) {
    String sessionName = node.getName().startsWith(REQ_PRFX + SEP)
        ? node.getName()
        : REQ_PRFX + SEP + node.getName();
    var session = new ASTSessionBuilder()
        .setName(sessionName)
        .setPathList(Arrays.asList(REQ_PRFX))
        .build();

    session.setParent("component");
    session.addGroup("requirement");

    return session;
  }

  public static ASTTheory createTheory(ASTRequirement node, ASTSession session) {
    var theory = new ASTTheoryBuilder()
        .setFilename(node.getName())
        .setSessionName(session.getName())
        .build();
    node.setTheory(theory.getName());

    return theory;
  }

  public static void buildSymbolTable(ASTRequirement req, ASTSession session, ASTTheory theory) {
    var tool = new FocusTool();
    tool.createSymbolTable(session);
    tool.createSymbolTable(theory);
    tool.createSymbolTable(req);
    tool.completeSymbolTable(session);
    tool.completeSymbolTable(theory);
    tool.completeSymbolTable(req);
  }

}
