package montibelle.focus;

import kotlin.Pair;
import montibelle.focus._ast.ASTSession;
import montibelle.focus._ast.ASTSessionBuilder;
import montibelle.focus._ast.ASTStateSpace;
import montibelle.focus._ast.ASTTheory;
import montibelle.focus._ast.ASTTheoryBuilder;
import montibelle.transformer.generic.Constants;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public final class Automaton {

  private Automaton() {
  }

  public static Pair<ASTTheory, ASTSession> createTheoryFrom(ASTStateSpace node) {

    String packageJoined = node.getPackage().stream()
        .collect(Collectors.joining(String.valueOf(Constants.SEP)));

    String sessionName = Constants.SPS_PRFX + Constants.SEP + packageJoined;

    List<String> pathList = new ArrayList<>();
    pathList.add(Constants.SPS_PRFX);
    pathList.addAll(node.getPackage());

    ASTSession session = new ASTSessionBuilder()
        .setName(sessionName)
        .setPathList(pathList)
        .build();

    session.addGroup("system");
    session.setParent("component");

    String filename = "def_" + node.getName().replace('.', Constants.SEP);

    ASTTheory theory = new ASTTheoryBuilder()
        .setSessionName(session.getName())
        .setFilename(filename)
        .build();

    node.setTheory(theory.getName());

    return new Pair<>(theory, session);
  }
}
