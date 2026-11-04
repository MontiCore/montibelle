package montibelle.focus;


import montibelle.focus._ast.ASTDatatypes;
import montibelle.focus._ast.ASTSession;
import montibelle.focus._ast.ASTSessionBuilder;
import montibelle.focus._ast.ASTTheory;
import montibelle.focus._ast.ASTTheoryBuilder;
import kotlin.Pair;
import java.util.List;

public final class Datatypes {

  private Datatypes() {
  }

  public static Pair<ASTTheory, ASTSession> createTheoryFrom(ASTDatatypes node) {
    ASTSession session = new ASTSessionBuilder()
        .setName("user")
        .setPathList(List.of("user"))
        .build();

    session.setParent("inc");
    session.addGroup("system");

    ASTTheory theory = new ASTTheoryBuilder()
        .setSessionName(session.getName())
        .setFilename("Datatypes")
        .build();

    node.setTheory(theory.getName());

    return new Pair<>(theory, session);
  }

  public static ASTTheory createTheoryFrom(String filename, ASTTheory parent) {
    ASTTheory theory = new ASTTheoryBuilder()
      .setSessionName(parent.getSessionName())
      .setFilename(filename)
      .build();
    theory.setEnclosingScope(parent.getEnclosingScope());

    return theory;
  }
}

