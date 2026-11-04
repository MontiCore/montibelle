package focus;

import kotlin.Pair;
import montibelle.focus.FocusTool;
import montibelle.focus._ast.ASTRefinement;
import montibelle.focus._ast.ASTSession;
import montibelle.focus._ast.ASTSessionBuilder;
import montibelle.focus._ast.ASTTheory;
import montibelle.focus._ast.ASTTheoryBuilder;
import montibelle.focus._ast.ASTRefinementBuilder;
import montibelle.focus.FocusMill;
import montibelle.focus._symboltable.IFocusArtifactScope;
import montibelle.focus._symboltable.IFocusGlobalScope;
import montibelle.focus._symboltable.SpsSymbol;
import montibelle.transformer.generic.sessions.SessionGenerator;
import de.monticore.symbols.compsymbols._symboltable.ComponentTypeSymbol;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static montibelle.transformer.generic.Constants.REF_PRFX;
import static montibelle.transformer.generic.Constants.SEP;

public class Refinement {

  public static ASTSession createSession(ASTRefinement node) {
    var pathList = new ArrayList<String>();
    pathList.add(REF_PRFX);
    pathList.addAll(List.of(node.getRefinedName().split("\\.")));
    pathList.add(node.getRoughName().replace('.', SEP));

    var session = new ASTSessionBuilder()
        .setName(REF_PRFX +
            SEP +
            node.getRefinedName().replace('.',SEP) +
            SEP +
            "refines" +
            SEP +
            node.getRoughName().replace('.',SEP))
        .setPathList(pathList)
        .build();

    var eventBased = node.getRefined().getInput().getTiming().isEventBased();
    session.setParent(eventBased ? "eventcomponent" : "tscomponent");

    session.addGroup("refinement");

    return session;
  }

  public static ASTTheory createTheory(ASTRefinement node, String sessionName) {
    var theory = new ASTTheoryBuilder()
        .setSessionName(sessionName)
        .setFilename("ref_" + node.getRefinedName().replace('.',SEP) +
            "_rough_" + node.getRoughName().replace('.',SEP))
        .build();
    node.setTheory(theory.getName());
    return theory;
  }

  public static List<Pair<ComponentTypeSymbol, ComponentTypeSymbol>> findAllTransitiveRefinements(
      ComponentTypeSymbol roughGoal,
      ComponentTypeSymbol refStart) {
    List<List<Pair<ComponentTypeSymbol, ComponentTypeSymbol>>> allPaths = new ArrayList<>();
    Set<ComponentTypeSymbol> visited = new HashSet<>();
    List<Pair<ComponentTypeSymbol, ComponentTypeSymbol>> currentPath = new ArrayList<>();

    dfs(refStart, roughGoal, allPaths, visited, currentPath, refStart);

    return allPaths.stream().flatMap(List::stream).collect(Collectors.toList());
  }

  private static void dfs(ComponentTypeSymbol current, ComponentTypeSymbol roughGoal,
                          List<List<Pair<ComponentTypeSymbol, ComponentTypeSymbol>>> allPaths,
                          Set<ComponentTypeSymbol> visited, List<Pair<ComponentTypeSymbol,
          ComponentTypeSymbol>> currentPath, ComponentTypeSymbol refStart) {
    visited.add(current);
    if (!current.equals(refStart)) {
      ComponentTypeSymbol refined;
      if (currentPath.isEmpty()) {
        refined = refStart;
      } else {
        refined = currentPath.get(currentPath.size() - 1).getFirst();
      }
      currentPath.add(new Pair<>(current, refined));
    }

    if (current.equals(roughGoal)) {
      allPaths.add(new ArrayList<>(currentPath));
    } else {
      for (ComponentTypeSymbol neighbor : current.getRefinementsList().stream()
          .map(ref -> ref.getTypeInfo()).collect(Collectors.toList())) {
        if (!visited.contains(neighbor) &&
            !(current.equals(refStart) && neighbor.equals(roughGoal))) {
          dfs(neighbor, roughGoal, allPaths, visited, currentPath, refStart);
        }
      }
    }

    if (!currentPath.isEmpty()) {
      currentPath.remove(currentPath.size() - 1);
    }
    visited.remove(current);
  }

  public static Pair<ASTRefinement, ASTTheory> generateRefinement(
      ComponentTypeSymbol roughComp,
      ComponentTypeSymbol refinedComp,
      SessionGenerator sessionGenerator) {
    IFocusGlobalScope gs = FocusMill.globalScope();

    SpsSymbol rough = gs.resolveSps(roughComp.getFullName()).get();
    SpsSymbol refined = gs.resolveSps(refinedComp.getFullName()).get();

    ASTRefinement refAst = new ASTRefinementBuilder()
        .setName(rough.getName() + ".ref." + refined.getName())
        .setRoughName(rough.getName())
        .setRefinedName(refined.getName())
        .setTransitiveRefinementList(
            findAllTransitiveRefinements(roughComp, refinedComp).stream()
                .map(p -> p.getFirst().getName() + ".ref." + p.getSecond().getName())
                .collect(Collectors.toList()))
        .uncheckedBuild();

    var focusTool = new FocusTool();
    focusTool.createSymbolTable(refAst);

    ASTSession sess = createSession(refAst);
    focusTool.createSymbolTable(sess);
    ASTTheory th = createTheory(refAst, sess.getName());
    focusTool.createSymbolTable(th);

    focusTool.completeSymbolTable(refAst);
    focusTool.completeSymbolTable(sess);
    focusTool.completeSymbolTable(th);

    sessionGenerator.add(refAst.getTheoryDefinition());

    return new Pair<>(refAst, th);
  }
}
