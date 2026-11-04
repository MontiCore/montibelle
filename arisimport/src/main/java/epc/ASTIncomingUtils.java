package epc;

import de.se_rwth.commons.logging.Log;
import epc._ast.ASTIncoming;
import epc._ast.ASTObject;
import epc._ast.ASTOutgoing;
import epc._ast.ASTRelationship;
import epc._symboltable.ObjectSymbol;

import java.util.List;
import java.util.function.BiPredicate;
import java.util.function.Predicate;
import java.util.stream.Collectors;

public class ASTIncomingUtils {

  public static ASTObject getSource(ASTIncoming node) {
    var sources = getSources(node);
    if(sources.size() > 1) {
      Log.error(String.format(
          "0x10121 Found multiple potential sources for %s", node.getName()),
          node.get_SourcePositionStart(), node.get_SourcePositionEnd());
    }
    else if(sources.size() == 0) {
      Log.error(String.format(
          "0x10131 Found no potential sources for %s", node.getName()),
          node.get_SourcePositionStart(), node.get_SourcePositionEnd());
    }
    return sources.get(0);
  }

  public static List<ASTObject> getSources(ASTIncoming node) {
    var scope = node.getEnclosingScope();
    var targetName = scope.getName();
    var sourceName = node.getName();

    BiPredicate<ObjectSymbol, String> pointsBackAndTypeMatches =
        (objectSymbol, type) -> {
          var source = objectSymbol.getAstNode();
          var matchingOut = source.getRelationshipList().stream()
              .filter(r -> r instanceof ASTOutgoing)
              .filter(r -> r.getName().equals(targetName));
          return matchingOut.count() > 0 && source.getType().equals(type);
        };

    var sources = scope.resolveObjectMany(sourceName);

    return sources.stream()
        .filter(objSym -> pointsBackAndTypeMatches.test(objSym, node.getType()))
        .map(objSym -> objSym.getAstNode())
        .collect(Collectors.toList());
  }

  public static List<ASTIncoming> getSiblingsWhoReferenceSameObject(ASTIncoming node) {
    var object = (ASTObject) node.getEnclosingScope().getAstNode();
    return object.getRelationshipList().stream()
        .filter(r -> r instanceof ASTIncoming)
        .map(r -> (ASTIncoming) r)
        .filter(r -> r.getName().equals(node.getName()))
        .filter(r -> r.getType().equals(node.getType()))
        .filter(r -> r != node)
        .collect(Collectors.toList());
  }

  public static List<ASTRelationship> getCounterparts(ASTRelationship node) {
    var scope = node.getEnclosingScope();
    var thisEndName = ((ASTObject)scope.getAstNode()).getName();
    var thisEndType = ((ASTObject)scope.getAstNode()).getType();
    var otherEndName = node.getName();

    Predicate<ASTRelationship> isOppositeToNode =
        astRelationship -> {
          if(node instanceof ASTIncoming) {
            return astRelationship instanceof ASTOutgoing;
          }
          else if (node instanceof ASTOutgoing) {
            return astRelationship instanceof ASTIncoming;
          }
          else {
            Log.warn(String.format("0x10132 Can't get opposite of %s",
                node.getClass().getName()),
                node.get_SourcePositionStart(),
                node.get_SourcePositionEnd());
            return false;
          }
        };

    return scope.resolveObjectMany(otherEndName).stream()
        .filter(obj -> obj.getAstNode().getType().equals(node.getType()))
        .flatMap(obj -> obj.getAstNode().getRelationshipList().stream())
        .filter(r -> isOppositeToNode.test(r)
            && r.getName().equals(thisEndName)
            && r.getType().equals(thisEndType))
        .collect(Collectors.toList());
  }

}
