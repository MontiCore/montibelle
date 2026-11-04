package epc;

import de.se_rwth.commons.logging.Log;
import de.se_rwth.commons.logging.LogStub;
import epc._ast.ASTIncoming;
import epc._ast.ASTOutgoing;

import java.nio.file.Path;
import java.util.stream.Collectors;

import static epc.ASTIncomingUtils.*;

public class Untangler {

  public static void untangle(EPCTool tool, Path in, Path out) {
    var ast = tool.parse(in.toAbsolutePath().toString());
    tool.createSymbolTable(ast);

    for(var diagram: ast.getDiagramList()) {
      var objects = diagram.getObjects().getObjectList();

      var incomings = objects.stream()
          .flatMap(o -> o.getRelationshipList().stream())
          .filter(r -> r instanceof ASTIncoming)
          .map(r -> (ASTIncoming)r)
          .collect(Collectors.toList());
      for(var incoming: incomings) {
        var duplicateSources = getSources(incoming);
        if(duplicateSources.size() > 1) {
          var incomingsFromDuplicateSources = incomings.stream()
              .filter(i -> getSources(i).equals(duplicateSources))
              .collect(Collectors.toList());

          var austauschbareSources = duplicateSources.stream()
              .allMatch(o -> o.getRelationshipList().size() == 1);

          var currentObj = incoming.getEnclosingScope().getAstNode();
          var sameTarget = incomingsFromDuplicateSources.stream()
              .map(inc -> inc.getEnclosingScope().getAstNode())
              .allMatch(obj -> obj.equals(currentObj));

          if(austauschbareSources || sameTarget) {
            if(incomingsFromDuplicateSources.size() != duplicateSources.size()) {
              Log.error("0x10128 Could not untangle successfully",
                  incoming.get_SourcePositionStart(),
                  incoming.get_SourcePositionEnd());
              continue;
            }
            for(var i = 0; i < duplicateSources.size(); i++) {
              var object = duplicateSources.get(i);

              if(!austauschbareSources) {

                var objectsPointingToCurr = object.getRelationshipList()
                    .stream()
                    .filter(r -> r instanceof ASTIncoming)
                    .map(r -> (ASTIncoming)r)
                    .flatMap(inc -> getSources(inc).stream())
                    .collect(Collectors.toList());
                var outgoingsPointingToCurr = objectsPointingToCurr.stream()
                    .flatMap(o -> o.getRelationshipList().stream())
                    .filter(r -> r instanceof ASTOutgoing)
                    .map(r -> (ASTOutgoing)r)
                    .filter(o -> o.getName().equals(object.getName()))
                    .collect(Collectors.toList());


                var toChange = object.getRelationshipList().stream()
                    .flatMap(r -> getCounterparts(r).stream())
                    .filter(r -> !incomingsFromDuplicateSources.contains(r) &&
                        !incomingsFromDuplicateSources.stream()
                            .flatMap(c -> getCounterparts(c).stream())
                            .collect(Collectors.toList())
                            .contains(r)
                    )
                    .collect(Collectors.toList());

                for(var relation: toChange) {
                  relation.setName(object.getName() + "%FF" + i);
                }
              }

              object.setName(object.getName() + "%FF" + i);
            }
            for(var i = 0; i < incomingsFromDuplicateSources.size(); i++) {
              var incoming1 = incomingsFromDuplicateSources.get(i);
              incoming1.setName(incoming1.getName() + "%FF" + i);
            }
          }
        }
      }
    }

    tool.prettyPrint(ast, out.toAbsolutePath().toString());
  }

}
