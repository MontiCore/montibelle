package epc;

import de.se_rwth.commons.logging.Log;
import epc._ast.ASTIncoming;
import epc._ast.ASTObject;
import epc._cocos.EPCASTIncomingCoCo;

import java.util.stream.Collectors;

import static epc.ASTIncomingUtils.getSiblingsWhoReferenceSameObject;
import static epc.ASTIncomingUtils.getSources;

public class MatchingPairsCoCo implements EPCASTIncomingCoCo {

  @Override
  public void check(ASTIncoming node) {
    var sources = getSources(node);
    if(sources.size() > 1) {
      var siblings = getSiblingsWhoReferenceSameObject(node);

      if (!siblings.isEmpty() && sources.size() != siblings.size() + 1) {
        Log.error("0x10122 Multiple incoming relationships share a name, " +
                "but the number of relationships does not match the " +
                "number of potential sources!",
            node.get_SourcePositionStart(),
            node.get_SourcePositionEnd());
      }
      else if(siblings.isEmpty()) {
        Log.error(
            String.format("0x10123 Found multiple potential sources for %s",
                node.getName()),
            node.get_SourcePositionStart(),
            node.get_SourcePositionEnd());
      }
    }
    else if (sources.size() == 0) {
      Log.error(
          String.format("Found no potential sources for %s", node.getName()),
          node.get_SourcePositionStart(), node.get_SourcePositionEnd());
    }
  }

}
