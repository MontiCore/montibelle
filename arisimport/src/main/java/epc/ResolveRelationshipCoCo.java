package epc;

import de.se_rwth.commons.logging.Log;
import epc._ast.ASTIncoming;
import epc._cocos.EPCASTIncomingCoCo;

import static epc.ASTIncomingUtils.getSources;

public class ResolveRelationshipCoCo implements EPCASTIncomingCoCo {

  @Override
  public void check(ASTIncoming node) {
    var obj = getSources(node);

    if(obj.isEmpty()) {
      Log.error(String.format(
          "0x10126 Could not resolve object '%s'", node.getName()),
          node.get_SourcePositionStart(),
          node.get_SourcePositionEnd());
    }
    else if(obj.size() > 1) {
      Log.error(String.format(
          "0x10127 Could not uniquely resolve object '%s'", node.getName()),
          node.get_SourcePositionStart(),
          node.get_SourcePositionEnd());
    }
  }
}
