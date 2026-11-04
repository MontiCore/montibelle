package epc;

import de.se_rwth.commons.logging.Log;
import epc._ast.ASTObject;
import epc._ast.ASTOutgoing;
import epc._cocos.EPCASTObjectCoCo;
import epc._cocos.EPCASTOutgoingCoCo;

import java.util.stream.Collectors;

public class OutgoingCoCo implements EPCASTObjectCoCo {

  @Override
  public void check(ASTObject node) {
    var outs = node.getRelationshipList().stream()
        .filter(r -> r instanceof ASTOutgoing)
        .map(r -> (ASTOutgoing)r)
        .collect(Collectors.toList());
    var names = outs.stream()
        .map(ASTOutgoing::getName)
        .collect(Collectors.toSet());
    if(outs.size() !=  names.size()) {
      Log.error("0x10130 At least 2 Outgoings have the same name",
          node.get_SourcePositionStart(),
          node.get_SourcePositionEnd());
    }
  }

}
