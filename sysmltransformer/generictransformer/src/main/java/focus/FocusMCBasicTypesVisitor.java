package focus;

import de.monticore.types.mcbasictypes._ast.ASTMCPrimitiveType;
import de.monticore.types.mcbasictypes.types3.MCBasicTypesTypeVisitor;
import montibelle.focus._ast.ASTMCPrimitiveTypeWithNat;
import montibelle.focus._visitor.FocusVisitor2;

public class FocusMCBasicTypesVisitor extends MCBasicTypesTypeVisitor
    implements
    FocusVisitor2 {

  @Override
  public void endVisit(ASTMCPrimitiveTypeWithNat node) {
    endVisit((ASTMCPrimitiveType) node);
  }
}
