package montibelle.transformer.sysml.printer

import de.monticore.literals.mccommonliterals._ast.ASTBooleanLiteral
import de.monticore.literals.mccommonliterals._ast.ASTNatLiteral
import de.monticore.literals.mccommonliterals._ast.ASTStringLiteral
import de.monticore.literals.mccommonliterals._visitor.MCCommonLiteralsVisitor2
import de.monticore.prettyprint.IndentPrinter

class MCCommonLiterals2Isabelle(val printer: IndentPrinter) :  MCCommonLiteralsVisitor2 {

  override fun visit(node: ASTBooleanLiteral) {
    printer.print(if (node.value) "True" else "False")
  }

  override fun visit(node: ASTNatLiteral) {
    printer.print(node.value)
  }

  override fun visit(node: ASTStringLiteral) {
    printer.print("''${node.source}''")
  }

}
