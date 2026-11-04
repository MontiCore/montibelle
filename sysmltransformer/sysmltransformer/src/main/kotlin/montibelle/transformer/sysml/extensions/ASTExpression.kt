package montibelle.transformer.sysml.extensions

import de.monticore.expressions.expressionsbasis._ast.ASTExpression
import de.monticore.lang.sysmlv2.SysMLv2Mill
import de.monticore.prettyprint.IndentPrinter
import montibelle.transformer.sysml.printer.CommonExpressions2Isabelle
import montibelle.transformer.sysml.printer.ExpressionsBasis2Isabelle
import montibelle.transformer.sysml.printer.MCCommonLiterals2Isabelle
import montibelle.transformer.sysml.printer.OCLExpressions2Isabelle
import montibelle.transformer.sysml.printer.SetExpressions2Isabelle
import montibelle.transformer.sysml.printer.StreamExpressions2Isabelle
import montibelle.transformer.sysml.printer.SysMLExpressions2Isabelle

fun ASTExpression.print(): String {
  val printer = IndentPrinter()
  val traverser = SysMLv2Mill.inheritanceTraverser()

  var commonExpressions = CommonExpressions2Isabelle(printer)
  commonExpressions.traverser = traverser
  traverser.setCommonExpressionsHandler(commonExpressions)
  traverser.add4CommonExpressions(commonExpressions)

  var mcCommonLiterals = MCCommonLiterals2Isabelle(printer)
  traverser.add4MCCommonLiterals(mcCommonLiterals)

  var expressionsBasis = ExpressionsBasis2Isabelle(printer)
  expressionsBasis.traverser = traverser
  traverser.setExpressionsBasisHandler(expressionsBasis)
  traverser.add4ExpressionsBasis(expressionsBasis)

  var oclExpressions = OCLExpressions2Isabelle(printer)
  oclExpressions.traverser = traverser
  traverser.add4OCLExpressions(oclExpressions)
  traverser.setOCLExpressionsHandler(oclExpressions)

  var setExpressions = SetExpressions2Isabelle(printer)
  setExpressions.traverser = traverser
  traverser.add4SetExpressions(setExpressions)
  traverser.setSetExpressionsHandler(setExpressions)

  var sysmlExpressions = SysMLExpressions2Isabelle(printer)
  sysmlExpressions.traverser = traverser
  traverser.add4SysMLExpressions(sysmlExpressions)
  traverser.setSysMLExpressionsHandler(sysmlExpressions)

  var streamExpressions = StreamExpressions2Isabelle(printer)
  streamExpressions.traverser = traverser
  traverser.add4StreamExpressions(streamExpressions)
  traverser.setStreamExpressionsHandler(streamExpressions)

  this.accept(traverser)

  return printer.content
}
