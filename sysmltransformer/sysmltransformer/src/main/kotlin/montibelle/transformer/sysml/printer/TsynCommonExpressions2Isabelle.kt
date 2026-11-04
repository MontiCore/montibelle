package montibelle.transformer.sysml.printer

import de.monticore.expressions.commonexpressions._ast.*
import de.monticore.lang.sysmlv2.SysMLv2Mill
import de.monticore.prettyprint.IndentPrinter
import montibelle.transformer.sysml.Constants.SEP

open class TsynCommonExpressions2Isabelle(printer: IndentPrinter, settings: IsabellePrinterSettings) : CommonExpressions2Isabelle(printer, settings) {

  protected open fun mapToIsabelleTsyn(fqn: String): String? = when (fqn) {
    "EventStream.untimed" -> "tsyn2ustream\\<cdot>"
    else -> null
  }

  override fun visit(node: ASTFieldAccessExpression) {
    val fqn = ProvisorischerCode.getQualifiedNameOfFunction(node)
    val tsyn = mapToIsabelleTsyn(fqn)
    if (tsyn != null) {
      printer.print(tsyn)
      return
    }
    super.visit(node)
  }

  override fun endVisit(node: ASTFieldAccessExpression) {
    val fqn = ProvisorischerCode.getQualifiedNameOfFunction(node)
    if (mapToIsabelleTsyn(fqn) != null) {
      return
    }
    super.endVisit(node)
  }

  override fun traverse(node: ASTCallExpression) {
    val lhs = node.expression
    when (ProvisorischerCode.getQualifiedNameOfFunction(lhs)) {
      "SyncStream.map" -> {
        printer.print("smap (map_tsyn ")
        node.arguments.expressionList[0].accept(getTraverser())
        printer.print(")\\<cdot>")
        ProvisorischerCode.getObject(lhs).accept(getTraverser())
      }
      "SyncStream.zip" -> {
        printer.print("tsynZipAlt\\<cdot>")
        ProvisorischerCode.getObject(lhs).accept(getTraverser())
        printer.print("\\<cdot>")
        node.arguments.expressionList[0].accept(getTraverser())
      }
      "SyncStream.syncBoolFilter" -> {
        printer.print("tsynBoolFilter\\<cdot>")
        ProvisorischerCode.getObject(lhs).accept(getTraverser())
        printer.print("\\<cdot>")
        node.arguments.expressionList[0].accept(getTraverser())
      }
      else -> super.traverse(node)
    }
  }

  override fun handle(node: ASTArrayAccessExpression) {
    val indexStr = SysMLv2Mill.prettyPrint(node.indexExpression, false).trim()
    val accessor = when (indexStr.toIntOrNull()) {
      0 -> "tsynFst"
      1 -> "tsynSnd"
      else -> return super.handle(node)
    }

    val fieldAccess = node.expression as ASTFieldAccessExpression
    val portUsage = getPortUsage(fieldAccess)
    val channelPattern = buildChannelPattern(portUsage.get().name, fieldAccess.name)

    printer.print("($accessor $channelPattern)")
  }

  private fun buildChannelPattern(portName: String, attrName: String): String {
    return "channel_${portName}${SEP}${attrName}_pattern"
  }
}
