package trafos

import de.monticore.lang.componentconnector._symboltable.MildInstanceSymbol
import de.monticore.symbols.compsymbols._symboltable.PortSymbol
import de.monticore.symbols.compsymbols._visitor.CompSymbolsVisitor2
import de.se_rwth.commons.Names
import de.se_rwth.commons.logging.Log
import montibelle.focus.FocusMill
import montibelle.focus.FocusTool
import montibelle.focus._ast.ASTBundleBuilder
import montibelle.focus._ast.ASTChannelBuilder

class Ports2BundleTrafo(
    val inputBuilder: ASTBundleBuilder,
    val outputBuilder: ASTBundleBuilder,
    val typePrinter: ITypePrinter,
    val withLongLocalName: Boolean = true,
    val instance: MildInstanceSymbol? = null): CompSymbolsVisitor2 {

  override fun visit(node: PortSymbol) {
    val currBuilder: ASTBundleBuilder

    currBuilder = if (node.isIncoming) {
      inputBuilder
    } else {
      outputBuilder
    }

    val isabelleType = typePrinter.print(node.type)

    var chanName: String
    if(instance != null) {
      chanName = SourceMap.mapToFocus(node, instance)
    }
    else {
      chanName = SourceMap.mapToFocus(node)
    }

    var exChannel = FocusMill.globalScope().resolveChannel(chanName)
    if(exChannel.isEmpty()) {
      val channelAst = ASTChannelBuilder().apply {
        name = chanName
        if (instance == null) {
          localName = if (withLongLocalName) "channel_${
            currBuilder.name.substringBeforeLast('.').replace('.', '_')
          }_${
            node.name.replace(
              '.',
              '_'
            )
          }_rep" else "channel_${node.name.replace('.', '_')}"
        } else {
          localName = if (withLongLocalName) "channel_${
            currBuilder.name.substringBeforeLast('.').replace('.', '_')
          }_${
            node.name.replace(
              '.',
              '_'
            )
          }_rep" else "channel_${
            Names.getSimpleName(
              currBuilder.name.substringBeforeLast('.')
            ).replace('.', '_')
          }_${node.name.replace('.', '_')}"
        }
        pattern = localName + "_pattern"
        type = "${isabelleType.replace(Regex("[^A-Za-z0-9]"), "")}${SourceMap.mapToFocus(node.timing).name}"

      }.build()

      FocusTool().createSymbolTable(channelAst)
      FocusTool().completeSymbolTable(channelAst)
    }
    exChannel = FocusMill.globalScope().resolveChannel(chanName)
    if(exChannel.isPresent) {
      currBuilder.addChannels(chanName)
    }
    else {
      Log.warn("Channel %s not created, thus not added to bundle %s".format(
        chanName, currBuilder.name))
    }
    currBuilder.timing = SourceMap.mapToFocus(node.timing).name
  }
}
