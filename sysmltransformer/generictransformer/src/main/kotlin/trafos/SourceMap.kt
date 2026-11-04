package trafos

import de.monticore.ast.ASTNode
import de.monticore.lang.componentconnector._symboltable.ComponentConnectorScope
import de.monticore.lang.componentconnector._symboltable.IComponentConnectorScope
import de.monticore.lang.componentconnector._symboltable.MildComponentSymbol
import de.monticore.lang.componentconnector._symboltable.MildInstanceSymbol
import de.monticore.lang.componentconnector._symboltable.MildPortSymbol
import de.monticore.symbols.basicsymbols._symboltable.VariableSymbol
import de.monticore.symbols.compsymbols._symboltable.PortSymbol
import de.monticore.symbols.compsymbols._symboltable.SubcomponentSymbol
import de.monticore.symbols.compsymbols._symboltable.Timing
import de.monticore.symboltable.ISymbol
import montibelle.focus.FocusMill
import montibelle.focus._symboltable.TimingSymbol
import javax.sound.sampled.Port

object SourceMap {

  @JvmStatic
  fun mapToFocus(source: PortSymbol): String {
    val spanningSymbol = source.enclosingScope.spanningSymbol
    val potentialComponent =
      (source.enclosingScope as IComponentConnectorScope).resolveMildComponent(
        spanningSymbol.fullName
      )

    val ownerName =
      if (potentialComponent.isPresent && potentialComponent.get().refinementStart.isPresent)
        potentialComponent.get().refinementStart.get().fullName else spanningSymbol.fullName

    return "channel_${ownerName.replace('.', '_')}_${
      source.name.replace(
        '.',
        '_'
      )
    }"
  }

  fun mapToFocus(source: PortSymbol, instance: MildInstanceSymbol): String {
    return "channel_${instance.fullName.replace('.','_')}_${source.name.replace('.','_')}"
  }

  fun mapToFocus(source: MildInstanceSymbol): String {
    return source.fullName
  }

  fun mapToFocus(source: VariableSymbol): String {
    return source.fullName
  }

  @JvmStatic
  fun mapToFocus(timing: Timing): TimingSymbol {
    return FocusMill.globalScope().resolveTiming(
        when (timing) {
          Timing.UNTIMED -> "TONE"
          Timing.TIMED -> "EVENT"
          Timing.TIMED_SYNC -> "SYNC"
        }
    ).get()
  }
}
