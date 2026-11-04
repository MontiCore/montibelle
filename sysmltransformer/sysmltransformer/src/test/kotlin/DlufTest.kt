import de.monticore.lang.sysmlv2.SysMLv2Mill
import de.se_rwth.commons.logging.Log
import de.se_rwth.commons.logging.LogStub
import extension.comparator.FileCompare
import montibelle.focus.FocusMill
import montibelle.transformer.generic.hwls.InMemoryHwlProvider
import montibelle.transformer.sysml.Main
import org.apache.commons.io.FileUtils
import org.assertj.core.api.Assertions.assertThat
import java.nio.file.Paths
import kotlin.test.Test

class DlufTest {
  companion object {
    const val BASE = "src/test/resources/dluf"
    const val MODELS = "$BASE/models"
  }

  @FileCompare(base = BASE, recursive = true)
  @Test
  fun testMainFromScratch() {
    LogStub.init()

    FileUtils.deleteDirectory(Paths.get("${BASE}/focusSymbols").toFile())
    FileUtils.deleteDirectory(Paths.get("${BASE}/sysmlSymbols").toFile())
    FileUtils.deleteDirectory(Paths.get("${BASE}/theories").toFile())

    val modelSets = listOf(
        "$MODELS/Ctrl.sysml;" +
            "$MODELS/CtrlEnum.sysml;" +
            "$MODELS/Packet.sysml;" +
            "$MODELS/Packets.sysml",
        "$MODELS/DLUF_HLR1.sysml;" +
            "$MODELS/Merge_LLR.sysml",
        "$MODELS/System_HLR.sysml",
        "$MODELS/Scheduler_HLR2.sysml",
        "$MODELS/DLUF_HLR2.sysml",
        "$MODELS/Buffer_HLR3.sysml",
        "$MODELS/Capacity_HLR3.sysml",
        "$MODELS/Scheduler_HLR3.sysml",
        "$MODELS/DLUF_HLR3.sysml",
        "$MODELS/Buffer_LLR.sysml",
        "$MODELS/Capacity_LLR.sysml",
        "$MODELS/Scheduler_LLR.sysml",
        "$MODELS/DLUF_LLR.sysml",
        "$MODELS/System_LLR.sysml",
    )

    var target = Paths.get(BASE)
    var hwlProvider = InMemoryHwlProvider()

    modelSets.forEach { modelSet ->
      var sources = modelSet.split(";").map { Paths.get(it) }
      Main.transformIncrementally(sources, target, hwlProvider, false)

      assertThat(Log.getFindings()).filteredOn{it.isError}.isEmpty()

      SysMLv2Mill.globalScope().clear()
      FocusMill.globalScope().clear()

      SysMLv2Mill.reset()
      FocusMill.reset()
    }
  }

  @FileCompare(base = BASE, recursive = true)
  @Test
  fun testMainWithSymfiles() {
    LogStub.init()

    val modelSets = listOf(
      "$MODELS/Ctrl.sysml;" +
          "$MODELS/CtrlEnum.sysml;" +
          "$MODELS/Packet.sysml;" +
          "$MODELS/Packets.sysml",
      "$MODELS/DLUF_HLR1.sysml;" +
          "$MODELS/Merge_LLR.sysml",
      "$MODELS/System_HLR.sysml",
      "$MODELS/Scheduler_HLR2.sysml",
      "$MODELS/DLUF_HLR2.sysml",
      "$MODELS/Buffer_HLR3.sysml",
      "$MODELS/Capacity_HLR3.sysml",
      "$MODELS/Scheduler_HLR3.sysml",
      "$MODELS/DLUF_HLR3.sysml",
      "$MODELS/Buffer_LLR.sysml",
      "$MODELS/Capacity_LLR.sysml",
      "$MODELS/Scheduler_LLR.sysml",
      "$MODELS/DLUF_LLR.sysml",
      "$MODELS/System_LLR.sysml",
    )

    var target = Paths.get(BASE)
    var hwlProvider = InMemoryHwlProvider()

    modelSets.forEach { modelSet ->
      var sources = modelSet.split(";").map { Paths.get(it) }
      Main.transformIncrementally(sources, target, hwlProvider, false)

      assertThat(Log.getFindings()).filteredOn{it.isError}.isEmpty()

      SysMLv2Mill.globalScope().clear()
      FocusMill.globalScope().clear()

      SysMLv2Mill.reset()
      FocusMill.reset()
    }
  }

}
