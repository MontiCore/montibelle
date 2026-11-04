import de.monticore.lang.sysmlv2.SysMLv2Mill
import de.se_rwth.commons.logging.Log
import de.se_rwth.commons.logging.LogStub
import extension.comparator.FileCompare
import montibelle.focus.FocusMill
import montibelle.transformer.generic.hwls.FilebasedHwlProvider
import montibelle.transformer.sysml.Main
import org.apache.commons.io.FileUtils
import org.assertj.core.api.Assertions.assertThat
import java.nio.file.Paths
import kotlin.test.Test

class SecurityGateTest {
  companion object {
    const val BASE = "src/test/resources/securityGate"
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
      "$MODELS/ActionEnum.sysml",
      "$MODELS/Actions.sysml",
      "$MODELS/VerificationLibrary.sysml",
      "$MODELS/SecurityGate_LLR.sysml",
      "$MODELS/Reachability.sysml",
    )

    var target = Paths.get(BASE)
    var hwlProvider = FilebasedHwlProvider(Paths.get("${BASE}/hwls/HWLS.yaml"))

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
  fun testMainWithSymbols() {
    LogStub.init()

    val modelSets = listOf(
      "$MODELS/ActionEnum.sysml",
      "$MODELS/Actions.sysml",
      "$MODELS/VerificationLibrary.sysml",
      "$MODELS/SecurityGate_LLR.sysml",
      "$MODELS/Reachability.sysml",
    )

    var target = Paths.get(BASE)
    var hwlProvider = FilebasedHwlProvider(Paths.get("${BASE}/hwls/HWLS.yaml"))

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
