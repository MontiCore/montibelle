import de.monticore.lang.sysmlv2.SysMLv2Mill
import de.se_rwth.commons.logging.Log
import de.se_rwth.commons.logging.LogStub
import extension.comparator.FileCompare
import montibelle.focus.FocusMill
import montibelle.transformer.generic.hwls.InMemoryHwlProvider
import montibelle.transformer.sysml.Main
import org.apache.commons.io.FileUtils
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.Disabled
import java.nio.file.Paths
import kotlin.test.Test

class AbpTest {
  companion object {
    const val BASE = "src/test/resources/abp"
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
      "$MODELS/Booleans.sysml;" +
          "$MODELS/Data.sysml;" +
          "$MODELS/Data_Bool_Tuples.sysml;" +
          "$MODELS/Nat_Bool_Tuples.sysml;" +
          "$MODELS/Decrypt.sysml;" +
          "$MODELS/Encrypt.sysml",
      "$MODELS/Alice_LLR.sysml",
      "$MODELS/Alice_HLR.sysml",
      "$MODELS/Bob_LLR.sysml",
      "$MODELS/Bob_HLR.sysml",
      "$MODELS/Encrypt1_HLR.sysml",
      "$MODELS/Encrypt2_HLR.sysml",
      "$MODELS/SecureProtocol_HLR1.sysml",
      "$MODELS/Decrypt1_HLR.sysml",
      "$MODELS/Decrypt2_HLR.sysml",
      "$MODELS/Eve_HLR.sysml"
    )

    var target = Paths.get(BASE)
    var hwlProvider = InMemoryHwlProvider()

    modelSets.forEach { modelSet ->
      var sources = modelSet.split(";").map { Paths.get(it) }
      Main.transformIncrementally(sources, target, hwlProvider, false)

      assertThat(Log.getFindings()).filteredOn{it.isError}.isEmpty()

      SysMLv2Mill.globalScope().clear()
      FocusMill.init()
      FocusMill.globalScope().clear()

      SysMLv2Mill.reset()
      FocusMill.reset()
    }
  }

}
