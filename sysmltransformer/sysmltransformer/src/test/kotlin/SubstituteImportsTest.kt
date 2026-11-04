package montibelle.transformer

import de.se_rwth.commons.logging.Log
import de.se_rwth.commons.logging.LogStub
import extension.comparator.FileCompare
import montibelle.transformer.generic.hwls.HwlTheory
import montibelle.transformer.generic.hwls.HwlType
import montibelle.transformer.generic.hwls.InMemoryHwlProvider
import montibelle.transformer.sysml.Main
import org.apache.commons.io.FileUtils
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths

class SubstituteImportsTest {

  companion object {
    private const val BASE = "src/test/resources/minInverter"
    private const val MODELS = "$BASE/models"
  }

  @BeforeEach
  fun clear() {
    LogStub.init()
  }

  @FileCompare(base = BASE, recursive = true)
  @Test
  fun testSubstituteFromScratch() {
    FileUtils.deleteDirectory(Paths.get("${BASE}/focusSymbols").toFile())
    FileUtils.deleteDirectory(Paths.get("${BASE}/sysmlSymbols").toFile())
    FileUtils.deleteDirectory(Paths.get("${BASE}/theories").toFile())

    var target = Paths.get(BASE)

    var hwlProvider = InMemoryHwlProvider()
    var hwlTheory = HwlTheory("hwl_Dummy", "hwl_Dummy", HwlType.SUBSTITUTE)
    hwlProvider.addHwl("bundle_BoolInverter", "def_BoolInverter_Input", hwlTheory)

    val sources = listOf(
      Paths.get("$MODELS/Bool.sysml"),
      Paths.get("$MODELS/BoolInverter.sysml")
    )

    Main.transformIncrementally(sources, target, hwlProvider, false)

    assertThat(Log.getFindings()).filteredOn { it.isError }.isEmpty()

    val file: Path = Paths
      .get("${BASE}/theories/sps/BoolInverter/def_BoolInverter.thy")
    val lines = Files.readAllLines(file)
    val actualLine = lines[3].trim()
    val expectedLine = "(* Gen  *) hwl_Dummy.hwl_Dummy bundle_BoolInverter.def_BoolInverter_Output"

    assertThat(actualLine).isEqualTo(expectedLine)
  }

  @Test
  fun testSubstituteWithSymbols() {
    var target = Paths.get(BASE)

    var hwlProvider = InMemoryHwlProvider()
    var hwlTheory = HwlTheory("hwl_Dummy", "hwl_Dummy", HwlType.SUBSTITUTE)
    hwlProvider.addHwl("bundle_BoolInverter", "def_BoolInverter_Input", hwlTheory)

    val sources = listOf(
        Paths.get("$MODELS/Bool.sysml"),
        Paths.get("$MODELS/BoolInverter.sysml")
    )

    Main.transformIncrementally(sources, target, hwlProvider, false)

    assertThat(Log.getFindings()).filteredOn { it.isError }.isEmpty()

    val file: Path = Paths
      .get("${BASE}/theories/sps/BoolInverter/def_BoolInverter.thy")
    val lines = Files.readAllLines(file)
    val actualLine = lines[3].trim()
    val expectedLine = "(* Gen  *) hwl_Dummy.hwl_Dummy bundle_BoolInverter.def_BoolInverter_Output"

    assertThat(actualLine).isEqualTo(expectedLine)
  }
}

