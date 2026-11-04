import de.monticore.lang.sysmlv2.SysMLv2Mill
import de.monticore.lang.sysmlv2.SysMLv2Tool
import de.monticore.lang.sysmlv2._ast.ASTSysMLModel
import focus.Bundles
import focus.Sps
import focus.SymType2MCTypePrinter
import montibelle.focus.DataInc
import montibelle.focus.Datatypes
import montibelle.focus.FocusMill
import montibelle.focus.FocusTool
import montibelle.focus._ast.*
import montibelle.transformer.generic.Constants
import montibelle.transformer.sysml.SysMLProvider
import montibelle.transformer.sysml.printer.TypePrinter
import montibelle.transformer.util.FreemarkerInterface
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import trafos.Ports2BundleTrafo
import java.io.BufferedWriter
import java.io.StringWriter
import java.nio.file.Paths


class SpecificationTemplateTest {

  @Test
  fun testWithoutPredicates(){
    val stringWriter = StringWriter()
    val outputStream = BufferedWriter(stringWriter)

    val target = Paths.get("target/resources/test/testModels")
    val sysmlTool = SysMLv2Tool()
    sysmlTool.init()

    val model = "part def Component {\n" +
        "\n" +
        "  port input: ~Controls;\n" +
        "  port output: Controls;\n" +
        "\n" +
        "}"
    val ast: ASTSysMLModel = SysMLv2Mill.parser().parse_String(model).get()

    val artifact = sysmlTool.createSymbolTable(ast)
    sysmlTool.completeSymbolTable(ast)
    sysmlTool.finalizeSymbolTable(ast)
    sysmlTool.runDefaultCoCos(ast)
    sysmlTool.runAdditionalCoCos(ast)

    val component = SysMLProvider.provideComponents(artifact).get(0)

    val focusTool = FocusTool()
    focusTool.init()
    focusTool.setup(target)

    val allChanTypes: List<String> = listOf()
    val allStructs: List<String> = listOf()
    val allEnums: List<String> = listOf()

    val datatypes = ASTDatatypesBuilder()
      .setChannelTypesList(allChanTypes)
      .setUserDefinedStructsList(allStructs)
      .setUserDefinedEnumsList(allEnums)
      .uncheckedBuild()

    focusTool.createSymbolTable(datatypes)
    val (datatypesTheory, datatypesSession) = Datatypes.createTheoryFrom(datatypes)
    focusTool.createSymbolTable(datatypesTheory)
    focusTool.createSymbolTable(datatypesSession)

    focusTool.completeSymbolTable(datatypes)
    focusTool.completeSymbolTable(datatypesTheory)
    focusTool.completeSymbolTable(datatypesSession)

    val dataInc = ASTDataIncBuilder()
      .setChannelTypesList(allChanTypes)
      .uncheckedBuild()
    focusTool.createSymbolTable(dataInc)

    val (t, s) = DataInc.createTheoryFrom(dataInc)
    focusTool.createSymbolTable(t)
    focusTool.createSymbolTable(s)

    focusTool.completeSymbolTable(dataInc)
    focusTool.completeSymbolTable(t)
    focusTool.completeSymbolTable(s)

    val trafo = Ports2BundleTrafo(
      ASTBundleBuilder().setName(component.fullName + "." + "Input")
        .setTiming("EVENT"),
      ASTBundleBuilder().setName(component.fullName + "." + "Output")
        .setTiming("EVENT"),
      TypePrinter(),
      withLongLocalName = false
    )

    val inputBundle = trafo.inputBuilder.uncheckedBuild()
    val outputBundle = trafo.outputBuilder.uncheckedBuild()

    val inputSession = Bundles.createSession(inputBundle)
    val inputTheory = Bundles.createTheory(inputBundle, inputSession.name)

    val outputTheory = Bundles.createTheory(outputBundle, inputSession.name)

    val bigList = listOf(inputBundle, outputBundle, inputTheory, outputTheory, inputSession)

    bigList.forEach {
      focusTool.createSymbolTable(it)
      focusTool.completeSymbolTable(it)
    }

    val params = component.parameterList.map {
      val mcType = FocusMill.parser().parse_StringMCType(
        SymType2MCTypePrinter().print(it.getType())
      ).get()
      ASTParameterBuilder()
        .setName("var_" + it.name)
        .setMCType(mcType)
        .build()
    }
    val specBuilder = ASTSpecificationBuilder()
      .setInputBundle("Component.Input")
      .setOutputBundle("Component.Output")
      .setFqn(component.fullName)
      .setStrongCausal(component.isStrongCausal)
      .setParametersList(params)

    val spec = specBuilder.build()
    focusTool.createSymbolTable(spec)
    val sess = Sps.createSession(spec)
    focusTool.createSymbolTable(sess)
    val th = Sps.createTheory(spec, sess.name)
    focusTool.createSymbolTable(th)

    focusTool.completeSymbolTable(spec)
    focusTool.completeSymbolTable(th)

    FreemarkerInterface.instance.generate(
      Constants.SPEC,
      outputStream,
      false,
      th,
      spec
    )
    outputStream.flush()

    fun String.normalize() = replace("\\s+".toRegex(), " ").trim()
    val result = stringWriter.toString().normalize()
    val expected = """
wholePredicate para input output = (
  ((wellformed input)
      \<longrightarrow> True)
  \<and> (causality input output))
""".normalize()
    assertTrue(result.contains(expected))
  }
}



