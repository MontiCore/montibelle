import RequirementHelper.*
import extension.comparator.FileCompare
import montibelle.focus.FocusMill
import montibelle.focus._symboltable.SpsSymbolBuilder
import montibelle.transformer.generic.Constants.REQUIREMENT_TEMPLATE
import montibelle.transformer.util.FreemarkerInterface
import org.junit.jupiter.api.Test
import java.nio.file.Path

class RequirementPrinterTest {
  companion object {
    const val REQUIREMENT_TEST_RESOURCES
                  = "src/test/resources/montibelle/transformer/requirement";
  }

  @Test
  fun focusRequirementToRequirementPrintingTest() {
    val rawRequirement = """
      requirement Requirement {
        theory Theory1;
        subject Inverter_LLR1;
        assumptions "input = <[EventMsg a, Tick]>" "output = < [EventMsg ( \\<not> a), Tick]>";
        guarantee "def_Inverter_LLR1_Output.sbgetter \\<cdot>
             (execsem ((), (x, y), z, s)
             (def_Inverter_LLR1_Input.sbsetter \\<cdot> input)) = output";
      }
      """.trimIndent()

    var parser = FocusMill.parser()
    var ast = parser.parse_StringRequirement(rawRequirement).get()

    var sess = createSession(ast);
    var th = createTheory(ast, sess);

    val spsMock = SpsSymbolBuilder()
                    .setName("Inverter_LLR1")
                    .setTheory(th.name).build();
    FocusMill.globalScope().add(spsMock);

    buildSymbolTable(ast, sess, th);

    FreemarkerInterface.instance.generate(
      REQUIREMENT_TEMPLATE,
      Path.of(REQUIREMENT_TEST_RESOURCES).resolve("theories").resolve(
        sess.path.resolve(th.filename + ".thy")).toAbsolutePath(),
      false,
      th,
      ast
    )
  }

  @FileCompare(base = REQUIREMENT_TEST_RESOURCES, recursive = true)
  @Test
  fun focusRequirementReachabilityToRequirementPrintingTest() {
    val rawRequirement = """
      requirement Reachability {
        theory Theory1;
        subject Cockpit_LLR;
        assumptions "{channel_Cockpit_LLR_input_dataConstr P2_plus_Eve_request_P1_accepts,
      channel_Cockpit_LLR_input_dataConstr P1_plus_Eve_request_P2_accepts} \\<inter> eValues\\<cdot>input = {}";
          guarantee "(StateConstr state__P1_P2_Eve) \\<notin> sreachableStates (behavior.eaut ())\\<cdot>input";
        proofStartHint "apply(simp add: sreachableStates_def autInitConfig.rep_eq autTransition.rep_eq behavior.eaut.rep_eq)" "apply(simp add: initialConfigs_def eventGen.config_def outconv_def image_comp behavior.ndaInitConfigC_def eventGen.ndaInitConfigC_def)" "apply(simp add: h assms)";
      }
      """.trimIndent()

    var parser = FocusMill.parser()
    var ast = parser.parse_StringRequirement(rawRequirement).get()

    var sess = createSession(ast);
    var th = createTheory(ast, sess);

    val spsMock = SpsSymbolBuilder()
                    .setName("Cockpit_LLR")
                    .setTheory(th.name).build();
    FocusMill.globalScope().add(spsMock);

    buildSymbolTable(ast, sess, th);

    FreemarkerInterface.instance.generate(
      REQUIREMENT_TEMPLATE,
      Path.of(REQUIREMENT_TEST_RESOURCES).resolve("theories").resolve(
        sess.path.resolve(th.filename + ".thy")).toAbsolutePath(),
      false,
      th,
      ast
    )
  }

}
