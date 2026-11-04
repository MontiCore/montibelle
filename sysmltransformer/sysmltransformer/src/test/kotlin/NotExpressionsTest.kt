import de.monticore.lang.sysmlv2.SysMLv2Mill
import de.monticore.lang.sysmlv2.SysMLv2Tool
import de.se_rwth.commons.logging.Log
import de.se_rwth.commons.logging.LogStub
import montibelle.transformer.sysml.extensions.print
import org.assertj.core.api.Assertions.assertThat
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test

class NotExpressionsTest {

  companion object {
    init {
      LogStub.init()
      SysMLv2Tool().init()
    }
  }

  @BeforeEach
  fun clear() {
    Log.clearFindings()
  }

  @Test
  fun testNotPrefixPrinting() {
    val parser = SysMLv2Mill.parser()
    val expression = parser.parse_StringExpression("not(a)")

    assertThat(Log.getFindings()).isEmpty()
    assertThat(parser.hasErrors()).isFalse()
    assertThat(expression).isPresent()

    val printed = expression.get().print()
    assertThat(printed).isEqualTo("\\<not>((a))")
  }

  @Test
  fun testNotInfixPrinting() {
    val parser = SysMLv2Mill.parser()
    val expression = parser.parse_StringExpression("a != b")

    assertThat(Log.getFindings()).isEmpty()
    assertThat(parser.hasErrors()).isFalse()
    assertThat(expression).isPresent()

    val printed = expression.get().print()
    assertThat(printed).isEqualTo("(a \\<noteq> b)")
  }
}
