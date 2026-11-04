import de.se_rwth.commons.logging.LogStub;
import montibelle.focus.FocusMill;
import montibelle.focus.FocusTool;
import montibelle.focus._ast.ASTTheoryBuilder;
import montibelle.transformer.generic.Constants;
import montibelle.transformer.util.FreemarkerInterface;
import org.junit.jupiter.api.Test;
import trafos.GenericTypePrinter;

import java.io.IOException;
import java.io.StringWriter;

import static org.assertj.core.api.Assertions.assertThat;

public class StructTest {

  @Test
  void testTemplate() throws IOException {
    LogStub.init();

    var tool = new FocusTool();
    tool.init();

    var theory = new ASTTheoryBuilder()
        .setSessionName("user")
        .setFilename("Person")
        .build();

    var model = "struct Person { nat age (age_pattern); }";

    var astOptional = FocusMill.parser()
        .parse_StringUserDefinedStruct(model);

    assertThat(astOptional).isPresent();

    var ast = astOptional.get();

    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);

    FreemarkerInterface.instance.getGlex()
        .setGlobalValue("typePrinter", new GenericTypePrinter());

    var writer = new StringWriter();

    FreemarkerInterface.instance.generate(
        Constants.STRUCT,
        writer,
        false,
        theory,
        ast,
        Constants.instance
    );

    var result = writer.toString();

    var expected = "theory Person\n"
        + "  imports \"HOL-Library.Countable_Set\"\n"
        + "\n"
        + "begin\n"
        + "\n"
        + "section \\<open>User-defined Datatypes\\<close>\n"
        + "\n"
        + "datatype Person = PersonConstr (* age = *) \"nat\"\n"
        + "\n"
        + "\n"
        + "instance Person::countable\n"
        + "by(countable_datatype)\n"
        + "\n"
        + "fun Person_get_age :: \"Person => nat\" where\n"
        + "\"Person_get_age (PersonConstr age_pattern) = age_pattern\"\n"
        + "\n"
        + "end\n";

    assertThat(result).isEqualTo(expected);
  }
}
