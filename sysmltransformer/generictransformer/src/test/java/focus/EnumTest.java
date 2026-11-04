package focus;

import de.se_rwth.commons.logging.LogStub;
import montibelle.focus.FocusMill;
import montibelle.focus.FocusTool;
import montibelle.focus._ast.ASTTheoryBuilder;
import montibelle.transformer.generic.Constants;
import montibelle.transformer.util.FreemarkerInterface;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.StringWriter;

import static org.assertj.core.api.Assertions.assertThat;

public class EnumTest {

  @Test
  void testParse() throws IOException {
    LogStub.init();
    var tool = new FocusTool();
    tool.init();
    var model = "Ampelfarben finite \"Rot\" \"Gruen\" \"Gelb\"";
    var ast = FocusMill.parser().parse_StringEnumType(model);

    assertThat(ast).isPresent();
    var focusType = ast.get();
    assertThat(focusType.getLiteralsList()).hasSize(3);
    assertThat(focusType.getLiteralsList().get(0)).isEqualTo("Rot");
    assertThat(focusType.getLiteralsList().get(1)).isEqualTo("Gruen");
    assertThat(focusType.getLiteralsList().get(2)).isEqualTo("Gelb");
  }

  @Test
  void testTemplate() throws IOException {
    LogStub.init();
    var tool = new FocusTool();
    tool.init();
    var model = "Ampelfarben finite \"Rot\" \"Gruen\" \"Gelb\"";
    var astOptional = FocusMill.parser().parse_StringEnumType(model);
    assertThat(astOptional).isPresent();
    var ast = astOptional.get();

    var writer = new StringWriter();
    var theory = new ASTTheoryBuilder();
    theory.setFilename(ast.getName());

    FreemarkerInterface.instance.generate(
        Constants.ENUM,
        writer,
        false,
        theory,
        ast
    );
    var result = writer.toString();

    var expected = "theory Ampelfarben\n"
        + "  imports \"HOL-Library.Countable_Set\"\n"
        + "\n"
        + "begin\n"
        + "\n"
        + "datatype Ampelfarben = Rot | Gruen | Gelb\n"
        + "\n"
        + "instance Ampelfarben::countable\n"
        + "  apply(intro_classes)\n"
        + "  by(countable_datatype)\n"
        + "\n"
        + "end\n";

    assertThat(result).isEqualTo(expected);
  }

}
