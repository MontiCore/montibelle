import montibelle.focus.FocusMill;
import montibelle.focus.FocusTool;
import montibelle.focus._ast.ASTSession;
import montibelle.focus._ast.ASTSessionBuilder;
import montibelle.focus._ast.ASTTheory;
import montibelle.focus._ast.ASTTheoryBuilder;
import montibelle.transformer.generic.Constants;
import org.junit.jupiter.api.Test;
import montibelle.transformer.util.FreemarkerInterface;
import java.io.IOException;
import java.io.BufferedWriter;
import java.io.StringWriter;
import java.util.List;
import static org.assertj.core.api.Assertions.assertThat;
import trafos.GenericTypePrinter;

public class FunctionTest {
  @Test
  public void testSecureState() throws IOException {
    var tool = new FocusTool();
    tool.init();

    ASTSession session = new ASTSessionBuilder()
        .setName("user")
        .setPathList(List.of())
        .build();

    ASTTheory theory = new ASTTheoryBuilder()
        .setSessionName("user")
        .setFilename("SecureState")
        .build();

    tool.createSymbolTable(session);
    tool.createSymbolTable(theory);

    var model = "fun SecureState () String = \"hallo\"";
    var ast = FocusMill.parser().parse_StringFocusFunction(model).get();

    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);

    FreemarkerInterface.instance.getGlex()
        .setGlobalValue("typePrinter", new GenericTypePrinter());

    var expected = "theory SecureState\n" +
        "  imports\n" +
        "    (* Core *) inc.Prelude inc.TSynDatatype inc.EventDatatype\n" +
        "    (* Gen  *)\n" +
        "    (* Hwl  *)\n" +
        "\n" +
        "begin\n" +
        "\n" +
        "fun SecureState:: \"string\" where\n" +
        "\"SecureState  = hallo\"\n" +
        "\n" +
        "end\n";

    var stringWriter = new StringWriter();
    var outputBuffer = new BufferedWriter(stringWriter);

    FreemarkerInterface.instance.generate(
        Constants.FUN_DEF,
        outputBuffer,
        false,
        theory,
        ast,
        Constants.instance
    );

    outputBuffer.flush();

    assertThat(stringWriter.toString()).isEqualTo(expected);
  }

  @Test
  public void testAddition() throws IOException {
    var tool = new FocusTool();
    tool.init();

    ASTSession session = new ASTSessionBuilder()
        .setName("user")
        .setPathList(List.of())
        .build();

    ASTTheory theory = new ASTTheoryBuilder()
        .setSessionName("user")
        .setFilename("Addition")
        .build();

    tool.createSymbolTable(session);
    tool.createSymbolTable(theory);

    var model = "fun add(a: nat, b: nat) nat = \"a + b\"";
    var ast = FocusMill.parser().parse_StringFocusFunction(model).get();

    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);

    FreemarkerInterface.instance.getGlex()
        .setGlobalValue("typePrinter", new GenericTypePrinter());

    var stringWriter = new StringWriter();
    var outputBuffer = new BufferedWriter(stringWriter);

    FreemarkerInterface.instance.generate(
        Constants.FUN_DEF,
        outputBuffer,
        false,
        theory,
        ast,
        Constants.instance
    );

    outputBuffer.flush();

    var expected =
        "theory Addition\n" +
            "  imports\n" +
            "    (* Core *) inc.Prelude inc.TSynDatatype inc.EventDatatype\n" +
            "    (* Gen  *)\n" +
            "    (* Hwl  *)\n" +
            "\n" +
            "begin\n" +
            "\n" +
            "fun add:: \"nat => nat => nat\" where\n" +
            "\"add a b = a + b\"\n" +
            "\n" +
            "end\n";

    assertThat(stringWriter.toString()).isEqualTo(expected);
  }

}
