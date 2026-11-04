import de.monticore.expressions.commonexpressions._ast.ASTEqualsExpression;
import de.monticore.lang.sysmlconstraints._ast.ASTConstraintUsage;
import de.monticore.lang.sysmlv2.SysMLv2Mill;
import de.monticore.lang.sysmlv2.SysMLv2Tool;
import de.monticore.lang.sysmlv2._visitor.SysMLv2Traverser;
import de.se_rwth.commons.logging.LogStub;
import montibelle.transformer.sysml.Main;
import trafos.IExpressionPrinter;
import java.io.IOException;
import org.junit.jupiter.api.Test;
import static org.assertj.core.api.Assertions.assertThat;

public class StreamLibraryTest {

  @Test
  public void testCallExpressionToIsabelleMapping() throws IOException {
    var model =
        "attribute es: Streams::EventStream { :>> E: ScalarValues::Boolean; }"
            + "attribute us: Streams::UntimedStream { :>> E: ScalarValues::Boolean; }"
            + "constraint {Streams::EventStream::eNth(es, 2)  == us }";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage cU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression eqExpr = (ASTEqualsExpression) cU.getExpression();

    String res = printer.print(eqExpr);
    assertThat(res).isNotEmpty();
    assertThat(res)
        .isEqualTo("((esnth 2\\<cdot>var_es) = var_us)");
  }

  @Test
  public void testFunOpExpressionToIsabelleMapping() throws IOException {
    var model =
        "attribute es: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
            + "attribute us: Streams::UntimedStream { :>> E: ScalarValues::Boolean;}"
            + "constraint { es->Streams::EventStream::eNth(2) == us }";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage cU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression eqExpr = (ASTEqualsExpression) cU.getExpression();

    String res = printer.print(eqExpr);
    assertThat(res).isNotEmpty();
    assertThat(res)
        .isEqualTo("(esnth 2\\<cdot>var_es = var_us)");
  }

  @Test
  public void testeMapToIsabelleMapping() throws IOException {
    var model =
        "attribute esB: Streams::EventStream { :>> E: ScalarValues::Boolean; }"
        + "attribute esA: Streams::EventStream { :>> E: ScalarValues::Boolean; }"
        + "constraint { esA->Streams::EventStream::eMap { in b: Boolean; b } == esB }"
        + "constraint { Streams::EventStream::eMap(esA, { in b: Boolean; b }) == esB }";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();

    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((emap (\\<lambda> b. b)\\<cdot>var_esA) = var_esB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(emap (\\<lambda> b. b)\\<cdot>var_esA = var_esB)");
  }

  @Test
  public void testE2UstreamToIsabelleMapping() throws IOException {
    var model =
        "attribute us: Streams::UntimedStream { :>> E: ScalarValues::Boolean; }"
            + "attribute es: Streams::EventStream { :>> E: ScalarValues::Boolean; }"
            + "constraint { es->Streams::EventStream::eUntimed() == us}"
            + "constraint { Streams::EventStream::eUntimed(es) == us }";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((e2ustream\\<cdot>var_es) = var_us)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(e2ustream\\<cdot>var_es = var_us)");
  }

  @Test
  public void testEFilterToIsabelleMapping() throws IOException {
    var model =
        "attribute esB: Streams::EventStream { :>> E: ScalarValues::Boolean; }"
        + "attribute esA: Streams::EventStream { :>> E: ScalarValues::Boolean; }"
        + "constraint { esA->Streams::EventStream::eFilter { in b: ScalarValues::Boolean; b } == esB}"
        + "constraint { Streams::EventStream::eFilter(esA, { in b: ScalarValues::Boolean; b }) == esB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((efilter (\\<lambda> b. b)\\<cdot>var_esA) = var_esB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(efilter (\\<lambda> b. b)\\<cdot>var_esA = var_esB)");
  }

  @Test
  public void testFirstToIsabelleMapping() throws IOException {
    var model =
        "attribute usB: Streams::UntimedStream { :>> E: ScalarValues::Boolean;}"
        + "attribute esA: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
        + "constraint { esA->Streams::EventStream::'first'() == usB}"
        + "constraint { Streams::EventStream::'first'(esA) == usB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((eshdts\\<cdot>var_esA) = var_usB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(eshdts\\<cdot>var_esA = var_usB)");
  }

  @Test
  public void testExistsToIsabelleMapping() throws IOException {
    var model = "constraint { ControlFunctions::exists((all ScalarValues::Natural), { in x: ScalarValues::Natural; x > 0 })}"
        + "constraint { (all ScalarValues::Natural)->ControlFunctions::exists { in x: ScalarValues::Natural; x > 0 }}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(0);
    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(1);

    String callRes = printer.print(callCU.getExpression());
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("(Bex (UNIV :: nat set) (\\<lambda> x. (x > 0)))");

    String foRes = printer.print(foCU.getExpression());
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("Bex (UNIV :: nat set) (\\<lambda> x. (x > 0))");
  }

  @Test
  public void testForAllToIsabelleMapping() throws IOException {
    var model = "constraint { ControlFunctions::forAll((all ScalarValues::Natural), { in x: ScalarValues::Natural; x >= 0 })}"
        + "constraint { (all ScalarValues::Natural)->ControlFunctions::forAll { in x: ScalarValues::Natural; x >= 0 }}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(0);
    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(1);

    String callRes = printer.print(callCU.getExpression());
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("(Ball (UNIV :: nat set) (\\<lambda> x. (x >= 0)))");

    String foRes = printer.print(foCU.getExpression());
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("Ball (UNIV :: nat set) (\\<lambda> x. (x >= 0))");
  }

  @Test
  public void testERougherTimeToIsabelleMapping() throws IOException {
    var model =
      "attribute esA: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
        + "attribute esB: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
        + "constraint { esA->Streams::EventStream::eRougherTime(2) == esB}"
        + "constraint { Streams::EventStream::eRougherTime(esA, 2) == esB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((e2rougherTime 2\\<cdot>var_esA) = var_esB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(e2rougherTime 2\\<cdot>var_esA = var_esB)");
  }

  @Test
  public void testEFinerTimeToIsabelleMapping() throws IOException {
    var model =
        "attribute esA: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
            + "attribute esB: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
            + "constraint { esA->Streams::EventStream::eFinerTime(2) == esB}"
            + "constraint { Streams::EventStream::eFinerTime(esA, 2) == esB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((e2finerTime 2 var_esA) = var_esB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(e2finerTime 2 var_esA = var_esB)");
  }

  @Test
  public void testETakeToIsabelleMapping() throws IOException {
    var model =
        "attribute esA: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
            + "attribute esB: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
            + "constraint { esA->Streams::EventStream::eTake(2) == esB}"
            + "constraint { Streams::EventStream::eTake(esA, 2) == esB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((etakeMsg 2\\<cdot>var_esA) = var_esB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(etakeMsg 2\\<cdot>var_esA = var_esB)");
  }

  @Test
  public void testEDropMultipleToIsabelleMapping() throws IOException {
    var model =
        "attribute esA: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
          + "attribute esB: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
          + "constraint { esA->Streams::EventStream::eDropMultiple(2) == esB}"
          + "constraint { Streams::EventStream::eDropMultiple(esA, 2) == esB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((edropMsg 2\\<cdot>var_esA) = var_esB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(edropMsg 2\\<cdot>var_esA = var_esB)");
  }

  @Test
  public void testETakeWhileToIsabelleMapping() throws IOException {
    var model =
      "attribute esA: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
      + "attribute esB: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
      + "constraint { esA->Streams::EventStream::eTakeWhile{ in b: ScalarValues::Boolean; b } == esB}"
      + "constraint { Streams::EventStream::eTakeWhile(esA,{ in b: ScalarValues::Boolean; b }) == esB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((etakewhile (\\<lambda> b. b)\\<cdot>var_esA) = var_esB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(etakewhile (\\<lambda> b. b)\\<cdot>var_esA = var_esB)");
  }

  @Test
  public void testEDropWhileToIsabelleMapping() throws IOException {
    var model =
        "attribute esA: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
            + "attribute esB: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
            + "constraint { esA->Streams::EventStream::eDropWhile{ in b: ScalarValues::Boolean; b } == esB}"
            + "constraint { Streams::EventStream::eDropWhile(esA,{ in b: ScalarValues::Boolean; b }) == esB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((edropwhile (\\<lambda> b. b)\\<cdot>var_esA) = var_esB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(edropwhile (\\<lambda> b. b)\\<cdot>var_esA = var_esB)");
  }

  @Test
  public void testEProjFstToIsabelleMapping() throws IOException {
    var model =
      "attribute usA: Streams::UntimedStream { :>> E: VerificationLibrary::Tuple"
        + "{:>> fst: ScalarValues::Boolean; :>> snd: ScalarValues::Boolean;}}"
        + "attribute esB: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
        + "constraint { usA->Streams::EventStream::eProjFst() == esB}"
        + "constraint { Streams::EventStream::eProjFst(usA) == esB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((eprojFst\\<cdot>var_usA) = var_esB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(eprojFst\\<cdot>var_usA = var_esB)");
  }

  @Test
  public void testEProjSndToIsabelleMapping() throws IOException {
    var model =
        "attribute usA: Streams::UntimedStream { :>> E: VerificationLibrary::Tuple"
            + "{:>> fst: ScalarValues::Boolean; :>> snd: ScalarValues::Boolean;}}"
            + "attribute esB: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
            + "constraint { usA->Streams::EventStream::eProjSnd() == esB}"
            + "constraint { Streams::EventStream::eProjSnd(usA) == esB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((eprojSnd\\<cdot>var_usA) = var_esB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(eprojSnd\\<cdot>var_usA = var_esB)");
  }

  @Test
  public void testEZipToIsabelleMapping() throws IOException {
    var model =
      "attribute esA: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
      + "attribute esB: Streams::EventStream { :>> E: ScalarValues::Boolean;}"
      + "attribute esC: Streams::EventStream { :>> E: VerificationLibrary::Tuple"
      + "{:>> fst: ScalarValues::Boolean; :>> snd: ScalarValues::Boolean;}}"
      + "constraint { esA->Streams::EventStream::eZip(esB) == esC}"
      + "constraint { Streams::EventStream::eZip(esA,esB) == esC}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(4);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((ezip\\<cdot> var_esA\\<cdot>var_esB) = var_esC)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(ezip\\<cdot> var_esA\\<cdot>var_esB = var_esC)");
  }

  @Test
  public void testETimesToIsabelleMapping() throws IOException {
    var model =
        "attribute esA: Streams::EventStream { :>> E: ScalarValues::Boolean; }"
        + "attribute esB: Streams::EventStream { :>> E: ScalarValues::Boolean; }"
        + "constraint { esA->Streams::EventStream::eTimes(3) == esB}"
        + "constraint { Streams::EventStream::eTimes(esA,3) == esB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((sntimes 3 var_esA) = var_esB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(sntimes 3 var_esA = var_esB)");
  }

  @Test
  public void testsyncTimesToIsabelleMapping() throws IOException {
    var model =
      "attribute toneA: Streams::SyncStream { :>> E: ScalarValues::Boolean; }"
      + "attribute toneB: Streams::SyncStream { :>> E: ScalarValues::Boolean; }"
      + "constraint { toneA->Streams::SyncStream::syncTimes(3) == toneB}"
      + "constraint { Streams::SyncStream::syncTimes(toneA,3) == toneB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((sntimes 3 var_toneA) = var_toneB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(sntimes 3 var_toneA = var_toneB)");
  }

  @Test
  public void testtoptTimesToIsabelleMapping() throws IOException {
    var model =
      "attribute tsynA: Streams::ToptStream{ :>> E: ScalarValues::Boolean; }"
      + "attribute tsynB: Streams::ToptStream{ :>> E: ScalarValues::Boolean; }"
      + "constraint { tsynA->Streams::ToptStream::toptTimes(3) == tsynB}"
      + "constraint { Streams::ToptStream::toptTimes(tsynA,3) == tsynB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((sntimes 3 var_tsynA) = var_tsynB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(sntimes 3 var_tsynA = var_tsynB)");
  }

  @Test
  public void testtoptInfTimesToIsabelleMapping() throws IOException {
    var model =
      "attribute tsynA: Streams::ToptStream{ :>> E: ScalarValues::Boolean; }"
      + "attribute tsynB: Streams::ToptStream{ :>> E: ScalarValues::Boolean; }"
      + "constraint { tsynA->Streams::ToptStream::toptInfTimes() == tsynB}"
      + "constraint { Streams::ToptStream::toptInfTimes(tsynA) == tsynB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((sinftimes var_tsynA) = var_tsynB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(sinftimes var_tsynA = var_tsynB)");
  }

  @Test
  public void testeInfTimesToIsabelleMapping() throws IOException {
    var model =
      "attribute esA: Streams::EventStream { :>> E: ScalarValues::Boolean; }"
      + "attribute esB: Streams::EventStream { :>> E: ScalarValues::Boolean; }"
      + "constraint { esA->Streams::EventStream::eInfTimes() == esB}"
      + "constraint { Streams::EventStream::eInfTimes(esA) == esB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((sinftimes var_esA) = var_esB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(sinftimes var_esA = var_esB)");
  }

  @Test
  public void testsyncInfTimesToIsabelleMapping() throws IOException {
    var model =
      "attribute toneA: Streams::SyncStream { :>> E: ScalarValues::Boolean; }"
      + "attribute toneB: Streams::SyncStream { :>> E: ScalarValues::Boolean; }"
      + "constraint { toneA->Streams::SyncStream::syncInfTimes() == toneB}"
      + "constraint { Streams::SyncStream::syncInfTimes(toneA) == toneB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((sinftimes var_toneA) = var_toneB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(sinftimes var_toneA = var_toneB)");
  }

  @Test
  public void testsyncRcDupsToIsabelleMapping() throws IOException {
    var model =
        "attribute toneA: Streams::SyncStream { :>> E: ScalarValues::Boolean; }"
            + "attribute toneB: Streams::SyncStream { :>> E: ScalarValues::Boolean; }"
            + "constraint { toneA->Streams::SyncStream::syncRcDups() == toneB}"
            + "constraint { Streams::SyncStream::syncRcDups(toneA) == toneB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((srcdups\\<cdot>var_toneA) = var_toneB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(srcdups\\<cdot>var_toneA = var_toneB)");
  }

  @Test
  public void testtoptRcDupsToIsabelleMapping() throws IOException {
    var model =
        "attribute tsynA: Streams::ToptStream { :>> E: ScalarValues::Boolean; }"
            + "attribute tsynB: Streams::ToptStream { :>> E: ScalarValues::Boolean; }"
            + "constraint { tsynA->Streams::ToptStream::toptRcDups() == tsynB}"
            + "constraint { Streams::ToptStream::toptRcDups(tsynA) == tsynB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((srcdups\\<cdot>var_tsynA) = var_tsynB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(srcdups\\<cdot>var_tsynA = var_tsynB)");
  }

  @Test
  public void testeRcDupsToIsabelleMapping() throws IOException {
    var model =
        "attribute esA: Streams::EventStream { :>> E: ScalarValues::Boolean; }"
            + "attribute esB: Streams::EventStream { :>> E: ScalarValues::Boolean; }"
            + "constraint { esA->Streams::EventStream::eRcDups() == esB}"
            + "constraint { Streams::EventStream::eRcDups(esA) == esB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((srcdups\\<cdot>var_esA) = var_esB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(srcdups\\<cdot>var_esA = var_esB)");
  }

  @Test
  public void testuTakeToIsabelleMapping() throws IOException {
    var model =
      "attribute usA: Streams::UntimedStream{:>> E: ScalarValues::Boolean; }"
      + "attribute usB: Streams::UntimedStream{:>> E: ScalarValues::Boolean; }"
      + "constraint { usA->Streams::UntimedStream::uTake(3) == usB}"
      + "constraint { Streams::UntimedStream::uTake(usA,3) == usB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((stake 3\\<cdot>var_usA) = var_usB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(stake 3\\<cdot>var_usA = var_usB)");
  }

  @Test
  public void testsyncTakeToIsabelleMapping() throws IOException {
    var model =
        "attribute syncA: Streams::SyncStream{:>> E: ScalarValues::Boolean; }"
            + "attribute syncB: Streams::SyncStream{:>> E: ScalarValues::Boolean; }"
            + "constraint { syncA->Streams::SyncStream::syncTake(3) == syncB}"
            + "constraint { Streams::SyncStream::syncTake(syncA,3) == syncB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((stake 3\\<cdot>var_syncA) = var_syncB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(stake 3\\<cdot>var_syncA = var_syncB)");
  }

  @Test
  public void testtoptTakeToIsabelleMapping() throws IOException {
    var model =
      "attribute tsynA: Streams::ToptStream{ :>> E: ScalarValues::Boolean; }"
      + "attribute tsynB: Streams::ToptStream{ :>> E: ScalarValues::Boolean; }"
      + "constraint { tsynA->Streams::ToptStream::toptTake(3) == tsynB}"
      + "constraint { Streams::ToptStream::toptTake(tsynA,3) == tsynB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((stake 3\\<cdot>var_tsynA) = var_tsynB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(stake 3\\<cdot>var_tsynA = var_tsynB)");
  }

  @Test
  public void testtoptDropMultipleToIsabelleMapping() throws IOException {
    var model =
      "attribute tsynA: Streams::ToptStream{ :>> E: ScalarValues::Boolean; }"
      + "attribute tsynB: Streams::ToptStream{ :>> E: ScalarValues::Boolean; }"
      + "constraint { tsynA->Streams::ToptStream::toptDropMultiple(3) == tsynB}"
      + "constraint { Streams::ToptStream::toptDropMultiple(tsynA,3) == tsynB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((sdrop 3\\<cdot>var_tsynA) = var_tsynB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(sdrop 3\\<cdot>var_tsynA = var_tsynB)");
  }

  @Test
  public void testsyncDropMultipleToIsabelleMapping() throws IOException {
    var model =
      "attribute toneA: Streams::SyncStream{ :>> E: ScalarValues::Boolean; }"
      + "attribute toneB: Streams::SyncStream{ :>> E: ScalarValues::Boolean; }"
      + "constraint { toneA->Streams::SyncStream::syncDropMultiple(3) == toneB}"
      + "constraint { Streams::SyncStream::syncDropMultiple(toneA,3) == toneB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((sdrop 3\\<cdot>var_toneA) = var_toneB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(sdrop 3\\<cdot>var_toneA = var_toneB)");
  }

  @Test
  public void testuDropMultipleToIsabelleMapping() throws IOException {
    var model =
      "attribute usA: Streams::UntimedStream{ :>> E: ScalarValues::Boolean; }"
      + "attribute usB: Streams::UntimedStream{ :>> E: ScalarValues::Boolean; }"
      + "constraint { usA->Streams::UntimedStream::uDropMultiple(3) == usB}"
      + "constraint { Streams::UntimedStream::uDropMultiple(usA,3) == usB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((sdrop 3\\<cdot>var_usA) = var_usB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(sdrop 3\\<cdot>var_usA = var_usB)");
  }



  @Test
  public void testsyncUntimedToIsabelleMapping() throws IOException {
    var model =
      "attribute toneA: Streams::SyncStream { :>> E: ScalarValues::Boolean; }"
      + "attribute usB: Streams::SyncStream { :>> E: ScalarValues::Boolean; }"
      + "constraint { toneA->Streams::SyncStream::syncUntimed() == usB}"
      + "constraint { Streams::SyncStream::syncUntimed(toneA) == usB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((tone2ustream\\<cdot>var_toneA) = var_usB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(tone2ustream\\<cdot>var_toneA = var_usB)");
  }

  @Test
  public void testsyncToptToIsabelleMapping() throws IOException {
    var model =
      "attribute toneA: Streams::SyncStream { :>> E: ScalarValues::Boolean; }"
      + "attribute tsynB: Streams::SyncStream { :>> E: ScalarValues::Boolean; }"
      + "constraint { toneA->Streams::SyncStream::syncTopt() == tsynB}"
      + "constraint { Streams::SyncStream::syncTopt(toneA) == tsynB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((tone2tsyn\\<cdot>var_toneA) = var_tsynB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(tone2tsyn\\<cdot>var_toneA = var_tsynB)");
  }

  @Test
  public void testsyncEventToIsabelleMapping() throws IOException {
    var model =
      "attribute toneA: Streams::SyncStream { :>> E: ScalarValues::Boolean; }"
      + "attribute esB: Streams::SyncStream { :>> E: ScalarValues::Boolean; }"
      + "constraint { toneA->Streams::SyncStream::syncEvent() == esB}"
      + "constraint { Streams::SyncStream::syncEvent(toneA) == esB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((tone2event\\<cdot>var_toneA) = var_esB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(tone2event\\<cdot>var_toneA = var_esB)");
  }

  @Test
  public void testtoptFilterToIsabelleMapping() throws IOException {
    var model =
      "attribute tsynA: Streams::ToptStream{ :>> E: ScalarValues::Boolean; }"
      + "attribute tsynB: Streams::ToptStream{ :>> E: ScalarValues::Boolean; }"
      + "constraint { tsynA->Streams::ToptStream::toptFilter { in b: ScalarValues::Boolean; true } == tsynB}"
      + "constraint { Streams::ToptStream::toptFilter(tsynA,{ in b: ScalarValues::Boolean; true }) == tsynB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((tsynFilter2 (\\<lambda> b. True)\\<cdot>var_tsynA) = var_tsynB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(tsynFilter2 (\\<lambda> b. True)\\<cdot>var_tsynA = var_tsynB)");
  }

  @Test
  public void testsyncFilterToIsabelleMapping() throws IOException {
    var model =
        "attribute toneA: Streams::SyncStream{ :>> E: ScalarValues::Boolean; }"
            + "attribute toneB: Streams::SyncStream{ :>> E: ScalarValues::Boolean; }"
            + "constraint { toneA->Streams::SyncStream::syncFilter { in b: ScalarValues::Boolean; true } == toneB}"
            + "constraint { Streams::SyncStream::syncFilter(toneA,{ in b: ScalarValues::Boolean; true }) == toneB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((toneFilter2 (\\<lambda> b. True)\\<cdot>var_toneA) = var_toneB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(toneFilter2 (\\<lambda> b. True)\\<cdot>var_toneA = var_toneB)");
  }

  @Test
  public void testuFilterToIsabelleMapping() throws IOException {
    var model =
        "attribute usA: Streams::UntimedStream{ :>> E: ScalarValues::Boolean; }"
            + "attribute usB: Streams::UntimedStream{ :>> E: ScalarValues::Boolean; }"
            + "constraint { usA->Streams::UntimedStream::uFilter { in b: ScalarValues::Boolean; true } == usB}"
            + "constraint { Streams::UntimedStream::uFilter(usA,{ in b: ScalarValues::Boolean; true }) == usB}";

    var tool = new SysMLv2Tool();
    tool.init();
    LogStub.init();
    SysMLv2Traverser traverser = tool.getInheritanceTraverser();
    IExpressionPrinter printer = Main.getEventExpressionPrinter(traverser);

    var ast = SysMLv2Mill.parser().parse_StringSysMLModel(model).get();
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);
    tool.finalizeSymbolTable(ast);

    ASTConstraintUsage foCU = (ASTConstraintUsage) ast.getSysMLElement(2);
    ASTEqualsExpression foEqExpr = (ASTEqualsExpression) foCU.getExpression();

    ASTConstraintUsage callCU = (ASTConstraintUsage) ast.getSysMLElement(3);
    ASTEqualsExpression callEqExpr = (ASTEqualsExpression) callCU.getExpression();

    String callRes = printer.print(callEqExpr);
    assertThat(callRes).isNotEmpty();
    assertThat(callRes)
        .isEqualTo("((sFilter2 (\\<lambda> b. True)\\<cdot>var_usA) = var_usB)");

    String foRes = printer.print(foEqExpr);
    assertThat(foRes).isNotEmpty();
    assertThat(foRes)
        .isEqualTo("(sFilter2 (\\<lambda> b. True)\\<cdot>var_usA = var_usB)");
  }
}
