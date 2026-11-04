
import aris._ast.ASTMERIDIEM;
import aris._ast.ASTMONTH;
import bpmn.BPMNMill;
import de.se_rwth.commons.logging.Log;
import de.se_rwth.commons.logging.LogStub;
import epc.EPCMill;
import org.junit.Test;

import java.io.IOException;

import static org.assertj.core.api.Assertions.assertThat;

public class ParserTest {

  @Test
  public void testParse() throws IOException {
    LogStub.init();
    BPMNMill.init();
    var parser = BPMNMill.parser();
    var res = parser.parse("src/test/resources/ModelInformation.txt");
    assertThat(Log.getFindings()).isEmpty();
    assertThat(res).isPresent();
    assertThat(res.get().getModelInformation().getName()).isEqualTo("BPMN2");

    var date = res.get().getModelInformation().getDate();
    assertThat(date.getDay()).isEqualTo("17");
    assertThat(date.getMonth()).isEqualTo("2");
    assertThat(date.getYear()).isEqualTo("25");

    var dt = res.get().getDiagram(0).getProperties().getDateTime();
    assertThat(dt.getDay()).isEqualTo("17");
    assertThat(dt.getMonth()).isEqualTo(ASTMONTH.FEB);
    assertThat(dt.getYear()).isEqualTo("2025");
    assertThat(dt.getHour()).isEqualTo("12");
    assertThat(dt.getMinute()).isEqualTo("14");
    assertThat(dt.getSecond()).isEqualTo("58");
    assertThat(dt.getMeridiem()).isEqualTo(ASTMERIDIEM.PM);
  }

  @Test
  public void testMultiDiagram() throws IOException {
    LogStub.init();
    BPMNMill.init();
    var parser = BPMNMill.parser();
    var res = parser.parse("src/test/resources/MultiDiagram.txt");
    assertThat(Log.getFindings()).isEmpty();
    assertThat(res).isPresent();
    assertThat(res.get().getModelInformation().isPresentName()).isFalse();
  }

  @Test
  public void testPDPoA() throws IOException {
    LogStub.init();
    BPMNMill.init();
    var parser = BPMNMill.parser();
    var res = parser.parse("src/test/resources/PDPoA.txt");
    assertThat(Log.getFindings()).isEmpty();
    assertThat(res).isPresent();
    assertThat(res.get().getModelInformation().isPresentName()).isFalse();
  }

  @Test
  public void testPDPoAv2() throws IOException {
    LogStub.init();
    BPMNMill.init();
    var parser = BPMNMill.parser();
    var res = parser.parse("src/test/resources/PDPoAv2.txt");
    assertThat(Log.getFindings()).isEmpty();
    assertThat(res).isPresent();
    assertThat(res.get().getModelInformation().isPresentName()).isFalse();
  }

  @Test
  public void testWeightProcess() throws IOException {
    LogStub.init();
    EPCMill.init();
    var parser = EPCMill.parser();

    var res = parser.parse("src/test/resources/CreateWeightCalculationForecast.Processed.txt");
    assertThat(Log.getFindings()).isEmpty();
    assertThat(parser.hasErrors()).isFalse();
    assertThat(res).isPresent();

    var ast = res.get();
    assertThat(ast.getModelInformation().isPresentName()).isTrue();
    assertThat(ast.getModelInformation().getName())
        .isEqualTo("CreateWeightCalculationForecast");
    assertThat(ast.getDiagramList()).hasSize(1);

    var diagram = ast.getDiagramList().get(0);
    assertThat(diagram.getObjects().getObjectList()).hasSize(163);
    assertThat(diagram.getObjects().getObject(0).getName())
        .isEqualTo("2D Sketches");
    assertThat(diagram.getObjects().getObject(63).getName())
        .isEqualTo("Co-Development OBS check & updated for \"COM\"");
    assertThat(diagram.getObjects().getObject(162).getName())
        .isEqualTo("VPM A320 (CF9A)");
  }

  @Test
  public void testWeightProcessUntangled() throws IOException {
    LogStub.init();
    EPCMill.init();
    var parser = EPCMill.parser();

    var res = parser.parse("src/test/resources/CreateWeightCalculationForecast.Untangled.txt");
    assertThat(Log.getFindings()).isEmpty();
    assertThat(parser.hasErrors()).isFalse();
    assertThat(res).isPresent();

    var ast = res.get();
    assertThat(ast.getModelInformation().isPresentName()).isTrue();
    assertThat(ast.getModelInformation().getName())
        .isEqualTo("CreateWeightCalculationForecast");
    assertThat(ast.getDiagramList()).hasSize(1);

    var diagram = ast.getDiagramList().get(0);
    assertThat(diagram.getObjects().getObjectList()).hasSize(163);
    assertThat(diagram.getObjects().getObject(0).getName())
        .isEqualTo("2D Sketches");
    assertThat(diagram.getObjects().getObject(63).getName())
        .isEqualTo("Co-Development OBS check & updated for \"COM\"");
    assertThat(diagram.getObjects().getObject(162).getName())
        .isEqualTo("VPM A320 (CF9A)");
  }

}
