import de.se_rwth.commons.logging.LogStub;
import epc.EPCMill;
import epc._ast.*;
import org.junit.BeforeClass;
import org.junit.Test;

import java.io.IOException;

import static org.assertj.core.api.Assertions.assertThat;

public class ElementParserTest {

  @BeforeClass
  public static void init() {
    LogStub.init();
    EPCMill.init();
  }

  @Test
  public void testParseDiag() throws IOException {
    var parser = EPCMill.parser();
    var diag =
        "\"MyDiagram\" " +
            "Properties " +
            "Properties " +
            "Type                \"MyType\" " +
            "Group               \"MyGroup\" " +
            "Time of generation  Jan 1 1900 00:00:00 AM " +
            "Creator             name@domain.tld " +
            "Last change         Jan 1 1900 00:00:00 AM " +
            "Last user           name@domain.tld " +
            "Objects " +
            "Graphic ";

    var astDiag = parser.parse_StringDiagram(diag);
    assertThat(LogStub.getFindings()).isEmpty();
    assertThat(astDiag).isPresent();
  }

  @Test
  public void testParseEventObject() throws IOException {
    var parser = EPCMill.parser();
    var eventObj =
        "\"MyObject\" " +
        "Properties " +
        "Type               \"Event\" " +
        "Group              \"MyGroup\" " +
        "Time of generation Jan 1 1900 00:00:00 AM " +
        "Creator            name@domain.tld " +
        "Last change        Jan 1 1900 00:00:00 AM " +
        "Last user          name@domain.tld " +
        "Relationships " +
        "Relationship type  Object name  Object type";

    var astObj = parser.parse_StringObject(eventObj);
    assertThat(LogStub.getFindings()).isEmpty();
    assertThat(astObj).isPresent();
  }

}
