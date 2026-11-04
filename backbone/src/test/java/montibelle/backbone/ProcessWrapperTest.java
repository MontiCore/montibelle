package montibelle.backbone;

import de.se_rwth.commons.logging.Log;
import montibelle.backbone.util.IProcessListener;
import montibelle.backbone.util.ProcessWrapper;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.util.Objects;

public class ProcessWrapperTest {

  @Test
  public void asyncStartStop() throws IOException, InterruptedException {

    String logName = getClass().getName();

    ProcessWrapper wrapper = new ProcessWrapper("sleep 1; echo 'Hello World!'", Path.of("test.thy"));

    wrapper.addListener(new IProcessListener() {
      @Override
      public void onStarted() {
        Log.info("Started!", logName);
      }

      @Override
      public void onStopped(int exitCode) {
        assert exitCode == 0;
        Log.info("Stopped!", logName);
      }

      @Override
      public void onLog(String logLine) {
        Log.info(logLine, logName);
      }
    });

    assert wrapper.start();
    assert wrapper.waitForExit() == 0;
    assert wrapper.getLog().get(0).equals("Hello World!");

  }

}
