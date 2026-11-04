package montibelle.backbone;

import de.se_rwth.commons.logging.Log;
import org.springframework.boot.SpringApplication;
import org.springframework.boot.autoconfigure.SpringBootApplication;

@SpringBootApplication
public class Main {

  public static void main(String[] args) {
    Log.init();
    SpringApplication.run(Main.class, args);
  }

}
