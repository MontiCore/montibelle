package montibelle.backbone;

import com.googlecode.jsonrpc4j.spring.AutoJsonRpcServiceImplExporter;
import montibelle.backbone.util.IsabelleUtil;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.context.annotation.Bean;

import java.nio.file.Path;

@org.springframework.context.annotation.Configuration
public class Configuration {

  public static final String HWL_PROVIDER_BEAN = "hwlProvider";

  @Bean
  public static AutoJsonRpcServiceImplExporter autoJsonRpcServiceImplExporter() {
    return new AutoJsonRpcServiceImplExporter();
  }

  @Bean
  public IsabelleUtil isabelleUtil(
      @Value("${core.path}") String corePath)
  {
    return new IsabelleUtil(Path.of(corePath).toAbsolutePath());
  }

}
