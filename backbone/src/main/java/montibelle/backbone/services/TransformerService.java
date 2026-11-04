package montibelle.backbone.services;

import com.googlecode.jsonrpc4j.spring.AutoJsonRpcServiceImpl;
import de.se_rwth.commons.logging.Log;
import montibelle.backbone.transformer.Transformer;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.stereotype.Component;
import org.springframework.stereotype.Service;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.net.URI;
import java.net.URL;
import java.net.URLConnection;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.time.Instant;
import java.time.temporal.ChronoUnit;

@AutoJsonRpcServiceImpl
@Service
@Component
public class TransformerService implements Transformer {

  @Value("${montibelle.token.path}")
  private String tokenPath;

  @Autowired
  private WorkspaceService workspaceManager;

  @Autowired
  HwlService hwlManager;

  @Override
  public String transform(String workspaceId, String version) throws Exception {
    var workdirDefinition = workspaceManager.retrieve(workspaceId);
    return transform(workspaceId, version, Paths.get(new URL(workdirDefinition.getTargetUri()).toURI()));
  }

  public static Path common(Path a, Path b) {
    while (b != null && !a.startsWith(b))
      b = b.getParent();
    return b;
  }

  public String transform(String workspaceId, String version, Path base) throws Exception {
    var workdirDefinition = workspaceManager.retrieve(workspaceId);
    var source = Paths.get(new URL(workdirDefinition.getSourceUri()).toURI());
    var target = Paths.get(new URL(workdirDefinition.getTargetUri()).toURI());
    var theoryTarget = target.resolve("theories");
    var binTarget = target.resolve("bin");
    var logsTarget  = target.resolve("logs");

    var command = "gradle -p \""+common(source, target).toAbsolutePath().toString()+"\" transform -PtransformerVersion=" + version;

    String timestamp = Instant.now().truncatedTo(ChronoUnit.SECONDS).toString().replace( "-" , "" ).replace( ":" , "" );
    File logFile = logsTarget.resolve("transformer_" + timestamp + ".log").toFile();
    if (!logFile.exists()){
      new File(logFile.getParent()).mkdirs();
      logFile.createNewFile();
    }

    if (System.getProperty("os.name").startsWith("Windows")) {
      command = "\"" + command.replace("\\", "/") + "\"";
    }

    ProcessBuilder builder;
    if (System.getProperty("os.name").startsWith("Windows")) {
      builder = new ProcessBuilder("cmd", "/c", command).redirectErrorStream(true);
    } else {
      builder = new ProcessBuilder("bash", "-c",  command).redirectErrorStream(true);
    }
    builder.redirectOutput(logFile);
    builder.start();

    return logFile.toString();
  }

  public Path downloadTransformerJar(Path base, String version, Boolean replace) throws IOException {
    String token = "";
    try {
      token = Files.readString(Path.of(tokenPath)).replace("\n","");
    }
    catch (IOException ex) {
      Log.error("Accesstoken was not properly configured, check " + tokenPath);
    }

    Path jarFile = base.resolve("transformer_" + version + ".jar");
    if (Files.exists(jarFile) && !replace) {
      return jarFile;
    }
    else if(Files.exists(jarFile)) {
      Files.delete(jarFile);
    }
    else if(jarFile.getParent() != null) {
      Files.createDirectories(jarFile.getParent());
    }
    Files.createFile(jarFile);

    var url = new URL("https://git.rwth-aachen.de/api/v4/projects/46134/packages/maven/montibelle/transformer/sysmltransformer/"
        + version.replaceFirst("-.*", "-SNAPSHOT")
        + "/sysmltransformer-"
        + version
        + "-jar-with-dependencies.jar");
    URLConnection conn = url.openConnection();
    conn.setRequestProperty("Private-Token", token);
    conn.setRequestProperty("Deploy-Token", token);
    Log.warn(token);
    InputStream in = conn.getInputStream();

    byte[] buffer = new byte[1024];
    OutputStream out = Files.newOutputStream(jarFile);
    int numRead;
    while ((numRead = in.read(buffer)) != -1) {
      out.write(buffer, 0, numRead);
    }
    if (in != null) {
      in.close();
    }
    if (out != null) {
      out.close();
    }

    return jarFile;
  }

}
