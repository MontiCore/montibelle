package montibelle.backbone.util;

public interface IProcessListener {

  default void onStarted(){

  }
  default void onStopped(int exitCode){

  }

  default void onLog(String logLine){

  }

  default void onProgress(String progress){

  }

}
