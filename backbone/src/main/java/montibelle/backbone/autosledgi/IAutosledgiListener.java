package montibelle.backbone.autosledgi;

import montibelle.backbone.util.IProcessListener;

public interface IAutosledgiListener extends IProcessListener {

  default void onProgress(int progress, int currentLemma, int totalLemmas) {

  }

  default void onProofResultChanged(int solved, int failed) {

  }

}
