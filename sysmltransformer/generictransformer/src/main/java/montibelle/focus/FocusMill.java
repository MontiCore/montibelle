package montibelle.focus;

import montibelle.transformer.generic.hwls.AHwlProvider;
import montibelle.transformer.generic.hwls.InMemoryHwlProvider;

public class FocusMill extends FocusMillTOP {

  private AHwlProvider hwlProvider;

  protected FocusMill() {
    hwlProvider = new InMemoryHwlProvider();
  }

  public static AHwlProvider getHwlProvider() {
    return getMill()._getHwlProvider();
  }

  protected AHwlProvider _getHwlProvider() {
    return hwlProvider;
  }

  public static void setHwlProvider(AHwlProvider hwlProvider) {
    getMill()._setHwlProvider(hwlProvider);
  }

  protected void _setHwlProvider(AHwlProvider hwlProvider) {
    this.hwlProvider = hwlProvider;
  }

}
