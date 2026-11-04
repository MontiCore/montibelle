package montibelle.backbone.util;

import montibelle.backbone.workspace.Parameters;

public class RegisteredWorkspace {
  public Parameters parameters;
  public String id;

  public RegisteredWorkspace(Parameters parameters, String id) {
    this.parameters = parameters;
    this.id = id;
  }

  public RegisteredWorkspace() {
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    else if(o instanceof RegisteredWorkspace) {
      RegisteredWorkspace otherWorkspace = (RegisteredWorkspace) o;
      return parameters.equals(otherWorkspace.parameters) && id.equals(otherWorkspace.id);
    }
    else {
      return false;
    }
  }
}
