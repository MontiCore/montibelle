package de.montibelle.ontology;

import com.nomagic.magicdraw.core.Application;
import com.nomagic.magicdraw.core.Project;
import com.nomagic.magicdraw.core.project.ProjectDescriptorsFactory;
import com.nomagic.magicdraw.core.project.ProjectsManager;
import com.nomagic.magicdraw.openapi.uml.ModelElementsManager;
import com.nomagic.magicdraw.openapi.uml.PresentationElementsManager;
import com.nomagic.magicdraw.openapi.uml.ReadOnlyElementException;
import com.nomagic.magicdraw.openapi.uml.SessionManager;
import com.nomagic.magicdraw.properties.PropertyID;
import com.nomagic.magicdraw.properties.PropertyManager;
import com.nomagic.magicdraw.uml.symbols.PresentationElement;
import com.nomagic.magicdraw.uml.symbols.layout.composite.CompositeStructureDiagramLayouter;
import com.nomagic.magicdraw.uml.symbols.shapes.ShapeElement;
import com.nomagic.uml2.ext.jmi.helpers.ModelHelper;
import com.nomagic.uml2.ext.jmi.helpers.StereotypesHelper;
import com.nomagic.uml2.ext.magicdraw.activities.mdfundamentalactivities.Activity;
import com.nomagic.uml2.ext.magicdraw.classes.mdkernel.*;
import de.se_rwth.commons.logging.Log;
import com.nomagic.magicdraw.sysml.util.SysMLProfile;

import java.awt.*;
import java.io.File;
import java.util.ArrayList;
import java.util.Optional;
import java.util.stream.Collectors;

public class Importer {

  public static final String SYSML_BDD = "SysML Block Definition Diagram";

  private File file;

  private Optional<String> errorMessage = Optional.empty();

  public Importer(File file) {
    this.file = file;
  }

  public boolean isPresentErrorMessage() {
    return this.errorMessage.isPresent();
  }

  void setErrorMessage(String error) {
    this.errorMessage = Optional.of(error);
  }

  public String getErrorMessage() {
    return this.errorMessage.get();
  }

  public boolean doImport() {
    ProjectsManager pm = Application.getInstance().getProjectsManager();

    var file = new File("C:/Users/Mathias/Documents/Clone.mdzip");
    var pd = ProjectDescriptorsFactory.createProjectDescriptor(file.toURI());
    pm.loadProject(pd, true);
    Project cloned = pm.getActiveProject();

    return true;
  }

  public boolean doImport2() {
    this.errorMessage = Optional.empty();

    var project = getOrCreateProject();

    SessionManager.getInstance().createSession(project, "Create a diagram");

    var diagram = createDiagram(project);

    var mem = ModelElementsManager.getInstance();
    var f = createBlock(project, "Function");
    var fg = createBlock(project, "FunctionGroup");
    var fp = createBlock(project, "FunctionalPart");
    var fpg = createBlock(project, "FunctionalPartGroup");
    var s_f = createShape(project, diagram, f, Color.green);
    var s_fg = createShape(project, diagram, fg, Color.green);
    createShape(project, diagram, fp, Color.green);
    createShape(project, diagram, fpg, Color.green);

    var assoc = createAssoc(project, fg, f);

    var pem = PresentationElementsManager.getInstance();
    var dpe = project.getDiagram(diagram);

    try {
      var p = pem.createPathElement(assoc, s_fg, s_f);
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage(
        "Failed to add association arrow, diagram was read-only");
      Log.error("0x10118 " + this.getErrorMessage(), e);
    }

    SessionManager.getInstance().closeSession(project);
    SessionManager.getInstance().createSession(project, "Modify a diagram");

    for(Property end : assoc.getMemberEnd()) {
      PresentationElement endPresentation =
        dpe.findPresentationElement(end, null);

      if (endPresentation != null) {
        PropertyManager pm = endPresentation.getPropertyManager();
        var p = pm.getProperty(PropertyID.SHOW_NAME);
        System.out.println("All properties of " + endPresentation +  "are: "
          + pm.getProperties().stream().map(s -> s.getName()).collect(Collectors.joining(", ")));
        p.setValue(false);
      }
    }

    boolean res;
    if(this.isPresentErrorMessage()) {
      SessionManager.getInstance().cancelSession(project);
      res = false;
    }
    else {
      SessionManager.getInstance().closeSession(project);
      res = true;
    }

    var diagramPresentation = project.getDiagram(diagram);
    diagramPresentation.open();
    diagramPresentation.layout(false,
        new CompositeStructureDiagramLayouter());

    return res;
  }

  private Association createAssoc(
    Project project,
    NamedElement parent,
    NamedElement child)
  {
    Association association = project.getElementsFactory().createAssociationInstance();
    association.setOwner(project.getPrimaryModel());
    association.setName("includes");

    Property parent_end = ModelHelper.getFirstMemberEnd(association);
    parent_end.setOwner(parent);
    parent_end.setType((Type) child);
    parent_end.setName("");
    parent_end.setVisibility(VisibilityKindEnum.PUBLIC);
    ModelHelper.setNavigable(parent_end, true);

    Property child_end = ModelHelper.getSecondMemberEnd(association);
    child_end.setOwner(child);
    child_end.setType((Type) parent);
    child_end.setName(null);
    child_end.setVisibility(VisibilityKindEnum.PUBLIC);
    ModelHelper.setNavigable(child_end, true);

    return association;
  }

  private ShapeElement createShape(Project project, Diagram diagram, Element element, Color color) {
    var pem = PresentationElementsManager.getInstance();
    var dpe = project.getDiagram(diagram);

    ShapeElement shape = null;
    try {
      shape = pem.createShapeElement(element, dpe);
      shape.setFillColor(color);
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage(
        "Failed to add control node, diagram was read-only");
      Log.error("0x10116 " + this.getErrorMessage(), e);
    }

    return shape;
  }

  private NamedElement createBlock(Project project, String name) {
    var mem = ModelElementsManager.getInstance();
    var parent = project.getPrimaryModel();

    var block = project.getElementsFactory().createClassInstance();
    block.setName(name);
    addBlockStereotype(project, block);

    try {
      mem.addElement(block, parent);
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage("Failed to create block, project was read-only");
      Log.error("0x10104 " + this.getErrorMessage(), e);
    }

    return block;
  }

  private void addBlockStereotype(Project project, Element element) {
    var profile = StereotypesHelper.getProfile(project, SysMLProfile.PROFILE_NAME);
    var stereotype = StereotypesHelper.getStereotype(project, SysMLProfile.BLOCK_STEREOTYPE, profile);

    StereotypesHelper.addStereotype(element, stereotype);
  }

  protected Project getOrCreateProject() {
    var manager = Application.getInstance().getProjectsManager();
    var project = manager.getActiveProject();
    if(project == null) {
      project = manager.createProject();
    }
    return project;
  }

  protected Diagram createDiagram(Project project) {
    var mem = ModelElementsManager.getInstance();

    Diagram diagram = null;
    try {
      diagram = mem.createDiagram(SYSML_BDD, project.getPrimaryModel());
    }
    catch (ReadOnlyElementException e) {
      this.setErrorMessage("Failed to create diagram, project was read-only");
      Log.error("0x10103 " + this.getErrorMessage(), e);
    }
    return diagram;
  }

  public static Optional<Activity> resolveActivity(
      Project project,
      String name)
  {
    Optional<Activity> res = Optional.empty();

    ArrayList children = new ArrayList();
    Element current = project.getPrimaryModel();
    children.add(current);
    for (int i = 0; i < children.size(); i++)
    {
      current = (Element) children.get(i);

      if(current instanceof Activity
          && ((Activity)current).getName().equals(name))
      {
        res = Optional.of((Activity) current);
        break;
      }

      children.addAll(current.getOwnedElement());
    }

    return res;
  }

  protected Activity getOrCreateActivity(
      Project project,
      String name)
  {
    var optAct = resolveActivity(project, name);

    if(optAct.isPresent()) {
      return optAct.get();
    }
    else {
      var mem = ModelElementsManager.getInstance();
      var parent = project.getPrimaryModel();

      var activity = project.getElementsFactory().createActivityInstance();
      activity.setName(name);

      try {
        mem.addElement(activity, parent);
      } catch (ReadOnlyElementException e) {
        this.setErrorMessage("Failed to create activity, project was read-only");
        Log.error("0x10104 " + this.getErrorMessage(), e);
      }

      return activity;
    }
  }

}
