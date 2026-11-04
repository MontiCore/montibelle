package bpmn;

import bpmn._ast.*;
import bpmn._symboltable.ObjectSymbol;
import bpmn._visitor.BPMNVisitor2;
import com.nomagic.magicdraw.core.Application;
import com.nomagic.magicdraw.core.Project;
import com.nomagic.magicdraw.openapi.uml.ModelElementsManager;
import com.nomagic.magicdraw.openapi.uml.PresentationElementsManager;
import com.nomagic.magicdraw.openapi.uml.ReadOnlyElementException;
import com.nomagic.magicdraw.openapi.uml.SessionManager;
import com.nomagic.magicdraw.uml.symbols.PresentationElement;
import com.nomagic.magicdraw.uml.symbols.layout.composite.CompositeStructureDiagramLayouter;
import com.nomagic.magicdraw.uml.symbols.shapes.NoteView;
import com.nomagic.magicdraw.uml.symbols.shapes.ShapeElement;
import com.nomagic.uml2.ext.magicdraw.activities.mdbasicactivities.ControlNode;
import com.nomagic.uml2.ext.magicdraw.activities.mdfundamentalactivities.Activity;
import com.nomagic.uml2.ext.magicdraw.activities.mdfundamentalactivities.ActivityNode;
import com.nomagic.uml2.ext.magicdraw.classes.mdkernel.Diagram;
import com.nomagic.uml2.ext.magicdraw.classes.mdkernel.Element;
import de.monticore.ast.ASTNode;
import de.monticore.symboltable.modifiers.AccessModifier;
import de.se_rwth.commons.logging.Log;

import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.function.Predicate;

public class Importer {

  public static final String SYSML_AD = "SysML Activity Diagram";

  protected Map<ASTNode, Element> astToElement
      = new HashMap<>();

  protected Map<ASTNode, PresentationElement> astToPresentation
      = new HashMap<>();

  private File file;

  private Optional<String> errorMessage = Optional.empty();

  public Importer(File file) {
    this.file = file;
  }

  public boolean doImport() {
    this.errorMessage = Optional.empty();

    var tool = new BPMNTool();
    BPMNMill.init();
    var ast = tool.parse(this.file.getAbsolutePath());
    tool.createSymbolTable(ast);
    tool.completeSymbolTable(ast);

    var project = getOrCreateProject();

    SessionManager.getInstance().createSession(project, "Create a diagram");

    var diagrams = new ArrayList<Diagram>();
    for(var astDiagram : ast.getDiagramList()) {
      var diagram = createDiagram(project, astDiagram);

      for(var object : astDiagram.getObjects().getObjectList()) {
        switch (object.getType()) {
          case "Event":
            createStartFinal(project, diagram, object);
            break;
          case "Function":
            createAction(project, diagram, object);
            break;
          case "Rule":
            createDecision(project, diagram, object);
            break;
          case "Text annotation":
            createAnnotation(project, diagram, object);
            break;
        }
      }

      for(var object : astDiagram.getObjects().getObjectList()) {
        createAssociations(project, diagram, object);
      }

      diagrams.add(diagram);
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

    for(var diagram : diagrams) {
      var diagramPresentation = project.getDiagram(diagram);
      diagramPresentation.open();
      diagramPresentation.layout(false,
          new CompositeStructureDiagramLayouter());
    }

    return res;
  }

  private void createStartFinal(
      Project project,
      Diagram diagram,
      ASTObject object)
  {
    Predicate<ASTObject> hasIncoming = o -> o.getRelationshipList().stream()
        .anyMatch(r -> r instanceof ASTIncoming);
    Predicate<ASTObject> hasOutgoing = o -> o.getRelationshipList().stream()
        .anyMatch(r -> r instanceof ASTOutgoing);

    var pem = PresentationElementsManager.getInstance();
    var dpe = project.getDiagram(diagram);
    var mem = ModelElementsManager.getInstance();

    ControlNode node;
    if(hasIncoming.and(hasOutgoing.negate()).test(object)) {
      node = project.getElementsFactory().createActivityFinalNodeInstance();
    }
    else if(hasIncoming.negate().and(hasOutgoing).test(object)) {
      node = project.getElementsFactory().createInitialNodeInstance();
    }
    else {
      setErrorMessage("Encountered event that was neither start nor end event");
      Log.error("0x10114 " + getErrorMessage(),
          object.get_SourcePositionStart());
      return;
    }
    astToElement.put(object, node);

    try {
      mem.addElement(node, diagram.getOwnerOfDiagram());
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage(
          "Failed to create control node, diagram was read-only");
      Log.error("0x10115 " + this.getErrorMessage(), e);
    }

    ShapeElement shape = null;
    try {
      shape = pem.createShapeElement(node, dpe);
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage(
          "Failed to add control node, diagram was read-only");
      Log.error("0x10116 " + this.getErrorMessage(), e);
    }
  }

  private void createAssociations(
      Project project,
      Diagram diagram,
      ASTObject object)
  {
    var pem = PresentationElementsManager.getInstance();
    var dpe = project.getDiagram(diagram);

    var visitor = new BPMNVisitor2() {
      @Override
      public void visit(ASTAssociation otherRef) {
        Predicate<ObjectSymbol> p = obj -> obj.isPresentAstNode() &&
            obj.getAstNode().getType().equals(otherRef.getType());
        var other = otherRef.getEnclosingScope()
            .resolveObjectMany(otherRef.getName(), AccessModifier.ALL_INCLUSION, p)
            .get(0).getAstNode();

        PresentationElement otherPresentation;
        PresentationElement thisPresentation;

        if(otherRef.getType().equals("Text annotation")) {
          otherPresentation = astToPresentation.get(other);

          var thisElement = astToElement.get(object);
          thisPresentation = dpe
              .findPresentationElement(thisElement, PresentationElement.class);
        }
        else if(object.getType().equals("Text annotation")) {
          return;
        }
        else {
          setErrorMessage(
              "Encountered an association where neither end was a note");
          Log.error("0x10113 " + getErrorMessage(),
              otherRef.get_SourcePositionStart());
          return;
        }

        try {
          if (otherPresentation instanceof NoteView) {
            pem.connectNote((ShapeElement) otherPresentation, thisPresentation);
          } else if (thisPresentation instanceof NoteView) {
            pem.connectNote((ShapeElement) thisPresentation, otherPresentation);
          }
          else {
            Log.warn("0x10101 Could not process annotation, neither end was a a note",
                otherRef.get_SourcePositionStart());
          }
        }
        catch (ReadOnlyElementException e) {
          setErrorMessage(
              "Failed to link note to milestone, diagram was read-only");
          Log.error("0x10102 " + getErrorMessage(), e);
        }
      }
      @Override
      public void visit(ASTIncoming sourceRef) {
        Predicate<ObjectSymbol> p = obj -> obj.isPresentAstNode() &&
            obj.getAstNode().getType().equals(sourceRef.getType());
        var source = sourceRef.getEnclosingScope()
            .resolveObjectMany(sourceRef.getName(), AccessModifier.ALL_INCLUSION, p)
            .get(0).getAstNode();
        var sourceElement = astToElement.get(source);
        var sourcePresentation = dpe
            .findPresentationElement(sourceElement, PresentationElement.class);

        var targetElement = astToElement.get(object);
        var targetPresentation = dpe
            .findPresentationElement(targetElement, PresentationElement.class);

        createControlFlow(project, diagram,
            (ShapeElement) sourcePresentation,
            (ShapeElement) targetPresentation);
      }
      @Override
      public void visit(ASTOutgoing node) {
      }
    };
    var traverser = BPMNMill.inheritanceTraverser();
    traverser.add4BPMN(visitor);
    object.accept(traverser);
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

  public static Project getOrCreateProject() {
    var manager = Application.getInstance().getProjectsManager();
    var project = manager.getActiveProject();
    if(project == null) {
      project = manager.createProject();
    }
    return project;
  }

  protected Diagram createDiagram(Project project, ASTDiagram node)
  {
    var mem = ModelElementsManager.getInstance();

    var activity = getOrCreateActivity(project, node.getName());

    Diagram diagram = null;
    try {
      diagram = mem.createDiagram(SYSML_AD, activity);
      astToElement.put(node, diagram);
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

  public ShapeElement createAction(
      Project project,
      Diagram diagram,
      ASTObject astObject)
  {
    var mem = ModelElementsManager.getInstance();
    var pem = PresentationElementsManager.getInstance();
    var dpe = project.getDiagram(diagram);

    var activity = getOrCreateActivity(project, astObject.getName());

    var action = project.getElementsFactory().createCallBehaviorActionInstance();
    action.setName(astObject.getName());
    action.setBehavior(activity);
    astToElement.put(astObject, action);

    try {
      mem.addElement(action, diagram.getOwnerOfDiagram());
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage("Failed to create activity, project was read-only");
      Log.error("0x10105 " + this.getErrorMessage(), e);
    }

    ShapeElement actionShape = null;
    try {
      actionShape = pem.createShapeElement(action, dpe);
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage("Failed to add action, diagram was read-only");
      Log.error("0x10106 " + this.getErrorMessage(), e);
    }

    return actionShape;
  }

  private PresentationElement createDecision(
      Project project,
      Diagram diagram,
      ASTObject node)
  {
    var mem = ModelElementsManager.getInstance();
    var pem = PresentationElementsManager.getInstance();
    var dpe = project.getDiagram(diagram);

    var decision = project.getElementsFactory().createDecisionNodeInstance();
    decision.setName(node.getName());

    try {
      mem.addElement(decision, diagram.getOwnerOfDiagram());
      astToElement.put(node, decision);
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage(
          "Failed to create decision node, project was read-only");
      Log.error("0x10107 " + this.getErrorMessage(), e);
    }

    ShapeElement actionShape = null;
    try {
      actionShape = pem.createShapeElement(decision, dpe);
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage(
          "Failed to add decision node, diagram was read-only");
      Log.error("0x10108 " + this.getErrorMessage(), e);
    }

    return actionShape;
  }

  private ShapeElement createAnnotation(
      Project project,
      Diagram diagram,
      ASTObject node)
  {
    var pem = PresentationElementsManager.getInstance();
    var dpe = project.getDiagram(diagram);

    ShapeElement noteShape = null;
    try {
      noteShape = pem.createNote(dpe);
      ((NoteView)noteShape).setName(node.getName());
      astToPresentation.put(node, noteShape);
    } catch (ReadOnlyElementException e) {
      this.setErrorMessage("Failed to add note, diagram was read-only");
      Log.error("0x10109 " + this.getErrorMessage(), e);
    }

    return noteShape;
  }

  protected void createControlFlow(
      Project project,
      Diagram diagram,
      ShapeElement from,
      ShapeElement to)
  {
    var mem = ModelElementsManager.getInstance();
    var pem = PresentationElementsManager.getInstance();

    var controlFlow = project.getElementsFactory().createControlFlowInstance();
    controlFlow.setSource((ActivityNode) from.getElement());
    controlFlow.setTarget((ActivityNode) to.getElement());

    try {
      mem.addElement(controlFlow, diagram.getOwnerOfDiagram());
    } catch (Exception e) {
      this.setErrorMessage("Failed to create control flow, project was read-only");
      Log.error("0x10110 " + this.getErrorMessage(), e);
    }

    try {
      pem.createPathElement(controlFlow, from, to);
    } catch (Exception e) {
      this.setErrorMessage("Failed to add control flow, diagram was read-only");
      Log.error("0x10111 " + this.getErrorMessage(), e);
    }
  }

}
