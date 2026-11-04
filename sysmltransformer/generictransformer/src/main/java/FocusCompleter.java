import de.monticore.types3.TypeCheck3;
import montibelle.focus._ast.ASTAutomaton;
import montibelle.focus._ast.ASTBundle;
import montibelle.focus._ast.ASTChannel;
import montibelle.focus._ast.ASTChannelMapping;
import montibelle.focus._ast.ASTChannelType;
import montibelle.focus._ast.ASTComposition;
import montibelle.focus._ast.ASTConnectors;
import montibelle.focus._ast.ASTDataInc;
import montibelle.focus._ast.ASTDatatypes;
import montibelle.focus._ast.ASTElement;
import montibelle.focus._ast.ASTField;
import montibelle.focus._ast.ASTFocusFunction;
import montibelle.focus._ast.ASTEnumType;
import montibelle.focus._ast.ASTInstance;
import montibelle.focus._ast.ASTParameter;
import montibelle.focus._ast.ASTParameterValue;
import montibelle.focus._ast.ASTRequirement;
import montibelle.focus._ast.ASTSession;
import montibelle.focus._ast.ASTSpecification;
import montibelle.focus._ast.ASTSps;
import montibelle.focus._ast.ASTStateSpace;
import montibelle.focus._ast.ASTStateVariable;
import montibelle.focus._ast.ASTStateVariableTOP;
import montibelle.focus._ast.ASTTheory;
import montibelle.focus._ast.ASTUserDefinedStruct;
import montibelle.focus._visitor.FocusVisitor2;
import trafos.GenericTypePrinter;

import java.util.stream.Collectors;

public class FocusCompleter implements FocusVisitor2 {

  public void visit(ASTEnumType node) {
    node.getSymbol().setFinite(node.isFinite());
    node.getSymbol().setFiniteChoicesList(node.getLiteralsList());
  }

  public void visit(ASTChannelType node) {
    node.getSymbol().setTimingName(node.getTiming());
    var symType = TypeCheck3.symTypeFromAST(node.getMCType());
    node.getSymbol().setSymType(symType);
  }

  public void visit(ASTChannel node) {
    node.getSymbol().setLocalName(node.getLocalName());
    node.getSymbol().setPattern(node.getPattern());
    node.getSymbol().setTypeName(node.getType());
  }

  public void visit(ASTTheory node) {
    node.getSymbol().setFilename(node.getFilename());
    node.getSymbol().setSessionName(node.getSessionName());
  }

  public void visit(ASTSession node) {
    node.getSymbol().setPathList(node.getPathList());
  }

  public void visit(ASTElement node) {
    node.getSymbol().setTheory(node.getTheory());
  }

  public void visit(ASTBundle node) {
    node.getSymbol().setChannelNamesList(node.getChannelsList());
    node.getSymbol().setTimingName(node.getTiming());
    if (node.isPresentCodeTheory()) {
      node.getSymbol().setCodeTheory(node.getCodeTheory());
    }
  }

  public void visit(ASTParameter node) {
    var symType = TypeCheck3.symTypeFromAST(node.getMCType());
    node.getSymbol().setSymType(symType);
  }

  public void visit(ASTSps node) {
    node.getSymbol().setInputName(node.getInputBundleSymbol().getName());
    node.getSymbol().setOutputName(node.getOutputBundleSymbol().getName());
    node.getSymbol().setStrong(node.isStrongCausal());
  }

  public void visit(ASTSpecification node) {
    node.getSymbol().setAssumptionsLen(node.sizeAssumptions());
    node.getSymbol().setPredicatesLen(node.sizePredicates());
  }

  public void visit(ASTComposition node) {
    node.getSymbol().setFeedbackName(node.getFeedbackBundle());
    node.getSymbol().setPartNamesList(
        node.getPartsSymbolList().stream()
            .map(s -> s.get().getName())
            .collect(Collectors.toList())
    );
    node.getSymbol().setConnectorsName(node.getConnectors().getName());
    node.getSymbol().setFeedbackName(node.getFeedbackBundle());
  }

  public void visit(ASTInstance node) {
    node.getSymbol().setInputMapName(node.getInputConnectors().getName());
    node.getSymbol().setOutputMapName(node.getOutputConnectors().getName());
    node.getSymbol().setParameterValuesList(
        node.getParameterValueList().stream()
            .map(ASTParameterValue::getName)
            .collect(Collectors.toList())
    );
    node.getSymbol().setSpsName(node.getSSps());
  }

  public void visit(ASTParameterValue node) {
    node.getSymbol().setDefinition(node.getDefinition());
    node.getSymbol().setValue(node.getValue());
  }

  public void visit(ASTConnectors node) {
    node.getSymbol().setChannelMappingNamesList(
        node.getChannelMappingList().stream()
            .map(ASTChannelMapping::getName)
            .collect(Collectors.toList())
    );
  }

  public void visit(ASTChannelMapping node) {
    node.getSymbol().setValue(node.getValue());
  }

  public void visit(ASTDatatypes node) {
    node.getSymbol().setChannelTypesList(node.getChannelTypesList());
    node.getSymbol().setUserDefinedStructsList(node.getUserDefinedStructsList());
    node.getSymbol().setUserDefinedEnumsList(node.getUserDefinedEnumsList());
    node.getSymbol().setFunctionsList(node.getFocusFunctionsList());
  }

  public void visit(ASTDataInc node) {
    node.getSymbol().setChannelTypesList(node.getChannelTypesList());
  }

  public void visit(ASTUserDefinedStruct node) {
    node.getSymbol().setFieldNamesList(
        node.getFieldList().stream()
            .map(ASTField::getName)
            .collect(Collectors.toList())
    );
  }

  public void visit(ASTField node) {
    node.getSymbol().setPattern(node.getPattern());
    var symType = TypeCheck3.symTypeFromAST(node.getMCType());
    node.getSymbol().setSymType(symType);
  }

  public void visit(ASTAutomaton node) {
    node.getSymbol().setStatespaceName(node.getStates().getName());
    node.getSymbol().setFinite(node.isFinite());
    if(node.isPresentCodeTheory()) {
      node.getSymbol().setCodeTheoryName(node.getCodeTheory());
    }
  }

  public void visit(ASTStateSpace node) {
    node.getSymbol().setVariableNamesList(
        node.getStateVariableList().stream()
            .map(ASTStateVariableTOP::getName)
            .collect(Collectors.toList())
    );
  }

  public void visit(ASTStateVariable node) {
    var symType = TypeCheck3.symTypeFromAST(node.getMCType());
    node.getSymbol().setSymType(symType);
  }

  public void visit(ASTFocusFunction node) {
    var symType = TypeCheck3.symTypeFromAST(node.getMCType());
    node.getSymbol().setSymType(symType);
  }

  @Override
  public void visit(ASTRequirement node) {
    node.getSymbol().setSubjectSymbol(
        node.getEnclosingScope().resolveSps(
            node.getSubjectSymbol().getName()
        ).get()
    );
  }
}
