package montibelle.transformer.sysml.printer;

import de.monticore.expressions.commonexpressions._ast.ASTCallExpression;
import de.monticore.expressions.commonexpressions._ast.ASTFieldAccessExpression;
import de.monticore.expressions.expressionsbasis._ast.ASTExpression;
import de.monticore.expressions.expressionsbasis._ast.ASTNameExpression;
import de.monticore.lang.sysmlexpressions._ast.ASTSysMLFunctionOperationExpression;
import de.se_rwth.commons.logging.Log;

public class ProvisorischerCode {

  private static String getFQNofMethodName(String name) {
    switch (name) {
      case "len": return "Stream.len";
      case "rcDups": return "Stream.rcDups";
      case "eRcDups": return "EventStream.eRcDups";
      case "eInfTimes": return "EventStream.eInfTimes";
      case "eTimes": return "EventStream.eTimes";
      case "eZip": return "EventStream.eZip";
      case "eProjSnd": return "EventStream.eProjSnd";
      case "eProjFst": return "EventStream.eProjFst";
      case "times": return "EventStream.times";
      case "nth": return "EventStream.nth";
      case "eNth": return "EventStream.eNth";
      case "eMap": return "EventStream.eMap";
      case "eUntimed": return "EventStream.eUntimed";
      case "eFilter": return "EventStream.eFilter";
      case "first": return "EventStream.first";
      case "untimed": return "EventStream.untimed";
      case "eRougherTime": return "EventStream.eRougherTime";
      case "eFinerTime": return "EventStream.eFinerTime";
      case "eTake": return "EventStream.eTake";
      case "eDropMultiple": return "EventStream.eDropMultiple";
      case "eTakeWhile": return "EventStream.eTakeWhile";
      case "eDropWhile": return "EventStream.eDropWhile";
      case "uFilter": return "UntimedStream.uFilter";
      case "uDropMultiple": return "UntimedStream.uDropMultiple";
      case "uTake": return "UntimedStream.uTake";
      case "setFilter": return "UntimedStream.setFilter";
      case "uProjFst": return "UntimedStream.uProjFst";
      case "uProjSnd": return "UntimedStream.uProjSnd";
      case "syncFilter": return "SyncStream.syncFilter";
      case "syncEvent": return "SyncStream.syncEvent";
      case "syncTopt": return "SyncStream.syncTopt";
      case "syncUntimed": return "SyncStream.syncUntimed";
      case "syncDropMultiple": return "SyncStream.syncDropMultiple";
      case "syncTake": return "SyncStream.syncTake";
      case "syncRcDups": return "SyncStream.syncRcDups";
      case "syncInfTimes": return "SyncStream.syncInfTimes";
      case "syncTimes": return "SyncStream.syncTimes";
      case "syncProjFst": return "SyncStream.syncProjFst";
      case "syncProjSnd": return "SyncStream.syncProjSnd";
      case "syncBoolFilter": return "SyncStream.syncBoolFilter";
      case "map": return "SyncStream.map";
      case "zip": return "SyncStream.zip";
      case "toptFilter": return "ToptStream.toptFilter";
      case "toptDropMultiple": return "ToptStream.toptDropMultiple";
      case "toptTake": return "ToptStream.toptTake";
      case "toptRcDups": return "ToptStream.toptRcDups";
      case "toptInfTimes": return "ToptStream.toptInfTimes";
      case "toptTimes": return "ToptStream.toptTimes";
      case "exists": return "ControlFunctions.exists";
      case "forAll": return "ControlFunctions.forAll";
      case "select": return "ControlFunctions.select";
      case "size": return "List.size";
      case "tail": return "List.tail";
      case "head": return "List.head";
      case "count": return "List.count";
      case "append": return "List.append";
      case "ReachableStates": return "VerificationLibrary.ReachableStates";
      default: return null;
    }
  }

  public static boolean isStatic(String fqn) {
    switch(fqn) {
      case "ToptStream.toptFilter":
      case "ToptStream.toptDropMultiple":
      case "ToptStream.toptTake":
      case "ToptStream.toptRcDups":
      case "ToptStream.toptInfTimes":
      case "ToptStream.toptTimes":
      case "ControlFunctions.forAll":
      case "ControlFunctions.exists":
      case "EventStream.eRcDups":
      case "EventStream.eInfTimes":
      case "EventStream.eTimes":
      case "EventStream.eZip":
      case "EventStream.eProjFst":
      case "EventStream.eProjSnd":
      case "EventStream.eDropWhile":
      case "EventStream.eTakeWhile":
      case "EventStream.eDropMultiple":
      case "EventStream.eTake":
      case "EventStream.eFinerTime":
      case "EventStream.eRougherTime":
      case "EventStream.first":
      case "EventStream.eFilter":
      case "EventStream.eMap":
      case "EventStream.eUntimed":
      case "EventStream.eNth":
      case "SyncStream.syncFilter":
      case "SyncStream.syncEvent":
      case "SyncStream.syncTopt":
      case "SyncStream.syncUntimed":
      case "SyncStream.syncDropMultiple":
      case "SyncStream.syncTake":
      case "SyncStream.syncRcDups":
      case "SyncStream.syncInfTimes":
      case "SyncStream.syncTimes":
      case "SyncStream.syncProjFst":
      case "SyncStream.syncProjSnd":
      case "UntimedStream.uFilter":
      case "UntimedStream.uDropMultiple":
      case "UntimedStream.uTake":
      case "UntimedStream.uProjFst":
      case "UntimedStream.uProjSnd":
      case "VerificationLibrary.ReachableStates": return true;
      default: return false;
    }
  }

  public static String getQualifiedNameOfFunction(ASTExpression funOrMethod) {
    String methodName = null;
    if(funOrMethod instanceof ASTFieldAccessExpression) {
      var fieldAccess = (ASTFieldAccessExpression) funOrMethod;
      methodName = fieldAccess.getName();
      ASTExpression objExpr = fieldAccess.getExpression();
      if("values".equals(methodName)) {
        if(objExpr instanceof ASTCallExpression) {
          return "UntimedStream.values";
        }
        else if(objExpr instanceof ASTFieldAccessExpression) {
          return "EventStream.values";
        }
      }
    }
    else if(funOrMethod instanceof ASTNameExpression) {
      ASTNameExpression nameExpr = (ASTNameExpression) funOrMethod;
      methodName = nameExpr.getName();
    }
    else if(funOrMethod instanceof ASTSysMLFunctionOperationExpression) {
      var sysmlExpr = (ASTSysMLFunctionOperationExpression) funOrMethod;
      methodName = sysmlExpr.getMCQualifiedName().getPartsList().get(sysmlExpr.getMCQualifiedName().getPartsList().size() -1);
    }
    if(methodName != null) {
      String fqn = getFQNofMethodName(methodName);
      if(fqn != null) {
        return fqn;
      }
    }
    Log.warn("Encountered unknown function/method");
    return "";

  }

  public static ASTExpression getObject(ASTExpression lhs) {
    if(lhs instanceof ASTSysMLFunctionOperationExpression) {
      var sysmlExpr = (ASTSysMLFunctionOperationExpression) lhs;
      return sysmlExpr.getExpression();
    }
    else if(lhs instanceof ASTFieldAccessExpression) {
      ASTFieldAccessExpression fAExpr = (ASTFieldAccessExpression) lhs;
      return fAExpr.getExpression();
    }
    else if(lhs instanceof ASTNameExpression){
      return lhs;
    }
    return null;
  }
}
