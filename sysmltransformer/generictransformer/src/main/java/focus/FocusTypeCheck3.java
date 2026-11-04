package focus;

import de.monticore.expressions.expressionsbasis._ast.ASTExpression;
import de.monticore.lang.sysmlv2._symboltable.ISysMLv2Scope;
import de.monticore.types.check.SymTypeExpression;
import de.monticore.types.mcstructuraltypes.types3.MCStructuralTypesTypeVisitor;
import de.monticore.types3.TypeCheck3Access;
import montibelle.focus.FocusTool;
import de.monticore.expressions.commonexpressions.types3.util.CommonExpressionsLValueRelations;
import de.monticore.expressions.expressionsbasis.types3.ExpressionBasisTypeVisitor;
import de.monticore.literals.mccommonliterals.types3.MCCommonLiteralsTypeVisitor;
import de.monticore.ocl.types3.OCLSymTypeRelations;
import de.monticore.types.mcbasictypes.types3.MCBasicTypesTypeVisitor;
import de.monticore.types.mccollectiontypes.types3.MCCollectionSymTypeRelations;
import de.monticore.types.mccollectiontypes.types3.MCCollectionTypesTypeVisitor;
import de.monticore.types.mcfunctiontypes.types3.MCFunctionTypesTypeVisitor;
import de.monticore.types3.Type4Ast;
import de.monticore.types3.TypeCheck3;
import de.monticore.types3.streams.StreamSymTypeRelations;
import de.monticore.types3.util.MapBasedTypeCheck3;
import de.monticore.visitor.ITraverser;
import de.se_rwth.commons.logging.Log;
import montibelle.focus.FocusMill;
import montibelle.focus._visitor.FocusTraverser;

public class FocusTypeCheck3 extends MapBasedTypeCheck3 {
  @Override
  protected SymTypeExpression _typeOf(ASTExpression expression) {
    var previousTypecheck = FocusTool.getPreviousTypecheck();
    if (expression.getEnclosingScope() instanceof ISysMLv2Scope
        && previousTypecheck != null) {
      return TypeCheck3Access.typeOf(previousTypecheck, expression);
    }
    return super._typeOf(expression);
  }

  public static void init() {
    initTC3Delegate();
    StreamSymTypeRelations.init();
    CommonExpressionsLValueRelations.init();
    MCCollectionSymTypeRelations.init();
  }

  public static void reset() {
    TypeCheck3.resetDelegate();
    StreamSymTypeRelations.reset();
    CommonExpressionsLValueRelations.reset();
    MCCollectionSymTypeRelations.reset();
    OCLSymTypeRelations.reset();
  }

  protected static void initTC3Delegate() {
    Log.trace("init FocusTypeCheck3", "TypeCheck setup");

    FocusTraverser typeTraverser = FocusMill.inheritanceTraverser();
    Type4Ast type4Ast = new Type4Ast();

    var forBasis = new ExpressionBasisTypeVisitor();
    forBasis.setType4Ast(type4Ast);
    typeTraverser.add4ExpressionsBasis(forBasis);

    var forLiterals = new MCCommonLiteralsTypeVisitor();
    forLiterals.setType4Ast(type4Ast);
    typeTraverser.add4MCCommonLiterals(forLiterals);

    var forBasicTypes = new MCBasicTypesTypeVisitor();
    forBasicTypes.setType4Ast(type4Ast);
    typeTraverser.add4MCBasicTypes(forBasicTypes);

    var forFocusTypes = new FocusMCBasicTypesVisitor();
    forFocusTypes.setType4Ast(type4Ast);
    typeTraverser.add4Focus(forFocusTypes);

    var forCollectionTypes = new MCCollectionTypesTypeVisitor();
    forCollectionTypes.setType4Ast(type4Ast);
    typeTraverser.add4MCCollectionTypes(forCollectionTypes);

    var forFunctionTypes = new MCFunctionTypesTypeVisitor();
    forFunctionTypes.setType4Ast(type4Ast);
    typeTraverser.add4MCFunctionTypes(forFunctionTypes);

    var forStructuralTypes = new MCStructuralTypesTypeVisitor();
    forStructuralTypes.setType4Ast(type4Ast);
    typeTraverser.add4MCStructuralTypes(forStructuralTypes);

    FocusTypeCheck3 sysmlTC3 = new FocusTypeCheck3(typeTraverser, type4Ast);
    sysmlTC3.setThisAsDelegate();
  }

  public FocusTypeCheck3(
      ITraverser typeTraverser, Type4Ast type4Ast) {
    super(typeTraverser, type4Ast);
  }
}
