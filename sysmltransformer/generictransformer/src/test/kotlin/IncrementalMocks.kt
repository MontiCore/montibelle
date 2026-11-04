import de.monticore.ast.Comment
import de.monticore.cardinality._symboltable.ICardinalityScope
import de.monticore.expressions.expressionsbasis._symboltable.IExpressionsBasisScope
import de.monticore.lang.componentconnector._ast.ASTStateSpace
import de.monticore.lang.componentconnector._symboltable.IComponentConnectorScope
import de.monticore.lang.componentconnector._visitor.ComponentConnectorTraverser
import de.monticore.literals.mccommonliterals._symboltable.IMCCommonLiteralsScope
import de.monticore.literals.mcliteralsbasis._symboltable.IMCLiteralsBasisScope
import de.monticore.mcbasics._symboltable.IMCBasicsScope
import de.monticore.symbols.basicsymbols._ast.ASTVariable
import de.monticore.symbols.basicsymbols._symboltable.IBasicSymbolsScope
import de.monticore.symbols.basicsymbols._symboltable.VariableSymbol
import de.monticore.symbols.compsymbols._symboltable.ICompSymbolsScope
import de.monticore.types.mcbasictypes._ast.ASTMCQualifiedName
import de.monticore.types.mcbasictypes._ast.ASTMCQualifiedNameBuilder
import de.monticore.types.mcbasictypes._symboltable.IMCBasicTypesScope
import de.se_rwth.commons.SourcePosition
import java.util.*
import java.util.function.Consumer
import java.util.function.Predicate
import java.util.function.UnaryOperator
import java.util.stream.Stream

class ASTStateSpaceMock(
  private val states: List<String>): ASTStateSpace {

  override fun getEnclosingScope(): IComponentConnectorScope {
    return enclosingScope
  }

  override fun getStatesList(): List<ASTMCQualifiedName> {
    return states.map { ASTMCQualifiedNameBuilder().setPartsList(it.split('.')).build() }
  }

  override fun equalAttributes(o: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun equalsWithComments(o: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun deepEquals(o: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun deepEquals(o: Any?, forceSameOrder: Boolean): Boolean {
    TODO("Not yet implemented")
  }

  override fun deepEqualsWithComments(o: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun deepEqualsWithComments(o: Any?, forceSameOrder: Boolean): Boolean {
    TODO("Not yet implemented")
  }

  override fun deepClone(): ASTStateSpace {
    TODO("Not yet implemented")
  }

  override fun get_SourcePositionEnd(): SourcePosition {
    TODO("Not yet implemented")
  }

  override fun set_SourcePositionEnd(end: SourcePosition?) {
    TODO("Not yet implemented")
  }

  override fun set_SourcePositionEndAbsent() {
    TODO("Not yet implemented")
  }

  override fun isPresent_SourcePositionEnd(): Boolean {
    TODO("Not yet implemented")
  }

  override fun get_SourcePositionStart(): SourcePosition {
    TODO("Not yet implemented")
  }

  override fun set_SourcePositionStart(start: SourcePosition?) {
    TODO("Not yet implemented")
  }

  override fun set_SourcePositionStartAbsent() {
    TODO("Not yet implemented")
  }

  override fun isPresent_SourcePositionStart(): Boolean {
    TODO("Not yet implemented")
  }

  override fun clear_PreComments() {
    TODO("Not yet implemented")
  }

  override fun add_PreComment(precomment: Comment?): Boolean {
    TODO("Not yet implemented")
  }

  override fun add_PreComment(index: Int, precomment: Comment?) {
    TODO("Not yet implemented")
  }

  override fun addAll_PreComments(precomments: MutableCollection<Comment>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun addAll_PreComments(index: Int, precomments: MutableCollection<Comment>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun contains_PreComment(element: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun containsAll_PreComments(element: MutableCollection<*>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun isEmpty_PreComments(): Boolean {
    TODO("Not yet implemented")
  }

  override fun iterator_PreComments(): MutableIterator<Comment> {
    TODO("Not yet implemented")
  }

  override fun remove_PreComment(element: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun remove_PreComment(index: Int): Comment {
    TODO("Not yet implemented")
  }

  override fun removeAll_PreComments(element: MutableCollection<*>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun retainAll_PreComments(element: MutableCollection<*>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun size_PreComments(): Int {
    TODO("Not yet implemented")
  }

  override fun toArray_PreComments(array: Array<out Comment>?): Array<Comment> {
    TODO("Not yet implemented")
  }

  override fun toArray_PreComments(): Array<Any> {
    TODO("Not yet implemented")
  }

  override fun removeIf_PreComment(filter: Predicate<in Comment>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun spliterator_PreComments(): Spliterator<Comment> {
    TODO("Not yet implemented")
  }

  override fun stream_PreComments(): Stream<Comment> {
    TODO("Not yet implemented")
  }

  override fun parallelStream_PreComments(): Stream<Comment> {
    TODO("Not yet implemented")
  }

  override fun forEach_PreComments(action: Consumer<in Comment>?) {
    TODO("Not yet implemented")
  }

  override fun get_PreComment(index: Int): Comment {
    TODO("Not yet implemented")
  }

  override fun indexOf_PreComment(element: Any?): Int {
    TODO("Not yet implemented")
  }

  override fun lastIndexOf_PreComment(element: Any?): Int {
    TODO("Not yet implemented")
  }

  override fun equals_PreComments(element: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun hashCode_PreComments(): Int {
    TODO("Not yet implemented")
  }

  override fun listIterator_PreComments(): MutableListIterator<Comment> {
    TODO("Not yet implemented")
  }

  override fun listIterator_PreComments(index: Int): MutableListIterator<Comment> {
    TODO("Not yet implemented")
  }

  override fun subList_PreComments(start: Int, end: Int): MutableList<Comment> {
    TODO("Not yet implemented")
  }

  override fun replaceAll_PreComments(operator: UnaryOperator<Comment>?) {
    TODO("Not yet implemented")
  }

  override fun sort_PreComments(comparator: java.util.Comparator<in Comment>?) {
    TODO("Not yet implemented")
  }

  override fun set_PreCommentList(preComments: MutableList<Comment>?) {
    TODO("Not yet implemented")
  }

  override fun get_PreCommentList(): MutableList<Comment> {
    TODO("Not yet implemented")
  }

  override fun set_PreComment(index: Int, precomment: Comment?): Comment {
    TODO("Not yet implemented")
  }

  override fun clear_PostComments() {
    TODO("Not yet implemented")
  }

  override fun add_PostComment(postcomment: Comment?): Boolean {
    TODO("Not yet implemented")
  }

  override fun add_PostComment(index: Int, postcomment: Comment?) {
    TODO("Not yet implemented")
  }

  override fun addAll_PostComments(postcomments: MutableCollection<Comment>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun addAll_PostComments(index: Int, postcomments: MutableCollection<Comment>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun contains_PostComment(element: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun containsAll_PostComments(element: MutableCollection<*>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun isEmpty_PostComments(): Boolean {
    TODO("Not yet implemented")
  }

  override fun iterator_PostComments(): MutableIterator<Comment> {
    TODO("Not yet implemented")
  }

  override fun remove_PostComment(element: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun remove_PostComment(index: Int): Comment {
    TODO("Not yet implemented")
  }

  override fun removeAll_PostComments(element: MutableCollection<*>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun retainAll_PostComments(element: MutableCollection<*>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun size_PostComments(): Int {
    TODO("Not yet implemented")
  }

  override fun toArray_PostComments(array: Array<out Comment>?): Array<Comment> {
    TODO("Not yet implemented")
  }

  override fun toArray_PostComments(): Array<Any> {
    TODO("Not yet implemented")
  }

  override fun removeIf_PostComment(filter: Predicate<in Comment>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun spliterator_PostComments(): Spliterator<Comment> {
    TODO("Not yet implemented")
  }

  override fun stream_PostComments(): Stream<Comment> {
    TODO("Not yet implemented")
  }

  override fun parallelStream_PostComments(): Stream<Comment> {
    TODO("Not yet implemented")
  }

  override fun forEach_PostComments(action: Consumer<in Comment>?) {
    TODO("Not yet implemented")
  }

  override fun get_PostComment(index: Int): Comment {
    TODO("Not yet implemented")
  }

  override fun indexOf_PostComment(element: Any?): Int {
    TODO("Not yet implemented")
  }

  override fun lastIndexOf_PostComment(element: Any?): Int {
    TODO("Not yet implemented")
  }

  override fun equals_PostComments(element: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun hashCode_PostComments(): Int {
    TODO("Not yet implemented")
  }

  override fun listIterator_PostComments(): MutableListIterator<Comment> {
    TODO("Not yet implemented")
  }

  override fun listIterator_PostComments(index: Int): MutableListIterator<Comment> {
    TODO("Not yet implemented")
  }

  override fun subList_PostComments(start: Int, end: Int): MutableList<Comment> {
    TODO("Not yet implemented")
  }

  override fun replaceAll_PostComments(operator: UnaryOperator<Comment>?) {
    TODO("Not yet implemented")
  }

  override fun sort_PostComments(comparator: java.util.Comparator<in Comment>?) {
    TODO("Not yet implemented")
  }

  override fun set_PostCommentList(postComments: MutableList<Comment>?) {
    TODO("Not yet implemented")
  }

  override fun get_PostCommentList(): MutableList<Comment> {
    TODO("Not yet implemented")
  }

  override fun set_PostComment(index: Int, postcomment: Comment?): Comment {
    TODO("Not yet implemented")
  }

  override fun accept(visitor: ComponentConnectorTraverser?) {
    TODO("Not yet implemented")
  }

  override fun containsVariablesSymbol(element: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun containsAllVariablesSymbol(collection: MutableCollection<*>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun isEmptyVariablesSymbol(): Boolean {
    TODO("Not yet implemented")
  }

  override fun iteratorVariablesSymbol(): MutableIterator<Optional<VariableSymbol>> {
    TODO("Not yet implemented")
  }

  override fun sizeVariablesSymbol(): Int {
    TODO("Not yet implemented")
  }

  override fun toArrayVariablesSymbol(array: Array<out Optional<VariableSymbol>>?): Array<Optional<VariableSymbol>> {
    TODO("Not yet implemented")
  }

  override fun toArrayVariablesSymbol(): Array<Any> {
    TODO("Not yet implemented")
  }

  override fun spliteratorVariablesSymbol(): Spliterator<Optional<VariableSymbol>> {
    TODO("Not yet implemented")
  }

  override fun streamVariablesSymbol(): Stream<Optional<VariableSymbol>> {
    TODO("Not yet implemented")
  }

  override fun parallelStreamVariablesSymbol(): Stream<Optional<VariableSymbol>> {
    TODO("Not yet implemented")
  }

  override fun getVariablesSymbol(index: Int): Optional<VariableSymbol> {
    TODO("Not yet implemented")
  }

  override fun indexOfVariablesSymbol(element: Any?): Int {
    TODO("Not yet implemented")
  }

  override fun lastIndexOfVariablesSymbol(element: Any?): Int {
    TODO("Not yet implemented")
  }

  override fun equalsVariablesSymbol(o: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun hashCodeVariablesSymbol(): Int {
    TODO("Not yet implemented")
  }

  override fun listIteratorVariablesSymbol(): MutableListIterator<Optional<VariableSymbol>> {
    TODO("Not yet implemented")
  }

  override fun listIteratorVariablesSymbol(index: Int): MutableListIterator<Optional<VariableSymbol>> {
    TODO("Not yet implemented")
  }

  override fun subListVariablesSymbol(start: Int, end: Int): MutableList<Optional<VariableSymbol>> {
    TODO("Not yet implemented")
  }

  override fun getVariablesSymbolList(): MutableList<Optional<VariableSymbol>> {
    TODO("Not yet implemented")
  }


  override fun containsVariablesDefinition(element: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun containsAllVariablesDefinition(collection: MutableCollection<*>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun isEmptyVariablesDefinition(): Boolean {
    TODO("Not yet implemented")
  }

  override fun iteratorVariablesDefinition(): MutableIterator<Optional<ASTVariable>> {
    TODO("Not yet implemented")
  }

  override fun sizeVariablesDefinition(): Int {
    TODO("Not yet implemented")
  }

  override fun toArrayVariablesDefinition(array: Array<out Optional<ASTVariable>>?): Array<Optional<ASTVariable>> {
    TODO("Not yet implemented")
  }

  override fun toArrayVariablesDefinition(): Array<Any> {
    TODO("Not yet implemented")
  }

  override fun spliteratorVariablesDefinition(): Spliterator<Optional<ASTVariable>> {
    TODO("Not yet implemented")
  }

  override fun streamVariablesDefinition(): Stream<Optional<ASTVariable>> {
    TODO("Not yet implemented")
  }

  override fun parallelStreamVariablesDefinition(): Stream<Optional<ASTVariable>> {
    TODO("Not yet implemented")
  }

  override fun getVariablesDefinition(index: Int): Optional<ASTVariable> {
    TODO("Not yet implemented")
  }

  override fun indexOfVariablesDefinition(element: Any?): Int {
    TODO("Not yet implemented")
  }

  override fun lastIndexOfVariablesDefinition(element: Any?): Int {
    TODO("Not yet implemented")
  }

  override fun equalsVariablesDefinition(o: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun hashCodeVariablesDefinition(): Int {
    TODO("Not yet implemented")
  }

  override fun listIteratorVariablesDefinition(): MutableListIterator<Optional<ASTVariable>> {
    TODO("Not yet implemented")
  }

  override fun listIteratorVariablesDefinition(index: Int): MutableListIterator<Optional<ASTVariable>> {
    TODO("Not yet implemented")
  }

  override fun subListVariablesDefinition(start: Int, end: Int): MutableList<Optional<ASTVariable>> {
    TODO("Not yet implemented")
  }

  override fun getVariablesDefinitionList(): MutableList<Optional<ASTVariable>> {
    TODO("Not yet implemented")
  }

  override fun containsStates(element: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun containsAllStates(collection: MutableCollection<*>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun isEmptyStates(): Boolean {
    TODO("Not yet implemented")
  }

  override fun iteratorStates(): MutableIterator<ASTMCQualifiedName> {
    TODO("Not yet implemented")
  }

  override fun sizeStates(): Int {
    TODO("Not yet implemented")
  }

  override fun toArrayStates(array: Array<out ASTMCQualifiedName>?): Array<ASTMCQualifiedName> {
    TODO("Not yet implemented")
  }

  override fun toArrayStates(): Array<Any> {
    TODO("Not yet implemented")
  }

  override fun spliteratorStates(): Spliterator<ASTMCQualifiedName> {
    TODO("Not yet implemented")
  }

  override fun streamStates(): Stream<ASTMCQualifiedName> {
    TODO("Not yet implemented")
  }

  override fun parallelStreamStates(): Stream<ASTMCQualifiedName> {
    TODO("Not yet implemented")
  }

  override fun getStates(index: Int): ASTMCQualifiedName {
    TODO("Not yet implemented")
  }

  override fun indexOfStates(element: Any?): Int {
    TODO("Not yet implemented")
  }

  override fun lastIndexOfStates(element: Any?): Int {
    TODO("Not yet implemented")
  }

  override fun equalsStates(o: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun hashCodeStates(): Int {
    TODO("Not yet implemented")
  }

  override fun listIteratorStates(): MutableListIterator<ASTMCQualifiedName> {
    TODO("Not yet implemented")
  }

  override fun listIteratorStates(index: Int): MutableListIterator<ASTMCQualifiedName> {
    TODO("Not yet implemented")
  }

  override fun subListStates(start: Int, end: Int): MutableList<ASTMCQualifiedName> {
    TODO("Not yet implemented")
  }

  override fun clearStates() {
    TODO("Not yet implemented")
  }

  override fun addStates(element: ASTMCQualifiedName?): Boolean {
    TODO("Not yet implemented")
  }

  override fun addStates(index: Int, element: ASTMCQualifiedName?) {
    TODO("Not yet implemented")
  }

  override fun addAllStates(collection: MutableCollection<out ASTMCQualifiedName>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun addAllStates(index: Int, collection: MutableCollection<out ASTMCQualifiedName>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun removeStates(element: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun removeStates(index: Int): ASTMCQualifiedName {
    TODO("Not yet implemented")
  }

  override fun removeAllStates(collection: MutableCollection<*>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun retainAllStates(collection: MutableCollection<*>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun removeIfStates(filter: Predicate<in ASTMCQualifiedName>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun forEachStates(action: Consumer<in ASTMCQualifiedName>?) {
    TODO("Not yet implemented")
  }

  override fun setStates(index: Int, element: ASTMCQualifiedName?): ASTMCQualifiedName {
    TODO("Not yet implemented")
  }

  override fun replaceAllStates(operator: UnaryOperator<ASTMCQualifiedName>?) {
    TODO("Not yet implemented")
  }

  override fun sortStates(comparator: java.util.Comparator<in ASTMCQualifiedName>?) {
    TODO("Not yet implemented")
  }

  override fun setStatesList(states: MutableList<ASTMCQualifiedName>?) {
    TODO("Not yet implemented")
  }

  override fun containsVariables(element: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun containsAllVariables(collection: MutableCollection<*>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun isEmptyVariables(): Boolean {
    TODO("Not yet implemented")
  }

  override fun iteratorVariables(): MutableIterator<String> {
    TODO("Not yet implemented")
  }

  override fun sizeVariables(): Int {
    TODO("Not yet implemented")
  }

  override fun toArrayVariables(array: Array<out String>?): Array<String> {
    TODO("Not yet implemented")
  }

  override fun toArrayVariables(): Array<Any> {
    TODO("Not yet implemented")
  }

  override fun spliteratorVariables(): Spliterator<String> {
    TODO("Not yet implemented")
  }

  override fun streamVariables(): Stream<String> {
    TODO("Not yet implemented")
  }

  override fun parallelStreamVariables(): Stream<String> {
    TODO("Not yet implemented")
  }

  override fun getVariables(index: Int): String {
    TODO("Not yet implemented")
  }

  override fun indexOfVariables(element: Any?): Int {
    TODO("Not yet implemented")
  }

  override fun lastIndexOfVariables(element: Any?): Int {
    TODO("Not yet implemented")
  }

  override fun equalsVariables(o: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun hashCodeVariables(): Int {
    TODO("Not yet implemented")
  }

  override fun listIteratorVariables(): MutableListIterator<String> {
    TODO("Not yet implemented")
  }

  override fun listIteratorVariables(index: Int): MutableListIterator<String> {
    TODO("Not yet implemented")
  }

  override fun subListVariables(start: Int, end: Int): MutableList<String> {
    TODO("Not yet implemented")
  }

  override fun getVariablesList(): MutableList<String> {
    TODO("Not yet implemented")
  }

  override fun clearVariables() {
    TODO("Not yet implemented")
  }

  override fun addVariables(element: String?): Boolean {
    TODO("Not yet implemented")
  }

  override fun addVariables(index: Int, element: String?) {
    TODO("Not yet implemented")
  }

  override fun addAllVariables(collection: MutableCollection<out String>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun addAllVariables(index: Int, collection: MutableCollection<out String>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun removeVariables(element: Any?): Boolean {
    TODO("Not yet implemented")
  }

  override fun removeVariables(index: Int): String {
    TODO("Not yet implemented")
  }

  override fun removeAllVariables(collection: MutableCollection<*>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun retainAllVariables(collection: MutableCollection<*>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun removeIfVariables(filter: Predicate<in String>?): Boolean {
    TODO("Not yet implemented")
  }

  override fun forEachVariables(action: Consumer<in String>?) {
    TODO("Not yet implemented")
  }

  override fun setVariables(index: Int, element: String?): String {
    TODO("Not yet implemented")
  }

  override fun replaceAllVariables(operator: UnaryOperator<String>?) {
    TODO("Not yet implemented")
  }

  override fun sortVariables(comparator: java.util.Comparator<in String>?) {
    TODO("Not yet implemented")
  }

  override fun setVariablesList(variables: MutableList<String>?) {
    TODO("Not yet implemented")
  }

  override fun setEnclosingScope(enclosingScope: IComponentConnectorScope?) {
    TODO("Not yet implemented")
  }

  override fun setEnclosingScope(enclosingScope: IMCBasicTypesScope?) {
    TODO("Not yet implemented")
  }

  override fun setEnclosingScope(enclosingScope: IExpressionsBasisScope?) {
    TODO("Not yet implemented")
  }

  override fun setEnclosingScope(enclosingScope: ICompSymbolsScope?) {
    TODO("Not yet implemented")
  }

  override fun setEnclosingScope(enclosingScope: ICardinalityScope?) {
    TODO("Not yet implemented")
  }

  override fun setEnclosingScope(enclosingScope: IMCBasicsScope?) {
    TODO("Not yet implemented")
  }

  override fun setEnclosingScope(enclosingScope: IMCLiteralsBasisScope?) {
    TODO("Not yet implemented")
  }

  override fun setEnclosingScope(enclosingScope: IBasicSymbolsScope?) {
    TODO("Not yet implemented")
  }

  override fun setEnclosingScope(enclosingScope: IMCCommonLiteralsScope?) {
    TODO("Not yet implemented")
  }

}
