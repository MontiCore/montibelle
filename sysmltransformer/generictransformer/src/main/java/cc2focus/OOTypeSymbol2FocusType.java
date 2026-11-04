package cc2focus;

import de.monticore.symbols.oosymbols._symboltable.OOTypeSymbol;
import de.monticore.types.mcbasictypes._ast.ASTMCType;
import focus.SymType2MCTypePrinter;
import jline.internal.Log;
import montibelle.focus.FocusMill;
import montibelle.focus._ast.ASTFieldBuilder;
import montibelle.focus._ast.ASTEnumType;
import montibelle.focus._ast.ASTEnumTypeBuilder;
import montibelle.focus._ast.ASTUserDefinedStruct;
import montibelle.focus._ast.ASTUserDefinedStructBuilder;
import trafos.ITypePrinter;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.util.stream.Collectors;

public class OOTypeSymbol2FocusType {

  public static ASTEnumType buildEnum(OOTypeSymbol symbol) {
    if (symbol.isIsEnum()) {
      return new ASTEnumTypeBuilder()
          .setName(symbol.getFullName().replace('.','_'))
          .setLiteralsList(
              symbol.getFieldList().stream()
                  .map(field -> field.getName())
                  .collect(Collectors.toList())
          )
          .setFinite(true)
          .build();
    }
    else {
      Log.error("0xF0C01 Internal error, attempted to transform a "
          + "struct to an enum");
      return null;
    }
  }

  public static ASTUserDefinedStruct buildStruct(
      OOTypeSymbol symbol,
      ITypePrinter typePrinter
  ) {
    if (symbol.isIsEnum()) {
      Log.error("0xF0C02 Internal error, attempted to transform an "
          + "enum to a struct");
    }
    var printer = new SymType2MCTypePrinter();
    return new ASTUserDefinedStructBuilder()
        .setName(symbol.getFullName().replace('.','_'))
        .setFieldsList(symbol.getFieldList().stream()
            .map(field -> {
              ASTMCType mcType;
              try {
                mcType = FocusMill.parser().parse_StringMCType(
                    printer.print(field.getType())).get();
              } catch (IOException e) {
                throw new UncheckedIOException(
                    "Cannot parse type of field " + field.getName(), e);
              }
              return new ASTFieldBuilder()
                  .setName(field.getName())
                  .setMCType(mcType)
                  .setPattern(field.getName() + "_pattern")
                  .build();
            })
            .collect(Collectors.toList()))
        .build();
  }

}
