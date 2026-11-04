package montibelle.transformer.sysml.util

object IsabelleNameCodec {

  fun encode(name: String): String {
    val result = StringBuilder()

    name.codePoints().forEach { codePoint ->
      when {
        isAsciiLetterOrDigit(codePoint) -> {
          result.appendCodePoint(codePoint)
        }

        codePoint == '_'.code -> {
          result.append("__")
        }

        else -> {
          val hexadecimal = codePoint
            .toString(16)
            .uppercase()
            .padStart(4, '0')

          result
            .append("_u")
            .append(hexadecimal)
            .append('_')
        }
      }
    }

    return result.toString()
  }

  fun decode(encodedName: String): String {
    val result = StringBuilder()
    var index = 0

    while (index < encodedName.length) {
      when {
        encodedName.startsWith("__", index) -> {
          result.append('_')
          index += 2
        }

        encodedName.startsWith("_u", index) -> {
          val endIndex = encodedName.indexOf(
            '_',
            startIndex = index + 2
          )

          require(endIndex >= 0) {
            "Missing closing underscore at index $index"
          }
          val hexadecimal = encodedName.substring(
            index + 2,
            endIndex
          )

          require(
            hexadecimal.length >= 4 &&
                hexadecimal.all { it.isHexadecimalDigit() }
          ) {
            "Invalid Unicode encoding at index $index"
          }

          val codePoint = hexadecimal.toInt(16)

          require(
            Character.isValidCodePoint(codePoint) &&
                codePoint !in 0xD800..0xDFFF
          ) {
            "Invalid Unicode code point U+$hexadecimal"
          }

          result.appendCodePoint(codePoint)

          index = endIndex + 1
        }

        isAsciiLetterOrDigit(encodedName[index].code) -> {
          result.append(encodedName[index])
          index++
        }

        else -> {
          throw IllegalArgumentException(
            "Invalid encoded character '${encodedName[index]}' " +
                "at index $index"
          )
        }
      }
    }

    return result.toString()
  }

  private fun isAsciiLetterOrDigit(codePoint: Int): Boolean {
    return codePoint in 'a'.code..'z'.code ||
        codePoint in 'A'.code..'Z'.code ||
        codePoint in '0'.code..'9'.code
  }

  private fun Char.isHexadecimalDigit(): Boolean {
    return this in '0'..'9' ||
        this in 'a'..'f' ||
        this in 'A'..'F'
  }
}
