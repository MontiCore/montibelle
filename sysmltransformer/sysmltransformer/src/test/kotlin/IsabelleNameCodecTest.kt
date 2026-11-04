import montibelle.transformer.sysml.util.IsabelleNameCodec
import org.assertj.core.api.Assertions.assertThat
import org.assertj.core.api.Assertions.assertThatThrownBy
import org.junit.jupiter.api.Test

class IsabelleNameCodecTest {

  @Test
  fun testEncodeAsciiName() {
    assertThat(IsabelleNameCodec.encode("Apollo11"))
      .isEqualTo("Apollo11")
  }

  @Test
  fun testEncodeUnderscore() {
    assertThat(IsabelleNameCodec.encode("my_name"))
      .isEqualTo("my__name")
  }

  @Test
  fun testEncodeSpecialCharacters() {
    assertThat(IsabelleNameCodec.encode("F-1"))
      .isEqualTo("F_u002D_1")

    assertThat(IsabelleNameCodec.encode("Roger B. Chaffee"))
      .isEqualTo(
        "Roger_u0020_B_u002E__u0020_Chaffee"
      )
  }

  @Test
  fun testDecodeName() {
    assertThat(
      IsabelleNameCodec.decode(
        "Roger_u0020_B_u002E__u0020_Chaffee"
      )
    ).isEqualTo("Roger B. Chaffee")
  }

  @Test
  fun testRoundTrip() {
    val originalNames = listOf(
      "",
      "Apollo11",
      "my_name",
      "F-1",
      "Roger B. Chaffee",
      "A_u0020_B",
      "äöü"
    )

    originalNames.forEach { originalName ->
      val encodedName = IsabelleNameCodec.encode(originalName)
      val decodedName = IsabelleNameCodec.decode(encodedName)

      assertThat(decodedName)
        .describedAs("Round trip for '$originalName'")
        .isEqualTo(originalName)
    }
  }

  @Test
  fun testEncodingIsUnambiguous() {
    val nameWithSpace = "A B"
    val nameWithUnicodeLikeText = "A_u0020_B"

    assertThat(IsabelleNameCodec.encode(nameWithSpace))
      .isEqualTo("A_u0020_B")

    assertThat(IsabelleNameCodec.encode(nameWithUnicodeLikeText))
      .isEqualTo("A__u0020__B")

    assertThat(IsabelleNameCodec.encode(nameWithSpace))
      .isNotEqualTo(
        IsabelleNameCodec.encode(nameWithUnicodeLikeText)
      )
  }

  @Test
  fun testRejectsMissingClosingUnderscore() {
    assertThatThrownBy {
      IsabelleNameCodec.decode("_u0020")
    }.isInstanceOf(IllegalArgumentException::class.java)
  }

  @Test
  fun testRejectsInvalidHexadecimalSequence() {
    assertThatThrownBy {
      IsabelleNameCodec.decode("_uZZZZ_")
    }.isInstanceOf(IllegalArgumentException::class.java)
  }

  @Test
  fun testRepresentativeNamesHaveUniqueEncodings() {
    val names = listOf(
      "A B",
      "A_u0020_B",
      "A.B",
      "A_B",
      "A-B",
      "A_u002E_B",
      "ä",
      "_u00E4_"
    )

    val encodedNames = names.map(IsabelleNameCodec::encode)

    assertThat(encodedNames).doesNotHaveDuplicates()

    names.forEach { name ->
      assertThat(IsabelleNameCodec.decode(IsabelleNameCodec.encode(name)))
        .isEqualTo(name)
    }
  }
}
