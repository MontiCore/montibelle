package extension.util;

import org.junit.jupiter.api.extension.ExtensionContext;
import org.junit.platform.commons.support.AnnotationSupport;

import java.lang.annotation.Annotation;
import java.util.Optional;

public class ExtensionUtil {

  public static <T extends Annotation> Optional<T> findAnnotation(
      ExtensionContext extensionContext, Class<T> annotation) {
    return AnnotationSupport.findAnnotation(extensionContext.getElement(), annotation)
        .or(() -> AnnotationSupport.findAnnotation(
            extensionContext.getParent().flatMap(ExtensionContext::getElement), annotation));
  }
}
