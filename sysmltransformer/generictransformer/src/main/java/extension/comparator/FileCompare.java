package extension.comparator;

import org.junit.jupiter.api.extension.ExtendWith;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@Target({ ElementType.ANNOTATION_TYPE, ElementType.TYPE, ElementType.METHOD })
@Retention(RetentionPolicy.RUNTIME)
@ExtendWith(FileComparatorExtension.class)
public @interface FileCompare {

  String extension() default "";

  boolean recursive() default false;

  String base() default ".";

  String[] value() default {};
}
