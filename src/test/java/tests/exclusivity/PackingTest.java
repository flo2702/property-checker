package tests.exclusivity;

import edu.kit.kastel.property.checker.PropertyChecker;
import org.checkerframework.framework.test.CheckerFrameworkPerDirectoryTest;
import org.junit.runners.Parameterized.Parameters;
import tests.property.PropertyCheckerTest;

import java.io.File;
import java.util.List;

/**
 * Test runner for tests of the Exclusivity Checker.
 *
 * <p>Tests appear as Java files in the {@code tests/exclusivity} folder. To add a new test case,
 * create a Java file in that directory. The file contains "// ::" comments to indicate expected
 * errors and warnings; see
 * https://github.com/typetools/checker-framework/blob/master/checker/tests/README .
 */
public class PackingTest extends PropertyCheckerTest {
    public PackingTest(List<File> testFiles) {
        super(
                testFiles,
                null,
                "tests/exclusivity/packing");
    }

    @Parameters
    public static String[] getTestDirs() {
        return new String[] {"exclusivity/packing"};
    }
}