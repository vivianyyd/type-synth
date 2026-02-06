# Testing layout

The test source set follows Gradle's standard `src/test/kotlin` root. The test fixtures live in the
`test` package (e.g., `src/test/kotlin/test/DictTest.kt`). This makes the path look like it repeats
`test`, but it keeps:

- The `Test` interface in `src/main/kotlin/test/Test.kt` under the same package so production code
  can refer to the interface without depending on test sources.
- The data-only fixtures in the test source set, so they don't ship with production artifacts but
  remain in the `test` package for existing imports and interoperability with `parseTest` utilities.

Renaming the package would require touching many references while providing no functional benefit,
so we keep the package name and rely on the standard source-set directory to separate production and
test code.
