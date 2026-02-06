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

## If the `Test` interface moves into `src/test`
To avoid the `src/test/kotlin/test` repetition and to separate runnable tests from shared test
objects, prefer Gradle's test fixtures source set:

```
src
 ├─ testFixtures
 │   └─ kotlin
 │       └─ testfixtures/   ← shared fixtures & interfaces (e.g., Test.kt, DictTest, ...)
 └─ test
     └─ kotlin
         └─ …               ← runnable tests
```

Place the `Test` interface and reusable objects under `src/testFixtures/kotlin/testfixtures/` (or a
similar package). Runnable tests stay under `src/test/kotlin`. This keeps shared test-only code out
of production artifacts, avoids the double `test` path, and clearly distinguishes fixtures from test
cases.
