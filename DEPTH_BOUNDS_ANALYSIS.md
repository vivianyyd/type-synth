# Analysis: Most Recent Change in Enumeration/Search Logic Related to Depth Bounds

## Summary

The most recent change in the enumeration or search logic related to depth bounds was introduced in commit **54ef558** (Merge pull request #30) on **February 17, 2026**.

## Key Finding

**Location:** `src/main/kotlin/oneast/searchstrategies/DFSEnumerator.kt`

**Line 53:** 
```kotlin
mustBeLeaf = sizeBound <= 1 || depth >= depthBound
```

## Details

### The Depth Bound Logic

In the `DFSEnumerator` class, which implements a depth-first search enumeration strategy, the depth bound is used to determine when a hole expansion must result in a leaf node. Specifically:

- When filling holes during enumeration, the algorithm tracks the depth of each hole
- At line 53, the `mustBeLeaf` parameter is set based on two conditions:
  1. `sizeBound <= 1`: The size budget is exhausted
  2. `depth >= depthBound`: The current depth has reached or exceeded the depth bound

This logic ensures that:
- The search does not expand beyond the specified depth limit
- Once a hole reaches the maximum depth, only leaf expansions are allowed
- This provides an important pruning mechanism for the search space

### Context in the Search Algorithm

The DFSEnumerator fills holes one at a time, prioritizing the shallowest fillable holes:

```kotlin
val (iToFill, holeWithDepth) = c.shallowestFillableHole() ?: error("Impossible")
val (hole, depth) = holeWithDepth
```

When expanding a hole, the depth bound is passed through to constrain which expansions are valid:

```kotlin
return hole.expansions(
    unification = unification,
    labelArities = c.labelArities,
    vars = c.types[iToFill].variables().size,
    topLevel = hole == c.types[iToFill],
    introduceBlanks = introduceBlanks,
    mustBeLeaf = sizeBound <= 1 || depth >= depthBound  // ← Key line
)
```

### Integration with the Search Framework

The depth bound is:
1. Configured in `Configuration` data class (`src/main/kotlin/oneast/OneMain.kt`, line 21)
2. Passed through the `SearchStrategy.candidates()` method (line 21 of `DFSEnumerator.kt`)
3. Used in iterative deepening search in `Search.solutions()` (lines 219-244 of `Search.kt`)

The iterative deepening loop in `Search.kt` gradually increases both size and depth bounds:

```kotlin
for (depth in 1..config.depthBound) {
    logger.start("Depth $depth for ${examples.names}")
    for (size in 1..config.sizeBound) {
        // ...enumerate with current depth and size bounds
    }
}
```

## Commit Information

- **Commit SHA:** 54ef558be6c9382c8457560b83dc18106a75fa56
- **Date:** February 17, 2026
- **Author:** Vivian Ding
- **Message:** Merge pull request #30 from vivianyyd/copilot/refactor-tests-to-use-helper

This appears to be the initial commit (grafted) that established the depth bound logic in the codebase.

## Related Files

1. **`src/main/kotlin/oneast/searchstrategies/DFSEnumerator.kt`** - Primary implementation of depth-bounded DFS enumeration
2. **`src/main/kotlin/oneast/Search.kt`** - Orchestrates the search with iterative deepening
3. **`src/main/kotlin/oneast/OneMain.kt`** - Configuration and entry point
4. **`src/main/kotlin/util/Configuration.kt`** - Configuration data structure for depth bounds

## Usage

The depth bound is typically set to 4 in the codebase:
- `src/main/kotlin/core/Enumerators.kt:29`: `depthBound = 4`
- `src/main/kotlin/oneast/OneMain.kt:21`: `depthBound = 4`
- Test files also use depth bounds of 3-4
