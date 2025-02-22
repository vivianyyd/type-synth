package util

fun <T> equivalenceClasses(elems: Collection<T>, equals: (T, T) -> Boolean): Set<Set<T>> {
    val result = mutableSetOf<MutableSet<T>>()  // Invariant: No element of the set is empty
    elems.forEach { elem ->
        var foundOne = false
        for (eqClass in result) {
            if (equals(elem, eqClass.first())) {
                eqClass.add(elem)
                foundOne = true
                break
            }
        }
        if (!foundOne) result.add(mutableSetOf(elem))
    }
    return result
}

fun <T> reflexiveNaryProduct(set: List<T>, n: Int): Sequence<List<T>> {
    TODO()
//    return naryCartesianProduct((1..n).map { set })
    /*
    fun help(currProd: List<T>, setInd: Int): Sequence<List<T>> = sequence {
        var i = setInd
        if (++i >= sets.size) {

            yield(currProd)
        } else {
            val next = sets[i]
            for (element in next) {
                yieldAll(help(currProd + element, i))
            }
        }
    }
    return help(listOf(), -1)
     */


/*
function crossProduct(sets) {
  var n = sets.length, carets = [], args = [];

  function init() {
    for (var i = 0; i < n; i++) {
      carets[i] = 0;
      args[i] = sets[i][0];
    }
  }

  function next() {
    if (!args.length) {
      init();
      return true;
    }
    var i = n - 1;
    carets[i]++;
    if (carets[i] < sets[i].length) {
      args[i] = sets[i][carets[i]];
      return true;
    }
    while (carets[i] >= sets[i].length) {
      if (i == 0) {
        return false;
      }
      carets[i] = 0;
      args[i] = sets[i][0];
      carets[--i]++;
    }
    args[i] = sets[i][carets[i]];
    return true;
  }

  return {
    next: next,
    do: function (block, _context) {
      return block.apply(_context, args);
    }
  }
}
     */
}

fun <T> naryCartesianProduct(sets: List<List<T>>): Set<List<T>> {
    if (sets.isEmpty()) return setOf()
    var result = sets[0].map { listOf(it) }.toSet()
    var rest = sets.drop(1)
    while (rest.isNotEmpty()) {
        result = binaryCartesianProduct(result, rest[0])
        rest = rest.drop(1)
    }
    return result
}

fun <T> binaryCartesianProduct(a: Set<List<T>>, b: Collection<T>): Set<List<T>> {
    val result = mutableSetOf<List<T>>()
    a.forEach { ita -> b.forEach { itb -> result.add(ita + itb) } }
    return result
//    return a.flatMap { ita -> b.asSequence().map { itb -> ita + itb } }
}
