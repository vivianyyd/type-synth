/** AI-generated code I was toying with */
/* =========================================
   Syntax
   ========================================= */
sealed interface Expr
data class Var(val name: String) : Expr
data class App(val fn: Expr, val arg: Expr) : Expr

/* Tiny DSL for building expressions */
fun v(n: String) = Var(n)
infix fun Expr.ap(e: Expr) = App(this, e)

/* =========================================
   Types & Schemes
   ========================================= */
sealed interface Type {
    fun ftv(): Set<String>
    fun show(): String
}

data class TVar(val name: String) : Type {
    override fun ftv() = setOf(name)
    override fun show() = name
}

data class TCon(val name: String) : Type {
    override fun ftv() = emptySet<String>()
    override fun show() = name
}

data class TFun(val from: Type, val to: Type) : Type {
    override fun ftv() = from.ftv() + to.ftv()
    override fun show(): String {
        fun parenIf(t: Type): String = when (t) {
            is TFun -> "(${t.show()})"
            else -> t.show()
        }
        return "${parenIf(from)} -> ${to.show()}"
    }
}

infix fun Type.arrow(to: Type) = TFun(this, to)

data class Scheme(val vars: Set<String>, val type: Type) {
    fun ftv(): Set<String> = type.ftv() - vars
    fun show(): String =
        if (vars.isEmpty()) type.show()
        else "forall ${vars.joinToString(" ")}. ${type.show()}"
}

/* =========================================
   Substitutions
   ========================================= */
typealias Subst = Map<String, Type>

val emptySubst: Subst = emptyMap()

fun Type.apply(s: Subst): Type = when (this) {
    is TVar -> s[this.name]?.apply(s) ?: this
    is TCon -> this
    is TFun -> TFun(this.from.apply(s), this.to.apply(s))
}

fun Scheme.apply(s: Subst): Scheme {
    // Do not substitute bound vars
    val filtered = s - vars
    return Scheme(vars, type.apply(filtered))
}

fun Map<String, Scheme>.apply(s: Subst): Map<String, Scheme> =
    mapValues { (_, sch) -> sch.apply(s) }

fun compose(s1: Subst, s2: Subst): Subst {
    // s1 ∘ s2 means apply s1 after s2
    val s2applied = s2.mapValues { (_, t) -> t.apply(s1) }
    return s2applied + s1
}

/* =========================================
   Fresh variable supply & instantiation
   ========================================= */
private object Fresh {
    private var counter = 0
    fun reset() {
        counter = 0
    }

    fun tv(prefix: String = "a"): TVar = TVar("$prefix${counter++}")
}

fun instantiate(s: Scheme): Type {
    if (s.vars.isEmpty()) return s.type
    val mapping: Subst = s.vars.associateWith { Fresh.tv().also { } }
    return s.type.apply(mapping)
}

/* =========================================
   Unification (with occurs check)
   ========================================= */
fun unify(t1: Type, t2: Type): Subst {
    val a = t1
    val b = t2
    return when {
        a is TFun && b is TFun -> {
            val s1 = unify(a.from, b.from)
            println(s1)
            val s2 = unify(a.to.apply(s1), b.to.apply(s1))
            compose(s2, s1)
        }
        a is TVar -> bind(a.name, b)
        b is TVar -> bind(b.name, a)
        a is TCon && b is TCon && a.name == b.name -> emptySubst
        else -> throw IllegalStateException("Cannot unify ${a.show()} with ${b.show()}")
    }
}

fun bind(name: String, t: Type): Subst {
    if (t == TVar(name)) return emptySubst
    if (t.ftv().contains(name))
        throw IllegalStateException("Occurs check failed: $name in ${t.show()}")
    return mapOf(name to t)
}

/* =========================================
   Inference (Algorithm W specialized)
   ========================================= */
data class InferResult(val subst: Subst, val type: Type)

fun infer(env: Map<String, Scheme>, e: Expr): InferResult = when (e) {
    is Var -> {
        val sch = env[e.name]
            ?: throw IllegalStateException("Unbound variable: ${e.name}")
        InferResult(emptySubst, instantiate(sch))
    }
//    is App -> {
//        val (s1, tFun) = infer(env, e.fn)
//        val (s2, tArg) = infer(env.apply(s1), e.arg)
//        val res = Fresh.tv()
//        val s3 = unify(tFun.apply(s2), TFun(tArg, res))
//        InferResult(compose(s3, compose(s2, s1)), res.apply(s3))
//    }
    is App -> {
        val (s1, tFun) = infer(env, e.fn)
        val (s2, tArg) = infer(env.apply(s1), e.arg)
        val res = Fresh.tv()
        // **** CRUCIAL FIX: apply s2 to BOTH sides before unifying ****
        val tFun2 = tFun.apply(s2)
        val tArg2 = tArg.apply(s2)

        val s3 = unify(tFun2, TFun(tArg2, res))
        InferResult(compose(s3, compose(s2, s1)), res.apply(s3))
    }
}

/* =========================================
   Helpers to build schemes and environments
   ========================================= */
fun tvar(n: String) = TVar(n)
fun tcon(n: String) = TCon(n)
fun fn(a: Type, b: Type) = TFun(a, b)

fun forall(vararg vs: String, type: Type) = Scheme(vs.toSet(), type)

/* =========================================
   Demo / quick tests
   ========================================= */
val TInt = tcon("Int")
val TBool = tcon("Bool")

// Environment mapping Strings to (possibly polymorphic) schemes
val baseEnv: Map<String, Scheme> = mapOf(
    // id : ∀a. a -> a
    "id" to forall("a", type = tvar("a") arrow tvar("a")),

    // const : ∀a b. a -> b -> a
    "const" to forall(
        "a", "b",
        type = tvar("a") arrow (tvar("b") arrow tvar("a"))
    ),

    // compose : ∀a b c. (b -> c) -> (a -> b) -> a -> c
    "compose" to forall(
        "a", "b", "c",
        type = (tvar("b") arrow tvar("c")) arrow
                ((tvar("a") arrow tvar("b")) arrow
                        (tvar("a") arrow tvar("c")))
    ),

    // succ : Int -> Int
    "succ" to Scheme(emptySet(), TInt arrow TInt),

    // isZero : Int -> Bool
    "isZero" to Scheme(emptySet(), TInt arrow TBool),

    // three : Int
    "three" to Scheme(emptySet(), TInt),

    // True : Bool
    "True" to Scheme(emptySet(), TBool),

    // ifThenElse : ∀a. Bool -> a -> a -> a
    "ifThenElse" to forall(
        "a",
        type = TBool arrow (tvar("a") arrow (tvar("a") arrow tvar("a")))
    ),

    "f" to forall("a", type = (tvar("a") arrow tvar("a")) arrow tvar("a") arrow tvar("a"))
)

/* -----------------------------------------
   Build a few example programs (only apps)
   ----------------------------------------- */
// id succ : should infer Int -> Int
val ex1 = v("id") ap v("succ")

// (compose succ succ) : Int -> Int
val ex2 = (v("compose") ap v("succ")) ap v("succ")

// (isZero (succ three)) : Bool
val ex3 = v("isZero") ap (v("succ") ap v("three"))

// (((ifThenElse) True) id) succ : (Int -> Int)
// Parsed as: ifThenElse True id succ
val ex4 = (((v("ifThenElse") ap v("True")) ap v("id")) ap v("succ"))

/* =========================================
   Run & print
   ========================================= */
fun typeOf(env: Map<String, Scheme>, expr: Expr): String {
    Fresh.reset()
    val (s, t) = infer(env, expr)
    return t.apply(s).show()
}

interface P {
    fun expansions(bound: Int): List<P>
    fun containsHole(): Boolean
}

object X : P {
    override fun toString() = "X"
    override fun expansions(bound: Int) = listOf(X)
    override fun containsHole() = false
}

data class K(val l: P, val r: P) : P {
    override fun toString() = "F($l,$r)"
    override fun containsHole() = l.containsHole() || r.containsHole()
    override fun expansions(bound: Int) =
        l.expansions(bound - 1).flatMap { le -> r.expansions(bound - 1).map { re -> K(le, re) } }
}

class Hole private constructor(val id: Int) : P {
    companion object {
        var fresh = 0
        fun new() = Hole(fresh++)
    }

    override fun containsHole() = true

    override fun toString() = "?$id"

    override fun expansions(bound: Int) = if (bound < 1) listOf(X) else listOf(X, K(new(), new()))
}

fun commitLeftmost(c: List<P>, recursionBound: Int): List<List<P>> {
    val (changeInd, leftmostNode) = c.withIndex().firstOrNull { (i, it) -> it.containsHole() } ?: return listOf(c)

    val optionsForLeftmost = leftmostNode.expansions(recursionBound)
    return optionsForLeftmost.flatMap { newLeftMost ->
        val newCandidate = c.mapIndexed { i, p -> if (changeInd == i) newLeftMost else p }
        commitLeftmost(newCandidate, recursionBound)
    }
}


fun main() {

    println(commitLeftmost(List(3) { Hole.new() }, 3).take(200).joinToString(separator = "\n"))


//    println("ex1 : ${typeOf(baseEnv, ex1)}") // Int -> Int
//    println("ex2 : ${typeOf(baseEnv, ex2)}") // Int -> Int
//    println("ex3 : ${typeOf(baseEnv, ex3)}") // Bool
//    println("ex4 : ${typeOf(baseEnv, ex4)}") // Int -> Int

//    println(typeOf(baseEnv, (v("f") ap v("id"))))
//    println(typeOf(baseEnv, (v("f") ap v("succ"))))
}
