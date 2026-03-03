// package oneast
//
// import kotlin.test.Test
// import kotlin.test.assertEquals
//
// class DepthTest {
//    private fun dict(k: Type, v: Type) = NamedLabel(0, listOf(k, v))
//
//    private val holes = List(10) { TypeHole() }
//    private val a = Variable(0)
//    private val b = Variable(1)
//    private val put = Arrow(dict(a, b), Arrow(a, Arrow(b, dict(a, b))))
//
//    private val typeBlank = Blank(labelOnly = false)
//    private val labelBlank = Blank(labelOnly = true)
//
//    private val types: List<Pair<Type, Set<Pair<THole, Int>>>> =
//        listOf(
//            typeBlank to setOf(typeBlank to 0),
//            labelBlank to setOf(labelBlank to 0),
//            a to emptySet(),
//            holes[0] to setOf(holes[0] to 0),
//            /** D['a, 'b] -> 'a -> 'b -> D['a, 'b] */
//            put to emptySet(),
//            /** D['a, _] */
//            dict(a, holes[1]) to setOf(holes[1] to 1),
//            /** D[_, _] */
//            dict(holes[2], holes[3]) to setOf(holes[2] to 1, holes[3] to 1),
//            /** D[D['b, _], 'a] */
//            dict(dict(b, holes[4]), a) to setOf(holes[4] to 2),
//            /** D[D[_, _], 'a] */
//            dict(dict(holes[5], holes[6]), a) to setOf(holes[5] to 2, holes[6] to 2),
//            /** D['a, D[_, _]] */
//            dict(a, dict(holes[7], holes[8])) to setOf(holes[7] to 2, holes[8] to 2),
//            /** D[_, D[_, _]] */
//            dict(holes[9], dict(holes[7], holes[8])) to
//                    setOf(holes[9] to 1, holes[7] to 2, holes[8] to 2),
//            /** 'a -> 'b -> D[D['a, 'a], 'b] */
//            Arrow(a, Arrow(b, dict(dict(a, a), b))) to emptySet(),
//            /** 'a -> D[D['a, 'a], 'b] -> 'b */
//            Arrow(a, Arrow(dict(dict(a, a), b), b)) to emptySet(),
//            /** D[D['a, 'a], 'b] -> 'a -> 'b */
//            Arrow(dict(dict(a, a), b), Arrow(a, b)) to emptySet(),
//            /** 'a -> 'b -> D[D['a, 'a], _] */
//            Arrow(a, Arrow(b, dict(dict(a, a), holes[1]))) to setOf(holes[1] to 1),
//            /** 'a -> D[D['a, 'a], _] -> 'b */
//            Arrow(a, Arrow(dict(dict(a, a), holes[2]), b)) to setOf(holes[2] to 1),
//            /** D[D['a, _], 'b] -> 'a -> 'b */
//            Arrow(dict(dict(a, holes[3]), b), Arrow(a, b)) to setOf(holes[3] to 2),
//            /** D[D['a, _], 'b] -> _ -> 'b */
//            Arrow(dict(dict(a, holes[3]), b), Arrow(holes[4], b)) to
//                    setOf(holes[3] to 2, holes[4] to 0),
//            /** ('a -> D['a, _]) -> b -> D[_, 'b] */
//            Arrow(Arrow(a, dict(a, holes[5])), Arrow(b, dict(holes[6], b))) to
//                    setOf(holes[5] to 2, holes[6] to 1)
//        )
//
//    @Test
//    fun `Type allHolesWithDepth`() {
//        types.forEach { (ty, holesWithDepth) ->
//            assertEquals(holesWithDepth, ty.allHolesWithDepth(topLevel = true).toSet())
//        }
//    }
//
//    @Test
//    fun `Type shallowestFillableHole`() {
//        types.forEach { (ty, holesWithDepth) ->
//            val shallowest =
//                holesWithDepth.filter { it.first is TypeHole }.minByOrNull { it.second }
//            assertEquals(shallowest, ty.shallowestFillableHole(topLevel = true))
//        }
//    }
//
//    @Test
//    fun `Type maxParamDepth`() {
//        val depths = listOf(0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2)
//        types.unzip().first.zip(depths).forEach { (ty, depth) ->
//            assertEquals(depth, ty.maxParamDepth(countArrow = false))
//        }
//
//        assertEquals(0, Arrow(a, Arrow(a, b)).maxParamDepth(countArrow = false))
//        assertEquals(1, Arrow(Arrow(a, b), b).maxParamDepth(countArrow = false))
//    }
// }
