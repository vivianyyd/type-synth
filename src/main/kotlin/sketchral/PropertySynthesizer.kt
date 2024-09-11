package sketchral

import util.*

typealias Lambdas = Map<String, String>
typealias Examples = List<Example>

class PropertySynthesizer(function: Func, query: Query) {
    private val inputFactory = InputFactory(function, query)

    // TODO timeout variable up here and make each step check for timeout

    private val phiTruth = null//"out = true" // Synthesized property. Might delete
    private var outerIterator = 0
    private var innerIterator = 0
    private val discardAll = false

    private fun callSketch(sketchInput: String): String? {
        // TODO Write temp file containing [code] as the sketch input
        try {
            TODO()
            // TODO Run sketch with temp file, time it
            /*
            Spyro does:
            output = subprocess.check_output(
                [SKETCH_BINARY_PATH, path,
                    '--bnd-inline-amnt', str(self.__inline_bnd),
                    '--slv-seed', str(self.__slv_seed),
                    '--slv-timeout', f'{self.__timeout / 60.0:2f}'],
                stderr=subprocess.PIPE)
             */
            // TODO return output, time
        } catch (e: Exception) {
            TODO()
            // TODO handle. Might also handle timeout separately
        }
    }

    /**
     * */
    private fun synthesize(negMay: Examples, lams: Lambdas): Pair<U?, Lambdas?> {
        // TODO Run Sketch with temp file
        val code = inputFactory.synthInput(negMay, lams)
        val output = callSketch(code)
        return if (output != null) {
//            val outParser = OutputParser(output, function)
            val phi = ULiteral(123456) // TODO outParser.parseProperty()
//            val lam = outParser.getLams()
            Pair(phi, mapOf())
        } else Pair(null, null)
    }

    /**
     *
     * arg notes: lams we have no idea about and may be perpetually empty
     * maxsatInput generates harnesses that are required to fulfill the neg must example,and harnesses that fulfill as many may conditions as possible
     * maxSynth tries to run sketch on the maxSat harnesses,
     * ==> this returns the result of one step of trying to generate new L properties off of the old one and fulfilling as many "may"s as possible
     *     the output is: additional mays, changes, synthesized property, and synthesized lambdas.
     *
     * **/
    fun maxSynthesize(
        pos: Examples,
        negMust: Examples,
        negMay: Examples,
        lams: Lambdas,
        phiInit: U?
    ): Pair<Pair<Examples, Examples>, Pair<U, Lambdas>> {
        val code = inputFactory.maxsatInput(pos, negMust, negMay, lams)
        val output = callSketch(code)
        return if (output != null) {
//            val outParser = OutputParser(output)
//            val (newNegMay, delta) = outParser.parseMaxsat(negMay)
            val phi = ULiteral(123456) // TODO outParser.parseProperty()
//            val lam = outParser.getLams()
//            Pair(Pair(newNegMay, delta), Pair(phi, lam))
            Pair(Pair(listOf(), listOf()), Pair(phi, mapOf()))
        } else {
            if (phiInit == null) throw Exception("MaxSynth failed")
            val (newNegMay, delta) = Pair(listOf<Example>(), negMay)
            Pair(Pair(newNegMay, delta), Pair(phiInit, lams))
        }
    }

    fun checkSoundness(phi: U, lams: Lambdas): Triple<Example?, Lambdas?, Boolean> {
        val code = inputFactory.soundnessInput(phi, lams)
        val output = callSketch(code)
        return if (output != null) {
//            val outParser = OutputParser(output)
//            val posEx = outParser.parsePosEx()
//            val lam = outParser.getLams()
//            Triple(posEx, lam, false)
            Triple (null, null, false)
        } else {
            Triple(null, null, true /* TODO elapsed_time >= timeout */)
        }
    }

    fun checkPrecision(
        phi: String,
        phiList: List<String>,
        negMay: Examples,
        lams: Lambdas
    ): Triple<Example?, U?, Lambdas?> {
        val code = inputFactory.precisionInput(phi, phiList, negMay, lams)
        val output = callSketch(code)
        if (output != null) {
//            val outParser = OutputParser(output)
//            val negEx = outParser.parseNegExPrecision()
//            val newPhi = ULiteral(123456) // TODO outParser.parseProperty()
//            val lam = outParser.getLams()
//            return Triple(negEx, newPhi, lam)
            return Triple(null, null, null)
        } else {
            return Triple(null, null, null)
        }
    }
    // TODO the above is up to line 288 of property_synthesizer.py

    /**not 100%sure if most precise is a list or a set/conjunct/single yet
     **/
    /**
     * pos: set of positive examples
     * negMust: set of negative examples
     * negMay: set of potential negative examples
     * lams: ????????? seem to be set of functions that are produced along
     *          with the set of properties, probably hand in hand/ part of the definition.
     *          might just be a part of synthesizing the best l property conjunction
     * phiList: seems to be a set of consistent phi's
     * phi truth: string value
     * phi init is an initial phi we get from synthesizeAllProperties
     * mostprecise : boolean, usually true:otherwise turned on when user hyperparameter disable_min is turned off.
     * updatePsi: from what i can tell always false.
     * **/
    /**
     * **/
    fun synthesizeProperty(
        posi: List<Example>,
        negMusti: Examples,
        negMayi: Examples,
        lamFunctionsi: Lambdas,
        phiListi: List<U?>,
        phiInit: U?,
        mostPrecise: Boolean,
        updatePsi: Boolean
    ): Pair<Pair<U, Examples>, Triple<Examples, Examples, Lambdas>> {
        var pos = posi
        var negMust = negMusti
        var negMay = negMayi
        var lamFunctions = lamFunctionsi
        var phiList = phiListi
        var phiE = phiInit
        var phiLastSound: U? = null
        var negDelta = listOf<Example>()
        var phiSound = listOf<U?>()
        while (true) {
            var (ePos, lam, timeout) = checkSoundness(phiE as U, lamFunctions)
            if (ePos != null) {
                pos = pos.plus(ePos)
                lamFunctions = lamFunctions.plus(lam as Lambdas)
                var (phi, lam) = synthesize(negMay, lamFunctions)
                if (phi == null && ((negMay.size == 1 && phiLastSound != null) || this.discardAll)) {
                    phi = phiLastSound
                    negDelta = negDelta.plus(negMay)
                    negMay = listOf()
                    lam = mapOf()
                } else if (phi != null) {
                    var (left, right) = maxSynthesize(pos, negMust, negMay, lamFunctions, phiLastSound)
                    var (negMay, delta) = left
                    var (phi, lam) = right
                    negDelta = negDelta.plus(delta)
                    /**skipping line about minimizing terms*/
                }
                phiE = phi
                lamFunctions = lamFunctions.plus(lam as Lambdas)
            } else {
                phiLastSound = phiE
                if (updatePsi && negMay.isNotEmpty()) {
                    phiList = phiList + listOf(phiE)
                }
                TODO()
//                var (eNeg, phi, lam) = checkPrecision(phiE, phiList as List<U>, negMay, lamFunctions)
//                if (eNeg != null) {
//                    phiE = phi
//                    negMay = negMay.plus(eNeg)
//                    lamFunctions = lam as Lambdas
//                } else {
//                    //skipping line about filtering neg delta
//                    return Pair(Pair(phiE, pos), Triple(negMust.plus(negMay), negDelta, lamFunctions))
//                }
                /**skipping may move/ hyperparameters*/

            }
            /**skipping a bunch of stuff about filtering negatives*/
        }

        return TODO()
    }

    fun synthesizeAllProperties(): Pair<List<U?>, List<U?>> {
        var phiList = listOf<U?>()
        var funList = listOf<U?>()
        var pos = listOf<Example>()
        var negMay = listOf<Example>()
        var negMust = listOf<Example>()
        var lamFunctions = mapOf<String, String>()
        var phiInit: U?
        var phi: U?
        var lam: Lambdas
        while (true) {
            if (negMay.isNotEmpty()) {
                val (tmpl, tmpr) =
                    maxSynthesize(pos, listOf(), negMay, lamFunctions, this.phiTruth)
                negMay = tmpl.first
                phiInit = tmpr.first
                lam = tmpr.second
                lamFunctions = lamFunctions.plus(lam)
            } else {
                phiInit = this.phiTruth
            }
            var (tmpl, tmpr) = synthesizeProperty(
                pos,
                listOf(),
                negMay,
                lamFunctions,
                phiList,
                phiInit,
                mostPrecise = true,
                updatePsi = true
            )
            phi = tmpl.first
            pos = tmpl.second
            negMust = tmpr.first
            negMay = tmpr.second
            lam = tmpr.third
            lamFunctions = lam
            if (negMust.isEmpty()) {
                return Pair(phiList, funList)
                /**there's a big thing in here about checking the minimization  */
            }
            var (tml, tmr) = synthesizeProperty(
                pos,
                negMust,
                listOf(),
                lamFunctions,
                listOf(),
                phiInit,
                mostPrecise = true,
                updatePsi = false
            )
            phi = tml.first
            pos = tml.second
            negMust = tmr.first
            negMay = tmr.second
            lam = tmr.third
            lamFunctions = lamFunctions.plus(lam)
            phiList = phiList.plus(phi)
            var funs = listOf<Lambdas>()
            /**not entirely sure what this part does or how to translate this to
             * kotlin, especially with our interpretation of u */
            for (f in lamFunctions)
                if (phi.to(f) != null)
                    funs.plus(f)
            /**here we need to **/
            this.outerIterator = this.outerIterator + 1
            this.innerIterator = 0
        }
        return TODO()
    }

    /**
     * in between synthesize all props and run is a bunch of statistics code
     * is very long, will do it another day ==> has nothing to do with actually synthesizing,
     * looks useful for analysis.
     *
     * */
    fun run(): Triple<List<U?>, List<U?>, List<Float>?> {
        /**skipping logging code insert*/
        val (phiList, funList) = synthesizeAllProperties()
        val statistics = null
        /**skipping logging code insert*/
        return Triple(phiList, funList, statistics)
    }
}