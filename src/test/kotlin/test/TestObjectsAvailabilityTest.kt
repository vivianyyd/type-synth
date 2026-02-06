package test

import kotlin.test.Test
import kotlin.test.assertEquals

class TestObjectsAvailabilityTest {
    @Test
    fun `dict test exposes name`() {
        assertEquals("Dict", DictTest.name)
    }
}
