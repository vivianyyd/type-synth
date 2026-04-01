package testutil

import oneast.CustomSchedule
import java.io.File

fun loadSchedule(schedule: File, delimiter: String = ","): CustomSchedule {
    require(schedule.isFile) { "Not a file: $schedule" }
    return CustomSchedule(
        schedule.readLines().mapNotNull {
            if (it.startsWith("//")) null else it.split(delimiter).map { it.trim() }
        })
}
