/*
From the following Haskell type signatures, give me some examples of expressions that I might see in a reasonable program such that *all* functions and values I list are used somewhere in some example.
No, you're not allowed to use anything that isn't in the list I gave. For example, you created the list [6,7], but that's not allowed. If you want a list of ints, you can construct one from 0, IL, and/or some other functions like (++) and (:). Write everything in prefix notation


No, you're not allowed to use lambdas either. You can only do function applications using the literals I've given



 */


import com.squareup.moshi.Moshi
import com.squareup.moshi.kotlin.reflect.KotlinJsonAdapterFactory
import okhttp3.*
import okhttp3.MediaType.Companion.toMediaType
import java.io.IOException
import java.util.concurrent.TimeUnit

data class ChatCompletionResponse(
    val choices: List<Choice>
) {
    data class Choice(val message: Message)
    data class Message(val role: String, val content: String)
}

val seeds = listOf(
    "(++) (repeat True) (singleton True)",
    "all isEven (cons 0 (cons 0 NilInt))",
    "and (cons True NilBool)",
    "any not (cons True (cons (not True) NilBool)",
    "catMaybes (cons NothingInt (repeat (listToMaybe NilInt)))",
    "concatMap maybeToList (repeat NothingBool)",
    "cons (hd (cons 0 NilInt)) NilInt",
    "cons 0 (singleton 0)",
    "cons True (replicate 0 True)",
    "dropWhile null (singleton NilInt)",
    "filter not (cons True NilBool)",
    "id 0",
    "id cons",
    "id NilInt",
    "inc (fromMaybe 0 NothingInt)",
    "inc (hd (filter isEven (cons 0 NilInt)))",
    "inc (length (cons True NilBool))",
    "inc 0",
    "isJust NothingBool",
    "isNothing ((!?) (replicate 0 0) 0)",
    "iterate id 0",
    "iterate inc 0",
    "iterate not True",
    "length NilInt",
    "map isEven (cons 0 NilInt)",
    "mapMaybe ((!?) (cons 0 NilInt)) (repeat 0)",
    "maybeToList NothingBool",
    "not True",
    "null (cons 0 NilInt)",
    "null NilBool",
    "null NilInt",
    "or (cons True NilBool)",
    "take 0 ((++) (reverse (cons True NilBool)) (repeat True))",
    "takeWhile isEven NilInt",
    "tl (cons True NilBool)",
    "True isEven (listToMaybe (cons 0 NilInt))",
    "uncons (cons 0 (cons 0 NilInt))",
    "unsnoc (repeat True)",
)

fun main() {
    val apiKey = System.getenv("OPENAI_API_KEY") ?: error("OPENAI_API_KEY not set")
//    val client = OkHttpClient()  // Default client has 10s timeout
    val client = OkHttpClient.Builder()
        .connectTimeout(30, TimeUnit.SECONDS)  // time to connect
        .readTimeout(2, TimeUnit.MINUTES)      // time waiting for response body
        .writeTimeout(2, TimeUnit.MINUTES)     // time sending request body
        .build()

    val moshi = Moshi.Builder()
        .add(KotlinJsonAdapterFactory())
        .build()

    val prompt =
        "Use only prefix notation. Parentheses are used around function names which consist of symbols when used as prefix operators." +
                "You may only use the names/functions which appear in the examples provided." +
                "Generate text that is in the same format as the examples given. Your response should include only" +
                "the words that appear in the seed examples, parentheses, spaces, and each example separated by a newline." +
                "Do not use any characters which do not appear in the examples; not even numbers nor list literals which use brackets []."


    val requestBodyJson = mapOf(
        "model" to "gpt-4o-mini",
        "messages" to listOf(
            mapOf(
                "role" to "system",
                "content" to "Respond with only the text requested and no explanation."
            ),
            mapOf(
                "role" to "user", "content" to "Below are a list of example programs, which apply a fixed set of " +
                        "functions and values. Generate 100 additional examples which are similarly reasonable, that is, " +
                        "they seem they might type check given the examples you've seen. They should be separated by " +
                        "newlines. Then add an extra newline, then provide 100 examples which do NOT seem reasonable, " +
                        "that is, they might perform an application which is ill-typed." + prompt +
                        seeds.joinToString(prefix = "\n", separator = "\n")
            )
            // TODO
        )
    )

    val jsonAdapter = moshi.adapter(Map::class.java)
    val body = RequestBody.create(
        "application/json".toMediaType(),
        jsonAdapter.toJson(requestBodyJson)
    )

    val request = Request.Builder()
        .url("https://api.openai.com/v1/chat/completions")
        .addHeader("Authorization", "Bearer $apiKey")
        .addHeader("Content-Type", "application/json")
        .post(body)
        .build()

    client.newCall(request).enqueue(object : Callback {
        override fun onFailure(call: Call, e: IOException) {
            e.printStackTrace()
        }

        override fun onResponse(call: Call, response: Response) {
            response.use {
                if (!it.isSuccessful) {
                    println("Request failed: ${it.code} ${it.message}")
                } else {
                    val adapter = moshi.adapter(ChatCompletionResponse::class.java)
                    val parsed = adapter.fromJson(it.body?.string() ?: "")
                    val reply = parsed?.choices?.firstOrNull()?.message?.content
                    println(reply ?: "(No content returned)")
                }
            }
        }
    })
}

/*
Synchronous blocking version

import okhttp3.*
import okhttp3.MediaType.Companion.toMediaType
import okhttp3.RequestBody.Companion.toRequestBody
import com.squareup.moshi.*
import com.squareup.moshi.kotlin.reflect.KotlinJsonAdapterFactory
import java.io.IOException

// Data classes for parsing the response
data class ChatCompletionResponse(
    val choices: List<Choice>
) {
    data class Choice(val message: Message)
    data class Message(val role: String, val content: String)
}

fun main() {
    val apiKey = System.getenv("OPENAI_API_KEY") ?: error("Please set OPENAI_API_KEY environment variable")

    val client = OkHttpClient()

    val moshi = Moshi.Builder()
        .add(KotlinJsonAdapterFactory())
        .build()

    val requestBodyJson = mapOf(
        "model" to "gpt-4o-mini",
        "messages" to listOf(
            mapOf("role" to "system", "content" to "You are a helpful assistant."),
            mapOf("role" to "user", "content" to "Write a short haiku about Kotlin.")
        )
    )

    val jsonAdapter = moshi.adapter(Map::class.java)
    val json = jsonAdapter.toJson(requestBodyJson)

    val mediaType = "application/json".toMediaType()
    val body = json.toRequestBody(mediaType)

    val request = Request.Builder()
        .url("https://api.openai.com/v1/chat/completions")
        .addHeader("Authorization", "Bearer $apiKey")
        .post(body)
        .build()

    try {
        client.newCall(request).execute().use { response ->
            if (!response.isSuccessful) {
                println("Request failed: ${response.code} ${response.message}")
                return
            }

            val responseBody = response.body?.string() ?: ""
            val adapter = moshi.adapter(ChatCompletionResponse::class.java)
            val parsed = adapter.fromJson(responseBody)

            val reply = parsed?.choices?.firstOrNull()?.message?.content ?: "(No content)"
            println("GPT response:\n$reply")
        }
    } catch (e: IOException) {
        e.printStackTrace()
    }
}

 */