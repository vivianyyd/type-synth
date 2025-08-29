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

val exs = listOf(
    "(+ (cons 0 (cons 0 Li)))",
    "(+ (cons Li (cons Li LLi)))",
    "(- (cons Li 0))",
    "(- (cons LLi Li))",
    "(+ (cons LLi))",
    "(+ (cons (cons 0 Li)))",
    "(+ (cons tr (cons tr []b)))",
    "(- (cons 0 []b))",
    "(- (cons tr Li))",
    "(- (cons 0 LLi))",
    "(- (cons tr LLi))",
    "(- (cons tr (cons 0 Li)))"
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

    val requestBodyJson = mapOf(
        "model" to "gpt-4o-mini",
        "messages" to listOf(
            mapOf(
                "role" to "system",
                "content" to "Respond with only the text requested and no explanation."
            ),
            mapOf(
                "role" to "user", "content" to "Below are a list of example programs, which apply a fixed set of " +
                        "functions and values. " +
                        "Some of them are well-typed under Hindley-Milner typing rules; they are prefixed with a +. " +
                        "Others are ill-typed, and are prefixed with a -." +
                        "Determine the Hindley-Milner types of all program components that appear in the examples, " +
                        "that is, all of the unique symbols other than whitespace and parentheses. " +
                        "Some of the types may be parameterized: For instance, they may be of the form L<a> " +
                        "where a is a type variable, or L<Int> where Int is a primitive type. In this example, these" +
                        "types could represent lists. " +
                        "You may need to invent and assign appropriate type constructors like the ones in that example. " +
                        "However, they might have any name or have any number of type parameters." +
                        exs.joinToString(prefix = "\n", separator = "\n")
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