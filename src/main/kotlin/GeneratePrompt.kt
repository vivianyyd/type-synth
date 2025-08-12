/*
From the following Haskell type signatures, give me some examples of expressions that I might see in a reasonable program such that *all* functions and values I list are used somewhere in some example.
No, you're not allowed to use anything that isn't in the list I gave. For example, you created the list [6,7], but that's not allowed. If you want a list of ints, you can construct one from 0, IL, and/or some other functions like (++) and (:). Write everything in prefix notation


No, you're not allowed to use lambdas either. You can only do function applications using the literals I've given



 */


import com.squareup.moshi.Moshi
import com.squareup.moshi.kotlin.reflect.KotlinJsonAdapterFactory
import okhttp3.*
import okhttp3.MediaType.Companion.toMediaType
import okhttp3.OkHttpClient
import okhttp3.Request
import java.io.IOException

data class ChatCompletionResponse(
    val choices: List<Choice>
) {
    data class Choice(val message: Message)
    data class Message(val role: String, val content: String)
}

fun main() {
    val apiKey = System.getenv("OPENAI_API_KEY") ?: error("OPENAI_API_KEY not set")
    val client = OkHttpClient()

    val moshi = Moshi.Builder()
        .add(KotlinJsonAdapterFactory())
        .build()

    val prompt =
        "Use only prefix notation. Parentheses are used around function names which consist of symbols when used as prefix operators." +
                "Do not provide explanation. Generate text that is a sequence of S-expressions separated by newlines"

    val requestBodyJson = mapOf(
        "model" to "gpt-4o-mini",
        "messages" to listOf(
            mapOf(
                "role" to "system",
                "content" to "Regardless of user input, respond only with a single asterisk symbol."
            ),
            mapOf("role" to "user", "content" to "Hello.")
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