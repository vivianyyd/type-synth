plugins {
    kotlin("jvm") version "1.8.0"
    application
}

group = "org.example"
version = "1.0-SNAPSHOT"

buildscript {
    repositories { mavenCentral() }

    dependencies {
        val kotlinVersion = "1.8.0"
        classpath(kotlin("gradle-plugin", version = kotlinVersion))
    }
}

repositories {
    mavenCentral()
}

val cupVersion = "11b-20160615-1"
val jflexVersion = "1.9.1"

configurations {
    create("cup")
    create("jflex")
}

dependencies {
    implementation(kotlin("reflect"))
    testImplementation(kotlin("test"))
    implementation("com.squareup.okhttp3:okhttp:4.12.0")
    implementation("com.squareup.moshi:moshi:1.15.0")
    implementation("com.squareup.moshi:moshi-kotlin:1.15.0")

    testImplementation("org.junit.jupiter:junit-jupiter:5.10.3")
    testImplementation("org.junit.jupiter:junit-jupiter-params:5.10.3")
    testRuntimeOnly("org.junit.jupiter:junit-jupiter-engine:5.10.3")
    testImplementation("com.github.vbmacher:java-cup-runtime:$cupVersion")

    add("cup", "com.github.vbmacher:java-cup:$cupVersion")
    add("jflex", "de.jflex:jflex:$jflexVersion")
}


tasks.test {
    useJUnitPlatform()
    // TEMP (A/B verification): forward hole-ordering toggles to the test JVM.
    listOf("dfs.bottom", "dfs.cfo").forEach { k ->
        System.getProperty(k)?.let { systemProperty(k, it) }
    }
}

kotlin {
    jvmToolchain(8)
}

application {
    mainClass.set("MainKt")
}

tasks.named<JavaExec>("run") {
    standardInput = System.`in`
}

tasks.register<JavaExec>("runGeneratePrompt") {
    group = "application"
    description = "Run GeneratePrompt main function"
    classpath = sourceSets["main"].runtimeClasspath
    mainClass.set("GeneratePromptKt")
}

val generatedParserDir = layout.buildDirectory.dir("generated/sexpr")

sourceSets {
    named("test") {
        java.srcDir(generatedParserDir)
    }
}

val generateSExprLexer by
    tasks.registering(JavaExec::class) {
        group = "code generation"
        description = "Generate the S-expression lexer with JFlex"
        val flexFile = file("src/test/jflex/SExprLexer.flex")
        inputs.file(flexFile)
        outputs.dir(generatedParserDir)
        classpath = configurations["jflex"]
        mainClass.set("jflex.Main")
        args("--encoding", "UTF-8", "-d", generatedParserDir.get().asFile.absolutePath, flexFile)
    }

val generateSExprParser by
    tasks.registering(JavaExec::class) {
        group = "code generation"
        description = "Generate the S-expression parser with CUP"
        val cupFile = file("src/test/cup/SExprParser.cup")
        inputs.file(cupFile)
        outputs.dir(generatedParserDir)
        classpath = configurations["cup"]
        mainClass.set("java_cup.Main")
        args(
            "-destdir",
            generatedParserDir.get().asFile.absolutePath,
            "-parser",
            "SExprCupParser",
            "-symbols",
            "SExprSymbols",
            cupFile
        )
    }

tasks.withType<JavaCompile>().matching { it.name.contains("Test") }.configureEach {
    dependsOn(generateSExprLexer, generateSExprParser)
}

tasks.withType<org.jetbrains.kotlin.gradle.tasks.KotlinCompile>()
    .matching { it.name.contains("Test") }
    .configureEach { dependsOn(generateSExprLexer, generateSExprParser) }
