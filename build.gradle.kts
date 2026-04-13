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


dependencies {
    implementation(kotlin("reflect"))
    testImplementation(kotlin("test"))
    implementation("com.squareup.okhttp3:okhttp:4.12.0")
    implementation("com.squareup.moshi:moshi:1.15.0")
    implementation("com.squareup.moshi:moshi-kotlin:1.15.0")

    testImplementation("org.junit.jupiter:junit-jupiter:5.10.3")
    testImplementation("org.junit.jupiter:junit-jupiter-params:5.10.3")
    testRuntimeOnly("org.junit.jupiter:junit-jupiter-engine:5.10.3")
}


tasks.test {
    useJUnitPlatform()
}

tasks.withType<org.jetbrains.kotlin.gradle.tasks.KotlinCompile> {
    kotlinOptions.jvmTarget = "17"
}

tasks.withType<JavaCompile> {
    sourceCompatibility = "17"
    targetCompatibility = "17"
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
