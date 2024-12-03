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
}


tasks.test {
    useJUnitPlatform()
}

kotlin {
    jvmToolchain(8)
}

application {
    mainClass.set("enumgen.MainKt")
}

tasks.named<JavaExec>("run") {
    standardInput = System.`in`
}

