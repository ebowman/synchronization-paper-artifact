import sbtcrossproject.CrossPlugin.autoImport._

val scala3Version = "3.8.2"

lazy val prioritizer = crossProject(JVMPlatform, JSPlatform)
  .crossType(CrossType.Full)
  .in(file("."))
  .settings(
    name := "prioritizer",
    version := "0.1.0-SNAPSHOT",
    scalaVersion := scala3Version,
  )
  .jvmSettings(
    libraryDependencies += "org.scalameta" %% "munit" % "1.2.4" % Test,
    Compile / mainClass := Some("Main"),
  )
  .jsSettings(
    scalaJSUseMainModuleInitializer := false,
    // NoModule: @JSExportTopLevel creates browser globals
    scalaJSLinkerConfig ~= { _.withModuleKind(org.scalajs.linker.interface.ModuleKind.NoModule) },
  )

lazy val prioritizerJVM = prioritizer.jvm
lazy val prioritizerJS = prioritizer.js
