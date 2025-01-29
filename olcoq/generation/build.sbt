

ThisBuild / version := "1.0"

ThisBuild / scalaVersion := "3.1.3"

organization := "ch.epfl.lara"

def githubProject(repo: String, commitHash: String) = RootProject(uri(s"$repo#$commitHash"))

lazy val `lattices-algorithms` = githubProject("https://github.com/epfl-lara/lattices-algorithms.git", "ce3bf0885e6004aa002397d1d7d72b2ffe9b8760")

lazy val root = (project in file("."))

  .settings(

    name := "generation"

  )

  .dependsOn(`lattices-algorithms`)