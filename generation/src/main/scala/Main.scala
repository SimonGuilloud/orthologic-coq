//import `lattices-algorithms-build`.* 

import algorithms.{OLAlgorithm, OcbslAlgorithm, Printer}
import algorithms.Datastructures.*
import scala.util.Random

import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets


object Main {
  def main(args: Array[String]): Unit = {
    for i <- 1 to 50 do {
      val txt = (getBenchFile(2*i))
      val path = Paths.get(s"../bench/test${f"${2 * i}%03d"}.v")
      Files.createDirectories(path.getParent)
      Files.write(path, txt.getBytes(StandardCharsets.UTF_8))
    }
  }



  def getBenchFile(i:Int): String = {
    val (f1, f2) = generate_long_cnf(i)

    s"""Require Import OL_Bench.


Theorem test${f"${i}%03d"} (${(0 to i).map("x"+_).reduce(_ + " " + _)}: bool) :
  ${prettyCoq(f1)} 
    = 
  ${prettyCoq(f2)}
. Proof.
    ${if (i>60) then "benchSuperFast" else if (i>40) then "benchFast" else if (i>20) "bench" else "benchSlow"} "test$i".
Admitted.
"""
  }


  def getBenchFileTauto(i:Int): String = {
      val f = FormulaGenerator.randomFormula(size, numberVars)

      s"""Require Import OL_Bench.


  Theorem test${f"${i}%03d"} (${(0 to i).map("x"+_).reduce(_ + " " + _)}: bool) :
    ${prettyCoq(f1)} 
      = 
    ${prettyCoq(f2)}
  . Proof.
      ${if (i>60) then "benchSuperFast" else if (i>40) then "benchFast" else if (i>20) "bench" else "benchSlow"} "test$i".
  Admitted.
  """
    }




  def prettyCoq(f: Formula): String = f match {
    case Variable(id) => s"x$id"
    case Neg(child) => s"!${prettyCoq(child)}"
    case Or(children) => "(" + children.map(prettyCoq).reduce(_ + "||" + _) + ")"
    case And(children) => "(" + children.map(prettyCoq).reduce(_ + "&&" + _) + ")"
    case Literal(b) => if b then "x1||!x1" else "x1&&!x1"
  }

  def printCoqTest(p: (Formula, Formula), name: String, upvars: Int): Unit = {
    val (f1, f2) = p
    println(Console.BLUE + 
s"""Theorem ${name} (${(0 to upvars).map("x"+_).reduce(_ + " " + _)}: bool) :
  ${prettyCoq(f1)} 
    = 
  ${prettyCoq(f2)}
. Proof. match goal with | |- ?goal => (assert (goal /\\ goal /\\ goal /\\ goal /\\ goal); intuition) end.
  timeout 10 (solveOLBase BoolOL).
  timeout 10 (solveOL_memo BoolOL).
  timeout 10 (solveOL_fmap BoolOL).
  timeout 10 (solveOLPointers BoolOL).
  timeout 10 (btauto).
Admitted.
""" + Console.RESET
    )
  }

  def generate_distributive_swap(size:Int): (Formula, Formula) = {
    var i = 2
    var f: Formula = Or(List(Variable(0), Variable(1)))
    var g: Formula = Or(List(Variable(1), Variable(0)))
    while (i < size) {
      if i % 2 == 0 then 
        f = And(List(Variable(i), f))
        g = And(List(Variable(i), g))
      else
        f = Or(List(Variable(i), f))
        g = Or(List(Variable(i), g))
      i = i + 1
    }

    (f, g)
  }

  def generate_long_cnf(size: Int): (Formula, Formula) = {
    var i = 2
    var f: Formula = Or(List(Variable(0), Variable(1)))
    var g: Formula = Or(List(Variable(1), Variable(0)))
    while (i < size) {
      f = And(List(f, Or(List(Variable(i), Variable(i+1)))))
      g = And(List(g, Or(List(Variable(i+1), Variable(i)))))
      i = i + 2
    }
    (f, g)
  }




  def generate_reductions_random(seed:Int, number: Int, threshold: Double, size: Int, numberVars: Int): List[(Formula, Formula)] = {
    var l = List[(Formula, Formula)]()
    while (l.length < number) {
      val f = FormulaGenerator.randomFormula(size, numberVars)
      val r = OLAlgorithm.reducedForm(f)
      if (r.circuitSize.toDouble/f.circuitSize.toDouble < threshold) {
        l = (f, r) :: l
      }
    }
    l
  }

  def generate_commutative(n: Int): (Formula, Formula) = {
    val variables = List.range(0, n).map(i => Variable(i))
    val f1 = And(variables)
    val f2 = And(Random.shuffle(variables))
    (f1, f2)
  }
    



}
