//import `lattices-algorithms-build`.* 

import algorithms.{OLAlgorithm, OcbslAlgorithm, Printer}
import algorithms.Datastructures.*
import scala.util.Random

import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets
import scala.collection.immutable
import Math.*

object Main {
  def main(args: Array[String]): Unit = {

    for v <- 1 to 50 do {
      val txt = (getBenchFile(2*v))
      val path = Paths.get(s"../theories/bench2/test${f"${2 * v}%03d"}.v")
      Files.createDirectories(path.getParent)
      Files.write(path, txt.getBytes(StandardCharsets.UTF_8))
    }


    for v <- Range(2, 21, 2) do {
      val txts = (getBenchFileTauto(v, 4))
      txts.zipWithIndex.foreach((txt, i) => {
        val path = Paths.get(s"../theories/bench2/test_tauto${f"${v}%03d"}_$i.v")
        Files.createDirectories(path.getParent)
        Files.write(path, txt.getBytes(StandardCharsets.UTF_8))
      })
    }
    

  }



  def getBenchFile(v:Int): String = {
    val (f1, f2) = generate_long_cnf(v)

    s"""Require Import OL_Bench.


Theorem test${f"${v}%03d"} (${(0 to v).map("x"+_).reduce(_ + " " + _)}: bool) :
  ${prettyCoq(f1)} 
    = 
  ${prettyCoq(f2)}
. Proof.
    ${if (v>50) then "benchSuperFast" else if (v>40) then "benchFast" else if (v>12) "bench" else "benchSlow"} "test$v".
Admitted.
"""
  }





  def getBenchFileTauto(v: Int, i:Int): List[String] = {
    val s = v*6
    val list = find_small_r(s, 1000).toSet.toList
    val best = list.sortBy(x => abs(x._2 - 1/v)).head
    val (l, ru) = best
    val m = ceil(ru*v).toInt+1
    val size = l.foldLeft(1)(_ * _)*m
    val p = pow(1-compute_p(l), m)
    println(s"Generating formulas with params ${l.mkString("<", ", ", ">")},        v = $v,     p = $p,      ru = $ru,     m = $m,     ru*v = ${ru*v},     size = $size")
    val formulas = Range(0, i).toList.map( i => {
      val f = Neg(generate_conjunctive(m :: l, v))
      (i, f)
    })
    
    formulas.map((i, f) => {
s"""Require Import OL_Bench.


Theorem test_tauto${f"${v}%02d"}_$i (${(0 to v).map("x"+_).reduce(_ + " " + _)}: bool) :
  ${prettyCoq(f)} 
    = 
  true
. Proof.
    benchtauto "test${f"${v}%02d"}_$i".
Admitted.
""" 
    })

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

  def compute_p(ks: List[Int]) : Double = 
    ks match 
      case Nil => 0.5
      case head :: tl => 1.0 - Math.pow(compute_p(tl), head)
  
  def compute_r(ks: List[Int]) : Double = 
    val p = compute_p(ks)
    Math.log(2)/Math.log(1/p)


  def random_list(s: Int) : List[Int] = 
    if s <= 1 then Nil
    else 
      val rand = Random.nextFloat()
      if rand < 0.15 && s >= 3 then 4 :: random_list(s/4)
      else if rand < 0.3 && s >= 2 then 3 :: random_list(s/3)
      else 2 :: random_list(s/2)

  def find_small_r(s: Int, tries: Int): IndexedSeq[(List[Int], Double)] =
    Range(0, tries).map(_ => random_list(s)).map(ks => (ks.reverse, compute_r(ks)))

  def generate_disjunctive(ks : List[Int], n: Int) : Formula = 
    ks match
      case head :: tail => 
        Or(Range(0, head).map(i => generate_conjunctive(tail, n)).toList)
      case Nil =>
        if Random.nextBoolean() then 
          Variable(Random.nextInt(n))
        else
          Neg(Variable(Random.nextInt(n)))
    
  
  def generate_conjunctive(ks : List[Int], n: Int) : Formula =
    ks match
      case head :: tail => 
        And(Range(0, head).map(i => generate_disjunctive(tail, n)).toList)
      case Nil =>
        if Random.nextBoolean() then 
          Variable(Random.nextInt(n))
        else
          Neg(Variable(Random.nextInt(n)))

}
