//import `lattices-algorithms-build`.* 
import algorithms.{OLAlgorithm, OcbslAlgorithm, Printer}
import algorithms.Datastructures.*
import scala.util.Random

object Main {
  def main(args: Array[String]): Unit = {

    //generate_reductions_random(0, 10, 0.8, 30, 15).foreach(printPair)
    //printPair(generate_distributive_swap(50))
    printCoqTest(generate_long_cnf(25), 3, 25)
  }

  def printPair(p: (Formula, Formula)): Unit = {
    print(Console.RED + prettyCoq(p._1) + "\n" + "  =" + "\n" + Console.BLUE + prettyCoq(p._2) + "\n")
    println("")
  }



  def prettyCoq(f: Formula): String = f match {
    case Variable(id) => s"x$id"
    case Neg(child) => s"${prettyCoq(child)}"
    case Or(children) => "(" + children.map(prettyCoq).reduce(_ + "||" + _) + ")"
    case And(children) => "(" + children.map(prettyCoq).reduce(_ + "&&" + _) + ")"
    case Literal(b) => if b then "T" else "F"
  }

  def printCoqTest(p: (Formula, Formula), no: Int, upvars: Int): Unit = {
    val (f1, f2) = p
    println(Console.BLUE + 
s"""Theorem test${no}_solveOL (${(0 to upvars).map("x"+_).reduce(_ + " " + _)}: bool) :
  ${prettyCoq(f1)} 
    = 
  ${prettyCoq(f2)}
. Proof. timeout 10 (solveOL BoolOL). Qed.

Theorem test${no}_btauto (${(0 to upvars).map("x"+_).reduce(_ + " " + _)}: bool) :
  ${prettyCoq(f1)} 
    = 
  ${prettyCoq(f2)}
. Proof. timeout 10 (btauto). Qed."""


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