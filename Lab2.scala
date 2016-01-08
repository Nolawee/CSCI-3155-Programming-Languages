object Lab2 extends jsy.util.JsyApplication {
  import jsy.lab2.Parser
  import jsy.lab2.ast._
  
  /*
   * CSCI 3155: Lab 2
  * Dillon Drenzek
   * 
   * Partner: Samuel Carnes
   */

  /*
   * Replace the 'throw new UnsupportedOperationException' expression with
   * your code in each function.
   * 
   * Do not make other modifications to this template, such as
   * - adding "extends App" or "extends Application" to your Lab object,
   * - adding a "main" method, and
   * - leaving any failing asserts.
   * 
   * Your lab will not be graded if it does not compile.
   * 
   * This template compiles without error. Before you submit comment out any
   * code that does not compile or causes a failing assert.  Simply put in a
   * 'throws new UnsupportedOperationException' as needed to get something
   * that compiles without error.
   */
  
  /* We represent a variable environment is as a map from a string of the
   * variable name to the value to which it is bound.
   * 
   * You may use the following provided helper functions to manipulate
   * environments, which are just thin wrappers around the Map type
   * in the Scala standard library.  You can use the Scala standard
   * library directly, but these are the only interfaces that you
   * need.
   */
  
  type Env = Map[String, Expr]
  val emp: Env = Map()
  def get(env: Env, x: String): Expr = env(x)
  def extend(env: Env, x: String, v: Expr): Env = {
    require(isValue(v))
    env + (x -> v)
  }
  
  /* Some useful Scala methods for working with Scala values include:
   * - Double.NaN
   * - s.toDouble (for s: String)
   * - n.isNaN (for n: Double)
   * - n.isWhole (for n: Double)
   * - s (for n: Double)
   * - s format n (for s: String [a format string like for printf], n: Double)
   */

  def toNumber(v: Expr): Double = {
    require(isValue(v))
    (v: @unchecked) match {
      case Undefined => Double.NaN
      case N(n) => n
      case B(b) => if (b) 1 else 0
      case S(s)=> try { s.toDouble } catch { case _: NumberFormatException => Double.NaN }
      case _ => Double.NaN
    }
  }
  
  def toBoolean(v: Expr): Boolean = {
    require(isValue(v))
    (v: @unchecked) match {
      case Undefined => false
      case S(s) => if (s == "") false else true
      case N(n) => n match {
        case 0.0 => false
        case 0 => false
        case _ => if (n.isNaN) false else true
      }
      case B(b) => b
    }
  }
  
  def toStr(v: Expr): String = {
    require(isValue(v))
    (v: @unchecked) match {
      case S(s) => s
      case B(b) => if (b) "true" else "false"
      case N(n) => if (n.isWhole) "%.0f" format n else n.toString
      case Undefined => "undefined"
      case _ => throw new UnsupportedOperationException
    }
  }
  
  def eval(env: Env, e: Expr): Expr = {
    /* Some helper functions for convenience. */
    def eToVal(e: Expr): Expr = eval(env, e)
    
    e match {
      /* Base Cases */
      case Undefined => Undefined
      case S(s) => S(s)
      case N(n) => N(n)
      case B(b) => B(b)
      
      /* Inductive Cases */
      case Unary(Neg, b) => N(-toNumber(eToVal(b)))
      case Unary(Not, b) => B(!toBoolean(eToVal(b)))
      
      case Binary(a, b, c) => {
    	  a match {
    	    case And => {
    	      println(b)
    	      println(c)
    	      
    	      B(toBoolean(eToVal(b)) && toBoolean(eToVal(c)))
    	    }
    	    case Or => {
    	      B(toBoolean(eToVal(b)) || toBoolean(eToVal(c)))
    	    }
    	    
    	    case Plus => N(toNumber(eToVal(b)) + toNumber(eToVal(c)))
    	    case Minus => N(toNumber(eToVal(b)) - toNumber(eToVal(c)))
    	    case Times => N(toNumber(eToVal(b)) * toNumber(eToVal(c)))
    	    case Div => N(toNumber(eToVal(b)) / toNumber(eToVal(c)))
    	    
    	    case Eq => B(eToVal(b)==eToVal(c))
    	    case Ne => B(eToVal(b)!=eToVal(c))
    	    case Lt => {
    	      if (toNumber(eToVal(b)) < toNumber(eToVal(c))) B(true)
    	      else B(false)
    	    }
    	    case Le => {
    	      if (toNumber(eToVal(b)) <= toNumber(eToVal(c))) B(true)
    	      else B(false)
    	    }
    	    case Gt => {
    	      if (toNumber(eToVal(b)) > toNumber(eToVal(c))) B(true)
    	      else B(false)
    	    }
    	    case Ge => {
    	      if (toNumber(eToVal(b)) >= toNumber(eToVal(c))) B(true)
    	      else B(false)
    	    }
    	    case Seq => eToVal(b); eToVal(c)
    	    case _ => {
    	      throw new UnsupportedOperationException 
    	    }
    	  }
      }
      case ConstDecl(s, a, b) => {
        val v = eToVal(a)
        val envp = extend(env,s,v)
        eval(envp,b)
      }
      case If(s, a, b) => {
        if(toBoolean(eToVal(s))) eToVal(a)
        else eToVal(b)
      }
      case Var(x) => get(env,x)
      case Print(e1) => println(pretty(eToVal(e1))); Undefined
      case _ => {
        throw new UnsupportedOperationException
      }
    }
  }
    
  // Interface to run your interpreter starting from an empty environment.
  def eval(e: Expr): Expr = eval(emp, e)

  // Interface to run your interpreter from a string.  This is convenient
  // for unit testing.
  def eval(s: String): Expr = eval(Parser.parse(s))

 /* Interface to run your interpreter from the command-line.  You can ignore what's below. */ 
 def processFile(file: java.io.File) {
    if (debug) { println("Parsing ...") }
    
    val expr = Parser.parseFile(file)
    
    if (debug) {
      println("\nExpression AST:\n  " + expr)
      println("------------------------------------------------------------")
    }
    
    if (debug) { println("Evaluating ...") }
    
    val v = eval(expr)
    
    println(pretty(v))
  }

}