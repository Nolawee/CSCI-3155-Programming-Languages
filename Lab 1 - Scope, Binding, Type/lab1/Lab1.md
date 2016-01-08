# Lab 1

Problem 1
	(a) The use of '''pi''' at line 4 is bound at line 3 because '''pi''' is defined in the scope of the '''circumference''' function. The use of '''pi''' at line 7 comes from the '''pi''' defined at line 1, because we are now outside of the scope of the '''circumference''' function.

	(b) The use of '''x''' at line 3 is bound at line 2 by the argument '''x:int''' of the function '''f'''. The value for '''x''' is the same as the one at line 3, but not necessarily in every case. If '''x''' had been changed between the function definition and the '''match''' case, the value would be different. The value of '''x''' at line 10 also comes from the original '''x'''. Though there was a new '''x''' declared on line 8, it is within its own scope. Finally, the use of '''x''' at line 13 also comes from the argument of the function definition.

Problem 2
	The body of '''g''' is well typed. The return type of '''g''' is '''Tuple2((Int, Int), Int)'''

	'''
	a: Int
	b: Tuple2[Int, Int]
	'''

	'''val (a,b) = (1, (x, 3)): Tuple2[Int, Tuple2[Int, Int]]''' because
		'''(x, 3): Tuple2[Int, Int]''' because
			'''x: Int'''
	'''if (x == 0) (b, 1) else (b, a + 2): Tuple2[Tuple2[Int, Int], Int]''' because
		'''(b, 1): Tuple2[Tuple2[Int, Int], Int]''' because
			'''b: Tuple2[Int, Int]'''
		'''(b, a+2): Tuple2[Tuple2[Int, Int], Int]''' because
			'''b: Tuple2[Int, Int]'''
			'''a+2: Int''' because
				'''a: Int'''

Problem 3
	(a)
		'''
		def abs(n: Double): Double = {
			if (n < 0) -n else n
		}
		'''
	(b)
		'''
		def xor(a: Boolean, b: Boolean): Boolean = {
			if (a == b) false else true
		}
		'''

Problem 4
	(a)
		'''
		def repeat(s: String, n: Int): String = n match {
		    case 1 => return s
		   	case _ => return s + repeat(s, n-1)
		}
		'''
	(b)
		(i)
			'''
			def sqrtStep(c: Double, xn: Double): Double = {
    			return xn - ((xn*xn - c)/(2*xn))
  			}
  			'''

  		(ii)