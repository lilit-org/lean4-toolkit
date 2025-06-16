import «src».definitions.Basics

/-!
#
# examples of the double function and its properties
#
-/

-- double function examples
#eval double 5  -- prints 10
#eval double 0  -- prints 0
#eval double 3  -- prints 6

-- even number examples
#eval isEven 4  -- prints true
#eval isEven 5  -- prints false
#eval isEven 0  -- prints true

-- examples of double with multiplication
#eval double (2 * 3)  -- prints 12
#eval (double 2) * 3  -- prints 12
#eval double (0 * 5)  -- prints 0
#eval (double 0) * 5  -- prints 0
#eval double (1 * 10)  -- prints 20
#eval (double 1) * 10  -- prints 20
#eval double (5 * 5)  -- prints 50
#eval (double 5) * 5  -- prints 50
