import «src».Basics

/-!
## 
## this theorem proves that doubling the sum of two numbers is
## the same as adding their doubles --> 2(n + m) = 2n + 2m
##
-/

theorem double_add (n m : Nat) : double (n + m) = double n + double m := by
  -- unfold the definition of double to work with the raw addition
  unfold double

  -- use Lean's simplifier with three key properties of natural number addition
  -- 1. Nat.add_assoc: (a + b) + c = a + (b + c) (associativity)
  -- 2. Nat.add_comm: a + b = b + a (commutativity)
  -- 3. Nat.add_left_comm: a + (b + c) = b + (a + c) (left commutativity)
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

-- examples
#eval double 5  -- prints 10
#eval double 0  -- prints 0
#eval double 3  -- prints 6
#eval isEven 4  -- prints true
#eval isEven 5  -- prints false
#eval isEven 0  -- prints true
-- check the type of our theorem
#check double_add  -- shows the type: double_add : ∀ (n m : Nat), double (n + m) = double n + double m
-- example of the theorem in action
#eval double (3 + 4)  -- prints 14
#eval double 3 + double 4  -- prints 14


/-!
## 
## theorem to prove double of zero is zero
## 
-/

theorem double_zero : double 0 = 0 := by
  unfold double
  rw [Nat.zero_add]

-- examples
#eval double 0  -- prints 0
#check double_zero  -- type: double 0 = 0


/-!
## 
## theorem to prove double is distributive over multiplication
## 2(n * m) = (2n) * m
## 
-/

theorem double_mul (n m : Nat) : double (n * m) = (double n) * m := by
  unfold double
  -- after unfolding, we have: (n * m) + (n * m) = (n + n) * m
  rw [Nat.add_mul]  -- transforms (n + n) * m to n * m + n * m

-- examples
#eval double (2 * 3)  -- prints 12
#eval (double 2) * 3  -- prints 12
#eval double (0 * 5)  -- prints 0
#eval (double 0) * 5  -- prints 0
#eval double (1 * 10)  -- prints 20
#eval (double 1) * 10  -- prints 20
#eval double (5 * 5)  -- prints 50
#eval (double 5) * 5  -- prints 50
