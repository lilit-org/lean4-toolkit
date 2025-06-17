import «src».definitions.Basics

/-!
##
## theorem to prove that doubling the sum of two numbers is
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


/-!
##
## theorem to prove double of zero is zero
##
-/
theorem double_zero : double 0 = 0 := by
  unfold double
  rw [Nat.zero_add]


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
