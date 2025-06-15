/-!
## simple proofs I
-/

-- takes a natural number and returns its double
def double (n : Nat) : Nat := n + n

-- checks if a number is even by seeing if it's divisible by 2
def isEven (n : Nat) : Bool := n % 2 = 0

-- this theorem proves that doubling the sum of two numbers is the same as
-- adding their doubles --> 2(n + m) = 2n + 2m

theorem double_add (n m : Nat) : double (n + m) = double n + double m := by
  -- unfold the definition of double to work with the raw addition
  unfold double

  -- use Lean's simplifier with three key properties of natural number addition
  -- 1. Nat.add_assoc: (a + b) + c = a + (b + c)  (associativity)
  -- 2. Nat.add_comm: a + b = b + a              (commutativity)
  -- 3. Nat.add_left_comm: a + (b + c) = b + (a + c)  (left commutativity)
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

-- examples of using the double function
#eval double 5  -- prints 10
#eval double 0  -- prints 0
#eval double 3  -- prints 6

-- examples of using the isEven function
#eval isEven 4  -- prints true
#eval isEven 5  -- prints false
#eval isEven 0  -- prints true

-- check the type of our theorem
#check double_add  -- shows the type: double_add : ∀ (n m : Nat), double (n + m) = double n + double m

-- example of the theorem in action
#eval double (3 + 4)  -- prints 14
#eval double 3 + double 4  -- prints 14
