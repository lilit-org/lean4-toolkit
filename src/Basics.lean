import Mathlib.Tactic

/-!
## basic types and functions
-/

-- natural numbers
#check 43
#eval 43 + 1

-- booleans
#check true
#eval true && false

-- strings
#check "gm, anon"
#eval "gm, ".append "anon"

/-!
## simple functions
-/

-- a function that doubles a number
def double (n : Nat) : Nat := n + n

-- let's test it
#eval double 333  -- should output 666

-- a function that checks if a number is even
def isEven (n : Nat) : Bool := n % 2 = 0

#eval isEven 10  -- should output true
#eval isEven 25  -- should output false
