## basic concepts

<br>

### types and functions

<br>

* there are two primary concepts in lean: functions and types.
* basic types are:
  - natural numbers (`Nat`): whole numbers starting from 0
  - booleans (`Bool`): true or false values
  - strings: text values

we start with simple examples to check types using `#check` and evaluate expressions using `#eval`:

```lean
#check 43        -- shows the type of 43
#eval 43 + 1     -- evaluates to 44
#check true      -- shows the type of true
#eval true && false  -- evaluates to false
```

<br>

### function definitions

<br>

functions are defined using the `def` keyword. here's a simple example:

```lean
def double (n : Nat) : Nat := n + n
```

<br>

this defines a function that:
- takes a natural number `n` as input
- returns a natural number
- doubles the input by adding it to itself

<br>

### simple proofs

<br>

lean is primarily a theorem prover. here's a simple proof:

```lean
theorem double_add (n m : Nat) : double (n + m) = double n + double m := by
  -- unfold the definition of double to work with the raw addition
  unfold double

  -- use lean's simplifier with three key properties of natural number addition
  -- 1. Nat.add_assoc: (a + b) + c = a + (b + c)  (associativity)
  -- 2. Nat.add_comm: a + b = b + a              (commutativity)
  -- 3. Nat.add_left_comm: a + (b + c) = b + (a + c)  (left commutativity)
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
``` 

<br>