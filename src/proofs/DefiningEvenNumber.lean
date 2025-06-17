import Mathlib.Data.Nat.Basic

/-
##
## I. defining what an "even" number is
##
-/

-- we define a new `inductive` type called `MyEven`
-- an inductive type allows us to define a data type by specifying its constructors
-- here, we say that a number `n` is `MyEven` if:
-- 1. `MyEven.zero` : 0 is even
-- 2. `MyEven.add_two` : if `k` is even, then `k + 2` is also even
inductive MyEven : Nat → Prop
  | zero : MyEven 0
  | add_two (k : Nat) (hk : MyEven k) : MyEven (k + 2)


/-
##
## II. proving a simple property about even numbers
##
-/

-- our goal is to prove the following theorem:
-- if a number `n` is even, then `n + 2` is also even
theorem even_add_two_is_even {n : Nat} (hn : MyEven n) : MyEven (n + 2) := by
  -- we have `hn : MyEven n` in our context
  -- our goal is `MyEven (n + 2)`
  -- since `MyEven` is an inductive type, we can use `induction` on `hn`.
  -- this means we'll prove the statement for each constructor of `MyEven`
  induction hn with
  | zero =>
    -- case 1: `n` is `0`.
    -- our goal is now `MyEven (0 + 2)`, which simplifies to `MyEven 2`
    -- we can prove this directly using the `MyEven.add_two` constructor
    -- we need to show that `MyEven 0` holds, which is true by `MyEven.zero`
    exact MyEven.add_two 0 MyEven.zero
  | add_two k hk ih =>
    -- case 2: `n` is of the form `k + 2`, where `hk : MyEven k`
    -- and `ih` is our inductive hypothesis: `MyEven (k + 2)` implies `MyEven ((k + 2) + 2)`
    -- the inductive hypothesis `ih` is actually `MyEven (k + 2)` implies `MyEven (k + 2 + 2)`
    -- `ih` will be a proof of our goal for `k` so `ih : MyEven (k + 2)`
    -- our goal is `MyEven ((k + 2) + 2)`
    -- we can use `MyEven.add_two` again
    -- to apply `MyEven.add_two`, we need a proof that `MyEven (k + 2)` holds (our inductive hypothesis `ih`)
    exact MyEven.add_two (k + 2) ih


/-
##
## III. using the theorem
##
-/

example : MyEven 4 := by
  -- we know 0 is even
  have h0 : MyEven 0 := MyEven.zero
  -- then 2 is even (0 + 2)
  have h2 : MyEven 2 := MyEven.add_two 0 h0
  -- then 4 is even (2 + 2)
  exact MyEven.add_two 2 h2


-- another way to prove `MyEven 4` using our theorem `even_add_two_is_even`
example : MyEven 4 := by
  -- we know `MyEven 0`.
  have h0 : MyEven 0 := MyEven.zero
  -- apply `even_add_two_is_even` to `h0` to get `MyEven (0 + 2)`, i.e., `MyEven 2`
  have h2 : MyEven 2 := even_add_two_is_even h0
  -- apply `even_add_two_is_even` to `h2` to get `MyEven (2 + 2)`, i.e., `MyEven 4`
  exact even_add_two_is_even h2


/-
##
## IV. a slightly more complex definition and proof
##
-/

-- let's define what it means for a number to be "odd":
-- a number `n` is `MyOdd` if `n = k + 1` for some even `k`
def MyOdd (n : Nat) : Prop := ∃ k, MyEven k ∧ n = k + 1

-- prove that if `n` is odd, then `n + 2` is also odd
theorem odd_add_two_is_odd {n : Nat} (hn : MyOdd n) : MyOdd (n + 2) := sorry
