import Mathlib.Data.Nat.Basic

/-
##
## I. defining what an "even" number is
##
-/

-- we define a new `inductive` type called `Even`
-- an inductive type allows us to define a data type by specifying its constructors
-- here, we say that a number `n` is `Even` if:
-- 1. `Even.zero` : 0 is even
-- 2. `Even.add_two` : if `k` is even, then `k + 2` is also even
inductive Even : Nat → Prop
  | zero : Even 0
  | add_two {k : Nat} (hk : Even k) : Even (k + 2)


/-
##
## II. proving a simple property about even numbers
##
-/

-- our goal is to prove the following theorem:
-- if a number `n` is even, then `n + 2` is also even
theorem even_add_two_is_even {n : Nat} (hn : Even n) : Even (n + 2) := by
  -- we have `hn : Even n` in our context
  -- our goal is `Even (n + 2)`
  -- since `Even` is an inductive type, we can use `induction` on `hn`.
  -- this means we'll prove the statement for each constructor of `Even`
  induction hn with
  | zero =>
    -- case 1: `n` is `0`.
    -- our goal is now `Even (0 + 2)`, which simplifies to `Even 2`
    -- we can prove this directly using the `Even.add_two` constructor
    -- we need to show that `Even 0` holds, which is true by `Even.zero`
    apply Even.add_two
    apply Even.zero
  | add_two k hk ih =>
    -- case 2: `n` is of the form `k + 2`, where `hk : Even k`
    -- and `ih` is our inductive hypothesis: `Even (k + 2)` implies `Even ((k + 2) + 2)`
    -- the inductive hypothesis `ih` is actually `Even (k + 2)` implies `Even (k + 2 + 2)`
    -- `ih` will be a proof of our goal for `k` so `ih : Even (k + 2)`
    -- our goal is `Even ((k + 2) + 2)`
    -- we can use `Even.add_two` again
    -- to apply `Even.add_two`, we need a proof that `Even (k + 2)` holds (our inductive hypothesis `ih`)
    apply Even.add_two
    assumption -- this tactic tries to find a proof of the current goal among the hypotheses
               -- in this case, `ih` is exactly `Even (k + 2)`


/-
##
## III. using the theorem
##
-/

example : Even 4 := by
  -- we know 0 is even
  have h0 : Even 0 := Even.zero
  -- then 2 is even (0 + 2)
  have h2 : Even 2 := Even.add_two h0
  -- then 4 is even (2 + 2)
  exact Even.add_two h2


-- another way to prove `Even 4` using our theorem `even_add_two_is_even`
example : Even 4 := by
  -- we know `Even 0`.
  have h0 : Even 0 := Even.zero
  -- apply `even_add_two_is_even` to `h0` to get `Even (0 + 2)`, i.e., `Even 2`
  have h2 : Even 2 := even_add_two_is_even h0
  -- apply `even_add_two_is_even` to `h2` to get `Even (2 + 2)`, i.e., `Even 4`
  exact even_add_two_is_even h2


/-
##
## IV. a slightly more complex definition and proof
##
-/

-- let's define addition for natural numbers
-- let's assume `add_zero` and `add_succ` are axioms for now
-- let's define what it means for a number to be "odd":
-- a number `n` is `Odd` if `n = k + 1` for some even `k`
def Odd (n : Nat) : Prop := ∃ k, Even k ∧ n = k + 1

-- prove that if `n` is odd, then `n + 2` is also odd
theorem odd_add_two_is_odd {n : Nat} (hn : Odd n) : Odd (n + 2) := by
  -- our hypothesis `hn` is `Odd n`, which means `∃ k, wven k ∧ n = k + 1`
  -- we can `rcases` this hypothesis to get `k` and its properties
  rcases hn with ⟨k, hk_even, hk_n⟩
  -- `k : Nat`
  -- `hk_even : Even k`
  -- `hk_n : n = k + 1`

  -- our goal is `Odd (n + 2)`
  -- by definition, this means `∃ m, Even m ∧ (n + 2) = m + 1`

  -- let's substitute `n = k + 1` into the goal
  -- the goal becomes `Odd ((k + 1) + 2)`, which simplifies to `Odd (k + 3)`
  -- we need to find an `m` such that `Even m` and `k + 3 = m + 1`
  -- if we choose `m = k + 2`, then `k + 3 = (k + 2) + 1` is true
  -- so we need to show `Even (k + 2)`

  -- we know `hk_even : Even k`
  -- we can use our previously proven theorem `even_add_two_is_even` to show `Even (k + 2)`
  have hk_plus_2_even : Even (k + 2) := even_add_two_is_even hk_even

  -- now we have `hk_plus_2_even : Even (k + 2)`
  -- we want to show `∃ m, Even m ∧ (n + 2) = m + 1`
  -- let `m := k + 2`
  -- we use `exists.intro` to provide the witness `k + 2`
  exists (k + 2)
  -- now our goal is `Even (k + 2) ∧ (n + 2) = (k + 2) + 1`
  -- we can `split` the goal into two subgoals
  constructor
  -- subgoal 1: `Even (k + 2)`
  exact hk_plus_2_even
  -- subgoal 2: `(n + 2) = (k + 2) + 1`
  -- we know `n = k + 1`, lets rewrite:
  rw [hk_n]
  -- goal becomes `(k + 1) + 2 = (k + 2) + 1`
  -- this is true by associativity and commutativity of addition
  -- lean's simplifier `simp` can usually handle such arithmetic equalities
  simp
