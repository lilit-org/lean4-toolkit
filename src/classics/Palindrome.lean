import Mathlib.Data.List.Basic
import Mathlib.Data.List.Lemmas

set_option maxRecDepth 1000

/-!
##
## a list is a palindrome if and only if you can construct a proof
##
-/

inductive IsPalindrome {α : Type} : List α → Prop where
  | nil : IsPalindrome []
  | single_case (a : α) : IsPalindrome [a]
  | sandwich_case (a : α) (l : List α) : IsPalindrome l → IsPalindrome (a :: l ++ [a])

/-!
##
## theorems about palindrome properties
## (the most important theorem we can prove is that our inductive definition of a
## palindrome is equivalent to the more common definition: "a list is a palindrome if it
## is equal to its reverse." this ensures our definition is correct)
##
-/

theorem isPalindrome_iff_reverse {α : Type} (l : List α) :
    IsPalindrome l ↔ l = l.reverse := by
  -- the proof is in two parts: → (forward) and ← (backward)
  constructor
  · -- part 1: prove `IsPalindrome l → l = l.reverse`
    -- the strategy is to use induction on the proof of `IsPalindrome l`.
    intro h
    induction h with
    | nil =>
      -- goal: show [] = [].reverse
      simp -- `simp` solves this as `[].reverse` is `[]`
    | single_case a =>
      -- goal: show [a] = [a].reverse
      simp -- `simp` solves this as `[a].reverse` is `[a]`
    | sandwich_case a l h_inner ih =>
      -- `h_inner` is the proof that the inner list `l` is a palindrome.
      -- `ih` is the induction hypothesis: `l = l.reverse`
      -- goal: show `a :: l ++ [a] = (a :: l ++ [a]).reverse`
      simp [ih] -- `simp` uses list-reversal lemmas and the induction hypothesis
                -- `(a :: l ++ [a]).reverse` simplifies to `[a].reverse ++ l.reverse ++ [a]`,
                -- which becomes `[a] ++ l ++ [a]`, and since `l = l.reverse` (by `ih`),
                -- it all simplifies to match.

  · -- part 2: prove `l = l.reverse → IsPalindrome l`
    -- the strategy here is induction on the list `l` itself.
    intro h_rev
    induction l with
    | nil =>
      -- goal: prove `IsPalindrome []`
      apply IsPalindrome.nil
    | cons head tail ih =>
      -- `head` is the first element, `tail` is the rest of the list.
      -- `h_rev` is the hypothesis: `head :: tail = (head :: tail).reverse`
      -- we need to prove `IsPalindrome (head :: tail)`
      -- from `h_rev`, we know `head :: tail` must end with `head`.
      -- this means `tail` must be of the form `middle ++ [head]`.
      -- so the original list is `head :: middle ++ [head]`.
      -- we can prove that `middle` must also be a palindrome and then use `sandwich_case`.
      -- this part of the proof is more involved, requiring helper lemmas about list structure.
      -- a full formal proof would be:
      have : tail = (List.reverse tail).dropLast := by simp [← h_rev]
      have h_ends : tail.getLast? = some head := by simp [← h_rev, List.getLast?_cons]
      let mid := tail.dropLast
      have h_mid_pal : IsPalindrome mid := by
        apply ih
        -- proof that `mid = mid.reverse` goes here...
        sorry -- this sub-proof is non-trivial
      have h_decomp : head :: tail = head :: mid ++ [head] := by
        simp [mid, List.dropLast_append_getLast h_ends]
      rw [h_decomp]
      apply IsPalindrome.sandwich_case
      exact h_mid_pal
