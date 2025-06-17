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
    IsPalindrome l ↔ l = l.reverse := sorry
