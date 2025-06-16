/-!
##
## a list is a palindrome if and only if you can construct a proof
## of IsPalindrome for it using my rules
##
-/

inductive IsPalindrome {α : Type} : List α → Prop where
  | nil : IsPalindrome []
  | single_case (a : α) : IsPalindrome [a]
  | sandwich_case (a : α) (l : List α) : IsPalindrome l → IsPalindrome (a :: l ++ [a])
