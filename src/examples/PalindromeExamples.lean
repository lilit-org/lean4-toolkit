import src.classics.Palindrome

/-!
##
## this file demonstrates various ways to construct
## proofs of palindromes using the `IsPalindrome` inductive type
##
-/

-- empty list is a palindrome
example : IsPalindrome ([] : List Nat) := by
  exact IsPalindrome.nil

-- single element list is a palindrome
example : IsPalindrome [1] := by
  exact IsPalindrome.single_case 1

-- two element palindrome
example : IsPalindrome [1, 1] := by
  apply IsPalindrome.sandwich_case 1 []
  exact IsPalindrome.nil

-- three element palindrome
example : IsPalindrome [1, 2, 1] := by
  apply IsPalindrome.sandwich_case 1 [2]
  exact IsPalindrome.single_case 2

-- four element palindrome
example : IsPalindrome [1, 2, 2, 1] := by
  apply IsPalindrome.sandwich_case 1 [2, 2]
  apply IsPalindrome.sandwich_case 2 []
  exact IsPalindrome.nil

-- five element palindrome
example : IsPalindrome [1, 2, 3, 2, 1] := by
  apply IsPalindrome.sandwich_case 1 [2, 3, 2]
  apply IsPalindrome.sandwich_case 2 [3]
  exact IsPalindrome.single_case 3

-- string palindromes
example : IsPalindrome (String.toList "radar") := by
  apply IsPalindrome.sandwich_case 'r' (String.toList "ada")
  apply IsPalindrome.sandwich_case 'a' (String.toList "d")
  exact IsPalindrome.single_case 'd'

-- boolean list palindrome
example : IsPalindrome [true, false, true] := by
  apply IsPalindrome.sandwich_case true [false]
  exact IsPalindrome.single_case false


#check IsPalindrome.nil
#check IsPalindrome.single_case 1
#check IsPalindrome.sandwich_case 1 [] IsPalindrome.nil
#check IsPalindrome.sandwich_case 1 [2] (IsPalindrome.single_case 2)
#check IsPalindrome.sandwich_case 1 [2, 2] (IsPalindrome.sandwich_case 2 [] IsPalindrome.nil)
#check IsPalindrome.sandwich_case 1 [2, 3, 2] (IsPalindrome.sandwich_case 2 [3] (IsPalindrome.single_case 3))
#check IsPalindrome.sandwich_case 'r' (String.toList "ada") (IsPalindrome.sandwich_case 'a' (String.toList "d") (IsPalindrome.single_case 'd'))
#check IsPalindrome.sandwich_case true [false] (IsPalindrome.single_case false)
