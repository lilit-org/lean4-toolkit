/-
##
## for the lolz
## https://leanprover-community.github.io/blog/posts/FLT-announcement/
## https://github.com/leanprover-community/flt-regular
## https://leanprover-community.github.io/flt-regular/blueprint/
##
-/

#check 2 + 2 = 4

def FermatLastTheorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

#check FermatLastTheorem

theorem easy : 2 + 2 = 4 :=
  rfl

#check easy

theorem hard : FermatLastTheorem :=
  sorry

#check hard
