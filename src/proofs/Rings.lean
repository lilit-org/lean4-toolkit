import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs

variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

-- these theorems are already defined in Mathlib.Algebra.Group.Basic
-- mul_inv_cancel
-- mul_one
-- mul_inv_rev


/-
##
## unique identity lemma
##
-/

-- simple lemma: the identity element is unique
lemma unique_identity (e e' : G)
    (he : ∀ g : G, e * g = g ∧ g * e = g)
    (he' : ∀ g : G, e' * g = g ∧ g * e' = g) :
    e = e' :=
by
  -- first, show that e * e' = e' using the fact that e' is an identity
  have h1 : e * e' = e' := (he' e).left

  -- next, show that e * e' = e using the fact that e is an identity
  have h2 : e * e' = e := (he e').right

  -- combine these equalities to show e = e'
  rw [← h2] at h1
  exact h1.symm
