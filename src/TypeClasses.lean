/-!
##
## type classes
##
-/

/-!
##
## a simple type class for things that can be doubled
##
-/
class Doublable (α : Type) where
  double : α → α

/-!
##
##instance for natural numbers
##
-/
instance : Doublable Nat where
  double n := n + n

/-!
##
## instance for lists
##
-/
instance [Doublable α] : Doublable (List α) where
  double xs := List.map (Doublable.double) xs


-- examples
#eval Doublable.double [1, 2, 3]  -- should output [2, 4, 6]
#eval Doublable.double ([] : List Nat)  -- empty list
#eval Doublable.double [5]  -- single element list
#eval Doublable.double [[1, 2], [3, 4]]  -- nested lists
#eval Doublable.double [0, 0, 0]  -- list with repeated elements
#eval Doublable.double [1000, 2000, 3000]  -- larger numbers


/-!
##
## a theorem about the relationship between map and append
##
-/

theorem map_append {α β : Type} (f : α → β) (xs ys : List α) :
  List.map f (xs ++ ys) = List.map f xs ++ List.map f ys := by
  induction xs with
  | nil =>
    simp [List.map, List.append]
  | cons x xs ih =>
    simp [List.map, List.append, ih]

/-!
## a theorem about the relationship between double and map
##
-/
theorem double_map {α : Type} [Doublable α] (xs : List α) :
  Doublable.double xs = List.map Doublable.double xs := by
  induction xs with
  | nil =>
    simp [Doublable.double, List.map]
  | cons x xs ih =>
    simp [Doublable.double, List.map, ih]



-- examples
#eval List.map (· + 1) ([1, 2] ++ [3, 4])  -- [2, 3, 4, 5]
#eval List.map (· + 1) [1, 2] ++ List.map (· + 1) [3, 4]  -- [2, 3, 4, 5]
#eval List.map (· * 2) ([1, 2] ++ [3, 4])  -- [2, 4, 6, 8]
#eval List.map (· * 2) [1, 2] ++ List.map (· * 2) [3, 4]  -- [2, 4, 6, 8]
#eval Doublable.double [1, 2, 3]  -- [2, 4, 6]
#eval List.map Doublable.double [1, 2, 3]  -- [2, 4, 6]
#eval Doublable.double [[1, 2], [3, 4]]  -- [[2, 4], [6, 8]]
#eval List.map Doublable.double [[1, 2], [3, 4]]  -- [[2, 4], [6, 8]]
