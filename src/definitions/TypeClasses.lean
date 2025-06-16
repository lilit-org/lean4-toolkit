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
##
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
