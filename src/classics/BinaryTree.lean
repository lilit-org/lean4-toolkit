/-!
##
## a simple inductive type for binary trees
##
-/
inductive BinaryTree (α : Type) where
  | leaf : BinaryTree α
  | node (left : BinaryTree α) (value : α) (right : BinaryTree α) : BinaryTree α


/-!
##
## a function to count nodes in a binary tree
##
-/
def countNodes {α : Type} : BinaryTree α → Nat
  | .leaf => 0
  | .node left _ right => 1 + countNodes left + countNodes right
