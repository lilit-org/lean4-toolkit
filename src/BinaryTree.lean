/-!
##
## inductive types
##
-/

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



-- examples
def exampleTree : BinaryTree Nat :=
  .node (.node .leaf 1 .leaf) 2 (.node .leaf 3 .leaf)

#eval countNodes exampleTree  -- should output 3

def emptyTree : BinaryTree Nat := .leaf
#eval countNodes emptyTree  -- should output 0

def singleNodeTree : BinaryTree Nat := .node .leaf 42 .leaf
#eval countNodes singleNodeTree  -- should output 1

def leftHeavyTree : BinaryTree Nat :=
  .node (.node (.node .leaf 1 .leaf) 2 .leaf) 3 .leaf
#eval countNodes leftHeavyTree  -- should output 3

def rightHeavyTree : BinaryTree Nat :=
  .node .leaf 1 (.node .leaf 2 (.node .leaf 3 .leaf))
#eval countNodes rightHeavyTree  -- should output 3

def balancedTree : BinaryTree Nat :=
  .node
    (.node (.node .leaf 1 .leaf) 2 (.node .leaf 3 .leaf))
    4
    (.node (.node .leaf 5 .leaf) 6 (.node .leaf 7 .leaf))
#eval countNodes balancedTree  -- should output 7
