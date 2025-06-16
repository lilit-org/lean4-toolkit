import src.classics.BinaryTree

/-!
##
## this file demonstrates various examples of binary trees and their operations
##
-/

-- basic tree with three nodes
def exampleTree : BinaryTree Nat :=
  .node (.node .leaf 1 .leaf) 2 (.node .leaf 3 .leaf)

#eval countNodes exampleTree  -- should output 3

-- empty tree
def emptyTree : BinaryTree Nat := .leaf
#eval countNodes emptyTree  -- should output 0

-- single node tree
def singleNodeTree : BinaryTree Nat := .node .leaf 42 .leaf
#eval countNodes singleNodeTree  -- should output 1

-- left-heavy tree
def leftHeavyTree : BinaryTree Nat :=
  .node (.node (.node .leaf 1 .leaf) 2 .leaf) 3 .leaf
#eval countNodes leftHeavyTree  -- should output 3

-- right-heavy tree
def rightHeavyTree : BinaryTree Nat :=
  .node .leaf 1 (.node .leaf 2 (.node .leaf 3 .leaf))
#eval countNodes rightHeavyTree  -- should output 3

-- balanced tree
def balancedTree : BinaryTree Nat :=
  .node
    (.node (.node .leaf 1 .leaf) 2 (.node .leaf 3 .leaf))
    4
    (.node (.node .leaf 5 .leaf) 6 (.node .leaf 7 .leaf))
#eval countNodes balancedTree  -- should output 7
