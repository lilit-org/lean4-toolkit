## basic concepts

<br>

### tl; dr

<br>

* there are two primary concepts in lean: functions and types
* basic types examples are natural numbers (`Nat`, whole numbers starting from 0), booleans (`Bool`), true or false values, strings
* functions are defined using the `def` keyword (`def double (n : Nat) : Nat := n + n`)
* check types using `#check`
* evaluate expressions using `#eval`

<br>

---

### universes

<br>

* the two primary kinds of universes are `Prop` and `Type`

<br>

#### predicative

<br>

* a function that returns a proposition (a statement that can be true or false), or, of type `Prop`
* for example, defining a predicate `is_empty` for lists:

```lean
def is_empty {α : Type} (l : List α) : Prop :=
  l = []
```

* `...` represents whatever input the predicate takes
* one can also define propositions inductively (i.e., instead of defining the property with a simple boolean check or an equality, one defines it by giving rules/constructors for when the proposition is true)

<br>

#### `Types`

<br>

* lean4's type theory is built upon a hierarchy of universes, which are types that contain other types (predicative)
* this is a hierarchy of universes (Type 0, Type 1, Type 2, ...), where Type is an abbreviation for Type 0
* these universes contain "data" or computational types. 
* for instance, for a function type `(a : A) → B`, where `A : Type u` and `B : Type v`, the resulting function type itself resides in `Type (max u v)`

<br>

##### inductive types

<br>

* one of the predicative `Type`
* a way of defining a new type by specifying its constructors.
  * used to define fundamental data structures like natural numbers (Nat), lists (List), and booleans (Bool), user-defined types
  * example for natural numbers, where `succ` is successor (takes a natural number and produces the next one)

```lean
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
```

<br>

##### inductive predicative types

<br>

* inductive type defined to live in one of the Type universes (must adhere to the predicativity rules of the Type hierarchy)
* for example, the definition of a polymorphic list, `MyList` lives in the same universe `u` as the type of its elements `α`

```lean
inductive MyList (α : Type u) : Type u where
  | nil : MyList α
  | cons : α → MyList α → MyList α
```

<br>

- universe polymorphism: same definition can be instantiated at different universe levels
- large elimination: while one can freely define functions that pattern match on a Type-level inductive type to produce a value in any other Type, doing the same with a Prop-level inductive to produce a Type-level value is restricted (proofs in Prop are meant to be logically relevant but computationally erased, while data in Type has computational content)

<br>

---

#### `Prop` (propositions)

<br>

* impredicative (can quantify over any type, including types in higher universes and even Prop itself)
* one can define a proposition that makes a statement about all types (for logical connectives -like `And`, `Or` - and quantifiers - `forall`, `exists`)
