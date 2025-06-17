# basic concepts

<br>

## tl; dr

<br>

* Lean is a strict pure functional language with dependent types
    - strictness: function calls work similarly to the way they do in most languages (the arguments are fully computed before the function's body begins running)
    - purity: programs cannot have side effects such as modifying locations in memory, sending emails, or deleting files without the program's type saying so.
    - functions are first-class values
    - the execution model is inspired by the evaluation of mathematical expressions
    - dependent types make types into a first-class part of the language
* there are two primary concepts in lean: functions and types
* basic types examples are natural numbers (`Nat`, whole numbers starting from 0), booleans (`Bool`), true or false values, strings
* functions are defined using the `def` keyword (`def double (n : Nat) : Nat := n + n`)
* arguments can be declared implicit by wrapping them in curly braces instead of parentheses when defining a function
* Lean is an expression-oriented functional language, there are no conditional statements, only conditional expressions (e.g. `String.append "it is " (if 1 > 2 then "yes" else "no")`)
* some definitions are internally marked as being unfoldable during overload resolution (definitions that are to be unfolded are called reducible)
* iterative tests:
    - `#check`: verify the type of an expression (without evaluating it)
    - `#eval`: evaluate expressions
    - `#reduce`: see the normal form of an expression

<br>

---

## data types

<br>

### structures

<br>

* structures enable multiple independent pieces of data to be combined into a coherent whole that is represented by a brand new type

<br>

```lean
structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }
```

<br>

* Lean provides a convenient syntax for replacing some fields in a structure a la functional programing by using the `with` keyword in a structure initialization:

```lean
def zeroX (p : Point) : Point :=
  { p with x := 0 }
```

<br>

* every structure has a constructor, that gathers the data to be stored in the newly-allocated data structure
  - the constructor for a structure named S is named S.mk: S is a namespace qualifier, and mk is the name of the constructor itself

<br>

----

### linked lists

<br>

* Lean's standard library includes a canonical linked list datatype, `List`

```lean
def primesUnder10 : List Nat := [2, 3, 5, 7]
```

<br>

* behind the scenes, List is an inductive datatype:

```lean
inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α
```

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

* Lean 4's type theory is built upon a hierarchy of universes, which are types that contain other types (predicative)
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
  | succ (n : Nat) : Nat
```

or (with two constructors as well)

```lean
inductive Bool where
  | false : Bool
  | true : Bool
```

<br>

* datatypes that allow choices are called sum types and datatypes that can include instances of themselves are called recursive datatypes. 
  - recursive sum types are called inductive datatypes, because mathematical induction may be used to prove statements about them
  - inductive datatypes are consumed through pattern matching and recursive functions


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


#### `Prop` (propositions)

<br>

* impredicative (can quantify over any type, including types in higher universes and even Prop itself)
* one can define a proposition that makes a statement about all types (for logical connectives -like `And`, `Or` - and quantifiers - `forall`, `exists`)

<br>

---

### options

<br>

* not every list has a first entry—some lists are empty
* instead of equipping existing types with a special null value, Lean provides a datatype called `Option` that equips some other type with an indicator for missing values (for instance, a nullable `Int` is represented by `Option Int`)
* introducing a new type to represent nullability means that the type system ensures that checks for null cannot be forgotten
* `Option` has two constructors, some and none:

```lean
inductive Option (α : Type) : Type where
  | none : Option α
  | some (val : α) : Option α
```

<br>

---

### product

<br>

* the `Prod` structure is a generic way of joining two values together (e.g, Prod Nat String contains a Nat and a String)

* the structure Prod is defined with two type arguments:

```lean
structure Prod (α : Type) (β : Type) : Type where
  fst : α
  snd : β
```

*  the type `Prod α β` is typically written `α × β`

<br>

---

### sum

<br>

* the `Sum` datatype is a generic way of allowing a choice between values of two different types (e.g., `Sum String Int` is either a `String` or an `Int`. 

```lean
inductive Sum (α : Type) (β : Type) : Type where
  | inl : α → Sum α β
  | inr : β → Sum α β
```

* these names are abbreviations for "left injection" and "right injection"

<br>

---

## pattern matching

<br>

```lean
def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => false
```

<br>

* Lean 4 supports various types of patterns:
  - literal: match exact literal values

```lean
match false with
| true => "It's true!"
| false => "It's false!"
```
  - variable: a fresh identifier acts as a variable, matching any value and binding that value to the variable within the right-hand side

```lean
def isPositive (n : Nat) : Bool :=
  match n with
  | 0 => false
  | _ => true
```
  - constructor: match values constructed by a specific constructor of an inductive type (central to working with algebraic data types)

```lean
inductive Option (α : Type) where
| none : Option α
| some : α → Option α

def unwrapOption (o : Option Nat) : Nat :=
  match o with
  | Option.none => 0
  | Option.some n => n
```
- disjunctive: allows a single right-hand side to apply to multiple patterns
```lean
def fib (n : Nat) : Nat :=
  match n with
  | 0 | 1 => 1
  | n' + 2 => fib n' + fib (n' + 1)
```

<br>

---

## recursivity

<br>

* inductive datatypes are allowed to be recursive (Nat is an example of such a datatype because succ demands another Nat)
* recursive datatypes can represent arbitrarily large data, limited only by technical factors like available memory
* Lean ensures that every recursive function will eventually reach a base case (ruling out accidental infinite loops -  especially important when proving theorems, where infinite loops cause major difficulties

<br>

----

## polymorphism

<br>

* in functional programming, polymorphism refers to datatypes and definitions that take types as arguments (as opposed to object-oriented programming, where the term refers to subclasses that may override some behavior of their superclass)

<br>

---

## anonymous functions

<br>

* define functions inline without giving them a specific name
* the most common way to define an anonymous function in Lean 4 is using the fun keyword

```lean
fun (parameter_name : Type) => expression
```

* Lean also supports the traditional lambda calculus notation using the λ 

```lean
#check λ (x : Nat) => x * x
-- Output: fun x => x * x : Nat → Nat
```

* pattern matching can be used within anonymous functions, particularly useful when the function's behavior depends on the structure of its input

```lean
inductive Option (α : Type) where
  | none : Option α
  | some : α → Option α

def unwrapOptionOrDefault (defaultVal : Nat) : Option Nat → Nat :=
  fun
  | Option.none => defaultVal
  | Option.some n => n

#eval unwrapOptionOrDefault 0 (Option.some 5) -- 5
#eval unwrapOptionOrDefault 0 Option.none    -- 0
```

* for very simple anonymous functions, Lean 4 provides the · (dot) character (often used for operations that involve an infix operator or a function application)

```lean
def twice (f : Nat → Nat) (a : Nat) := f (f a)

#eval twice (fun x => x + 2) 10 -- 14
#eval twice (· + 2) 10 -- 14 (using shorthand)
#eval (· * 10) 5 -- 50
```

<br>

* for instance, `(· + 2)` is syntax sugar for `(fun x => x + 2)`

<br>

---

## namespaces

<br>

* each name in Lean occurs in a namespace, which is a collection of names
* names are placed in namespaces using . (e.g., `List.map` is the name map in the List namespace)
* names can be directly defined within a namespace:

```lean
def Nat.double (x : Nat) : Nat := x + x
```

* because Nat is also the name of a type, dot notation is available to call Nat.double on expressions with type Nat:

```lean
#eval (4 : Nat).double
8
```

* namespaces may be opened, which allows the names in them to be used without explicit qualification

```lean
open NewNamespace in
#check quadruple
NewNamespace.quadruple (x : Nat) : Nat
```