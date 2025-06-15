## 🔮 lean4 toolkit

<br>

> *this repository contains examples and explanations as i learn lean 4 (a powerful theorem prover and programming language for the AI age)*

<br>

---

### installation

<br>

##### on macos

```bash
curl -L https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-apple-darwin.tar.gz | tar xz
./elan-init
source $HOME/.elan/env
```

##### on linux
```bash
curl -L https://github.com/leanprover/elan/releases/latest/download/elan-x86_64-unknown-linux-gnu.tar.gz | tar xz
./elan-init
source $HOME/.elan/env
```

<br>

test the installation with:
```bash
lean --version
lake --version
```

---

### project structure

<br>

- `lakefile.lean`: the lean package manager configuration file
- `src.lean`: the main entry point for the source code
- `src/Basics.lean`: basic examples and concepts
- `src/SimpleProofs_*.lean`: more advanced concepts and examples for proofs
- `Makefile`

<br>

---

### basic concepts

<br>

#### types and functions

lean has several basic types:
- natural numbers (`Nat`): whole numbers starting from 0
- booleans (`Bool`): true or false values
- strings: text values

<br>

we start with simple examples to check types using `#check` and evaluate expressions using `#eval`:

```lean
#check 43        -- shows the type of 42
#eval 43 + 1     -- evaluates to 43
#check true      -- shows the type of true
#eval true && false  -- evaluates to false
```

<br>

#### function definitions

functions are defined using the `def` keyword. here's a simple example:

```lean
def double (n : Nat) : Nat := n + n
```

this defines a function that:
- takes a natural number `n` as input
- returns a natural number
- doubles the input by adding it to itself

<br>

#### simple proofs

lean is primarily a theorem prover. here's a simple proof:

```lean
theorem double_add (n m : Nat) : double (n + m) = double n + double m := by
  -- unfold the definition of double to work with the raw addition
  unfold double

  -- use Lean's simplifier with three key properties of natural number addition
  -- 1. Nat.add_assoc: (a + b) + c = a + (b + c)  (associativity)
  -- 2. Nat.add_comm: a + b = b + a              (commutativity)
  -- 3. Nat.add_left_comm: a + (b + c) = b + (a + c)  (left commutativity)
  simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
```

<br>

---

### running

<br>

```shell
make build
```

<br>

#### basic types and functions

<br>

run `Basics.lean` with:

```shell
make run-basic

43 : ℕ
44
Bool.true : Bool
false
"gm, anon" : String
"gm, anon"
666
true
false
```

<br>

---

#### theorem to prove that doubling the sum of two numbers is the same as adding their double

<br>

run `SimpleProofs_I.lean` with:

```shell
make run-simple_proofs_I

10
0
6
true
false
true
double_add (n m : Nat) : double (n + m) = double n + double m
14
14
```


<br>

----

### resources

<br>

- [lean 4 documentation](https://leanprover.github.io/lean4/doc/)
- [lean 4 manual](https://leanprover.github.io/lean4/doc/)
