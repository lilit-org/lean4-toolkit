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

<br>

---

### documentation

<br>

- [basic concepts](docs/basic_concepts.md) - introduction to types, functions, and simple proofs in lean 4

<br>

---

### running

<br>

#### project structure

<br>

- `lakefile.lean`: the lean package manager configuration file
- `src.lean`: the main entry point for the source code
- `src/Basics.lean`: basic examples and concepts
- `src/SimpleProofs_*.lean`: more advanced concepts and examples for proofs
- `Makefile`

<br>

#### `make build`

<br>

run all `*.lean` files with:

```shell
make build

info: src/Basics.lean:8:0: 43 : ℕ
info: src/Basics.lean:9:0: 44
info: src/Basics.lean:12:0: Bool.true : Bool
info: src/Basics.lean:13:0: false
info: src/Basics.lean:16:0: "gm, anon" : String
info: src/Basics.lean:17:0: "gm, anon"
info: src/Basics.lean:27:0: 666
info: src/Basics.lean:32:0: true
info: src/Basics.lean:33:0: false
ℹ [2853/2855] Built src.SimpleProofs_I
info: src/SimpleProofs_I.lean:21:0: 10
info: src/SimpleProofs_I.lean:22:0: 0
info: src/SimpleProofs_I.lean:23:0: 6
info: src/SimpleProofs_I.lean:26:0: true
info: src/SimpleProofs_I.lean:27:0: false
info: src/SimpleProofs_I.lean:28:0: true
info: src/SimpleProofs_I.lean:31:0: double_add (n m : ℕ) : double (n + m) = double n + double m
info: src/SimpleProofs_I.lean:34:0: 14
info: src/SimpleProofs_I.lean:35:0: 14
Build completed successfully.
```

<br>

#### basic types and functions

<br>

run `Basics.lean` with:

```shell
make run-basic
```

<br>


#### simple proofs for simple theorems

<br>

* theorem to prove `2(n + m) = 2n + 2m`
* theorem to prove the relationship between double and addition
* theorem to prove double of zero is zero


<br>

run `proofs/SimpleProofs_*.lean` (replace `*` with `I` or `II`, etc.):

```shell
make run-simple_proofs_*
```

<br>

----

### study resources

<br>

#### learning lean

- [learn lean](https://lean-lang.org/documentation/0)
- [lean 4 documentation](https://leanprover.github.io/lean4/doc/)

<br>

#### applied examples

- [AI safety via debate, by G. Irving et al (2018)](https://arxiv.org/pdf/1805.00899)
    - *"In the debate game, it is harder to lie than to refute a lie."*