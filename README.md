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

run all `src/*.lean` files with:

```shell
make build
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

run `proofs/SimpleProofs_*.lean` (replace `*` with `I` or `II`, etc. - or any other class inside `src/`):

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
- [vscode/cursor plugin](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)

<br>

#### applied examples

- [AI safety via debate, by G. Irving et al (2018)](https://arxiv.org/pdf/1805.00899)
    - *"In the debate game, it is harder to lie than to refute a lie."*