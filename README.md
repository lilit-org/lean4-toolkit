## 🔮 Lean 4 toolkit

<br>

> *this repository contains examples and explanations as i learn Lean 4 (a powerful theorem prover and programming language for the AI age)*

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

### running

<br>

#### project structure

<br>

- `src.lean`: the main entry point for the source code
- `src/`: source code for concepts and `examples/` 
- `lakefile.lean`: the lean package manager configuration file
- `lean-toolchain`: specifies the Lean version for the project (elan manages the compiler toolchains)
- `Makefile`: specify all available commands

<br>

#### `make build`

<br>

run all `src/*.lean` files with:

```shell
make build
```

<br>

#### basic types, theorems, type classes...

<br>

run any other file inside `src/example/` following its command inside `Makefile`.

<br>


----

### study resources

<br>

#### my notes

- [basics](docs/basic_concepts.md)

<br>

#### learning lean

- ✅[learn Lean](https://lean-lang.org/documentation/0)
- 🟡[Lean 4 documentation](https://leanprover.github.io/lean4/doc/)
- 🟡[mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/C01_Introduction.html)
- 🟡[theorem proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)


#### useful

- 🟡[vscode/cursor plugin](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)

<br>

#### applied examples

- [AI safety via debate, by g. irving et al (2018)](https://arxiv.org/pdf/1805.00899)
    - *"in the debate game, it is harder to lie than to refute a lie."*