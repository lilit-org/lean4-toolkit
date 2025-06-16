## 🔮 lean4 toolkit

<br>

> *this repository contains examples and explanations as i learn lean4 (a powerful theorem prover and programming language for the AI age)*

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
- `Main.lean`: the main module file
- `src/`: source code for examples and concepts
- `lakefile.lean`: the lean package manager configuration file (TODO: replace with `toml`)
- `lake-manifest.json`: automatically generated dependency lock file
- `lean-toolchain`: specifies the Lean version for the project
- `Makefile`: speficify all available commands

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

run any other file inside `src/` following its command inside `Makefile`. for instance, run `src/Basics.lean` with:

```shell
make run-basic
```

<br>


----

### study resources

<br>

#### my notes

<br>

- [basics](docs/basic_concepts.md)

<br>

#### learning lean

- [learn lean](https://lean-lang.org/documentation/0)
- [lean4 documentation](https://leanprover.github.io/lean4/doc/)
- [vscode/cursor plugin](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)

<br>

#### applied examples

- [AI safety via debate, by g. irving et al (2018)](https://arxiv.org/pdf/1805.00899)
    - *"in the debate game, it is harder to lie than to refute a lie."*