# coq-of-python

> Translate Python code to Coq code

```python
input = "🐍"

print("🐓")
```

## Status

We focus on translating the Ethereum specification, which is written in Python: https://github.com/ethereum/execution-specs The output of the translation is in [CoqOfPython/ethereum](CoqOfPython/ethereum).

The generated Coq code type checks, with some holes for expressions we do not handle yet. We are now working on adding a semantics to be able to specify at least one file.

## Run

### Translate Python to Coq

Clone this repository and run:

```sh
git submodule update --init --recursive
```

as there are sub-modules. Then go in the `ethereum-execution-specs/src` folder and run:

```sh
find ethereum -name "*.py" -print0 | xargs -0 -n 1 python ../../main.py
```

This will translate each file of the Ethereum specification to Coq and put the result in the `CoqOfPython/ethereum` folder.

### Compile the Coq

Go into the `CoqOfPython` folder and install the dependencies with [opam](https://opam.ocaml.org/):

```sh
opam repo add coq-released https://coq.inria.fr/opam/released
opam install --deps-only coq-of-python.opam
```

Then, build the project (still in the `CoqOfPython` folder):

```sh
make -j4
```

It will compile all the Coq files, including the ones generated from the Ethereum specification and the proofs, so it might take some time.

## Documentation

For now, the documentation is the code (everything is open-source), this README, and the following blog posts:

- [Simulation of Python code in Coq](https://formal.land/blog/2024/05/14/translation-of-python-code-simulations) 2024-05-14
- [Translation of Python code to Coq](https://formal.land/blog/2024/05/10/translation-of-python-code) 2024-05-10
