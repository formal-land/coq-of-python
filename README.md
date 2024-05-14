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

For now this works only on the Ethereum code. We assume you have cloned both this repository and the [Ethereum specification](https://github.com/ethereum/execution-specs) in the same folder:

```
├── coq-of-python
│   ├── CoqOfPython
│   ├── LICENSE
│   ├── main.py
│   └── README.md
└── execution-specs
    ├── CONTRIBUTING.md
    ├── LICENSE.md
    ├── lists
    ├── mypy.ini
    ├── network-upgrades
    ├── pyproject.toml
    ├── README.md
    ├── scripts
    ├── setup.cfg
    ├── setup.py
    ├── src
    ├── static
    ├── tests
    ├── tox.ini
    └── whitelist.txt
```

Go into the `execution-specs/src` folder and run the following command:

```sh
find ethereum -name "*.py" -exec echo {} \; -exec python ../../coq-of-python/main.py {} \;
```

This will translate each file of the Ethereum specification to Coq and put the result in the `coq-of-python/CoqOfPython/ethereum` folder.

### Compile the Coq

Go into the `coq-of-python/CoqOfPython` folder and run the following command:

```sh
make -j4
```

It will compile all the Coq files, including the ones generated from the Ethereum specification and the proofs.

## Documentation

For now, the documentation is the code (everything is open-source), this README, and the following blog posts:

- [Simulation of Python code in Coq](https://formal.land/blog/2024/05/14/translation-of-python-code-simulations) 2024-05-14
- [Translation of Python code to Coq](https://formal.land/blog/2024/05/10/translation-of-python-code) 2024-05-10
