# coq-of-python

> Translate Python code to Coq code

```python
input = "🐍"

print("🐓")
```

## Status

We focus on translating the Ethereum specification, which is written in Python: https://github.com/ethereum/execution-specs The output of the translation is in [CoqOfPython/ethereum](CoqOfPython/ethereum).

The generated Coq code type checks, with some holes for expressions we do not handle yet. We are now working on adding a semantics to be able to specify at least one file.
