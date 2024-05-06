import ast


def parse_python_code(code):
    # Parse Python code into an abstract syntax tree
    parsed_tree = ast.parse(code)
    return parsed_tree


# Example Python code
python_code = """
def add(a, b):
    return a + b

result = add(3, 5)
print(result)
"""

# Parse the Python code
parsed_tree = parse_python_code(python_code)

print(parsed_tree)

# Now you can traverse and analyze the parsed tree as needed
