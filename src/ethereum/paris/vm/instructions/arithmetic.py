import ast
import sys


def generate_error(node):
    message = f"(* Unsupported node type: {type(node).__name__} *)"

    if hasattr(node, "lineno") and hasattr(node, "col_offset"):
        # Print the location information
        print(
            f"Line: {node.lineno}, Column: {node.col_offset}",
            file=sys.stderr,
        )

    print(message, file=sys.stderr)

    return message


def generate_mod(node):
    if isinstance(node, ast.Module):
        return "\n\n".join(generate_stmt(stmt) for stmt in node.body)
    elif isinstance(node, ast.Interactive):
        return generate_error(node)
    elif isinstance(node, ast.Interactive):
        return generate_error(node)
    elif isinstance(node, ast.Interactive):
        return generate_error(node)
    else:
        assert False


def generate_stmt(node):
    if isinstance(node, ast.FunctionDef):
        params = " ".join(generate_arg(arg) for arg in node.args.args)
        body = "\n".join(generate_stmt(stmt) for stmt in node.body)
        return f"Definition {node.name} {params} : Evm :=\n{body}."
    elif isinstance(node, ast.AsyncFunctionDef):
        return generate_error(node)
    elif isinstance(node, ast.ClassDef):
        return generate_error(node)
    elif isinstance(node, ast.Return):
        return "  Return " + generate_expr(node.value) + "."
    elif isinstance(node, ast.Delete):
        return generate_error(node)
    elif isinstance(node, ast.Assign):
        return "  let " + generate_expr(node.targets[0]) + " := " + \
            generate_expr(node.value) + " in"
    # elif isinstance(node, ast.TypeAlias):
    #     return generate_error(node)
    elif isinstance(node, ast.AugAssign):
        return "  let " + generate_expr(node.target) + " := " + \
            generate_expr(node.op) + " " + generate_expr(node.value) + " in"
    elif isinstance(node, ast.AnnAssign):
        return generate_error(node)
    elif isinstance(node, ast.For):
        return "  For " + generate_expr(node.target) + " in " + \
            generate_expr(node.iter) + " do\n" + \
            "\n".join(generate_stmt(stmt) for stmt in node.body) + \
            "\nEndFor."
    elif isinstance(node, ast.AsyncFor):
        return generate_error(node)
    elif isinstance(node, ast.While):
        return "  While " + generate_expr(node.test) + " do\n" + \
            "\n".join(generate_stmt(stmt) for stmt in node.body) + \
            "\nEndWhile."
    elif isinstance(node, ast.If):
        return "  If " + generate_expr(node.test) + " then\n" + \
            "\n".join(generate_stmt(stmt) for stmt in node.body) + \
            "\nElse\n" + "\n".join(generate_stmt(stmt) for stmt in node.orelse) + \
            "\nEndIf."
    elif isinstance(node, ast.With):
        return "  With " + generate_expr(node.items[0].context_expr) + " as " + \
            generate_expr(node.items[0].optional_vars) + " do\n" + \
            "\n".join(generate_stmt(stmt) for stmt in node.body) + \
            "\nEndWith."
    elif isinstance(node, ast.AsyncWith):
        return generate_error(node)
    elif isinstance(node, ast.Match):
        return generate_error(node)
    elif isinstance(node, ast.Raise):
        return generate_error(node)
    elif isinstance(node, ast.Try):
        return "  Try\n" + "\n".join(generate_stmt(stmt) for stmt in node.body) + \
            "\nExcept\n" + "\n".join(generate_stmt(stmt) for stmt in node.handlers) + \
            "\nEndTry."
    # elif isinstance(node, ast.TryStar):
    #     return generate_error(node)
    elif isinstance(node, ast.Assert):
        return "  Assert " + generate_expr(node.test) + "."
    elif isinstance(node, ast.Import):
        return "Import " + ", ".join(alias.name for alias in node.names) + "."
    elif isinstance(node, ast.ImportFrom):
        return "Import " + (node.module if node.module is not None else "?") + \
            ".[" + ", ".join(alias.name for alias in node.names) + "]."
    elif isinstance(node, ast.Global):
        return generate_error(node)
    elif isinstance(node, ast.Nonlocal):
        return generate_error(node)
    elif isinstance(node, ast.Expr):
        return "  Let _ := " + generate_expr(node.value) + " in"
    elif isinstance(node, ast.Pass):
        return "  Pass."
    elif isinstance(node, ast.Break):
        return "  Break."
    elif isinstance(node, ast.Continue):
        return "  Continue."
    else:
        assert False


def generate_arg(arg):
    return "(" + arg.arg + " : " + arg.annotation.id + ")"


def generate_expr(node):
    if isinstance(node, ast.BinOp):
        return "(" + generate_expr(node.op) + \
            generate_expr(node.left) + " " + generate_expr(node.right) + ")"
    elif isinstance(node, ast.Constant):
        return str(node.value)
    elif isinstance(node, ast.Call):
        return generate_expr(node.func) + " " + \
            " ".join(generate_expr(arg) for arg in node.args)
    elif isinstance(node, ast.Name):
        return node.id
    elif isinstance(node, ast.Attribute):
        return generate_expr(node.value) + "." + node.attr
    else:
        return f"(* Unsupported expr node type: {type(node).__name__} *)"


file_name = "../execution-specs/src/ethereum/paris/vm/instructions/arithmetic.py"
file_content = open(file_name).read()
parsed_tree = ast.parse(file_content)

# print(ast.dump(parsed_tree, indent=4))

# Generate Coq code from the AST
coq_code = generate_mod(parsed_tree)

# Print the generated Coq code
print(coq_code)
