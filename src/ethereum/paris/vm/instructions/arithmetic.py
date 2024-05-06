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
        return generate_error(node)


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
            generate_operator(node.op) + " " + \
            generate_expr(node.value) + " in"
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
        return generate_error(node)


def generate_expr(node):
    if isinstance(node, ast.BoolOp):
        return "(" + generate_boolop(node.op) + \
            " ".join(generate_expr(value) for value in node.values) + ")"
    elif isinstance(node, ast.NamedExpr):
        return "(" + generate_expr(node.target) + " := " + \
            generate_expr(node.value) + ")"
    elif isinstance(node, ast.BinOp):
        return "(" + generate_operator(node.op) + \
            generate_expr(node.left) + " " + generate_expr(node.right) + ")"
    elif isinstance(node, ast.UnaryOp):
        return "(" + generate_unaryop(node.op) + generate_expr(node.operand) + ")"
    elif isinstance(node, ast.Lambda):
        return f"fun {generate_expr(node.args)} => {generate_expr(node.body)}"
    elif isinstance(node, ast.IfExp):
        return f"If {generate_expr(node.test)} then {generate_expr(node.body)} else {generate_expr(node.orelse)}"
    elif isinstance(node, ast.Dict):
        return "{" + ", ".join(generate_expr(key) + ": " + generate_expr(value) for key, value in zip(node.keys, node.values)) + "}"
    elif isinstance(node, ast.Set):
        return "{" + ", ".join(generate_expr(elt) for elt in node.elts) + "}"
    elif isinstance(node, ast.ListComp):
        return f"[{generate_expr(node.elt)} for {generate_expr(node.generators)}]"
    elif isinstance(node, ast.SetComp):
        return f"{{{generate_expr(node.elt)} for {generate_expr(node.generators)}}}"
    elif isinstance(node, ast.DictComp):
        return f"{{{generate_expr(node.key)}: {generate_expr(node.value)} for {generate_expr(node.generators)}}}"
    elif isinstance(node, ast.GeneratorExp):
        return f"({generate_expr(node.elt)} for {generate_expr(node.generators)})"
    elif isinstance(node, ast.Await):
        return f"Await {generate_expr(node.value)}"
    elif isinstance(node, ast.Yield):
        return f"Yield {generate_expr(node.value)}"
    elif isinstance(node, ast.YieldFrom):
        return f"YieldFrom {generate_expr(node.value)}"
    elif isinstance(node, ast.Compare):
        return f"{generate_expr(node.left)} {generate_cmpop(node.ops[0])} {generate_expr(node.comparators[0])}"
    elif isinstance(node, ast.Call):
        return f"{generate_expr(node.func)}({', '.join(generate_expr(arg) for arg in node.args)})"
    elif isinstance(node, ast.FormattedValue):
        return f"{generate_expr(node.value)}"
    elif isinstance(node, ast.JoinedStr):
        return f"{''.join(generate_expr(value) for value in node.values)}"
    elif isinstance(node, ast.Constant):
        return str(node.value)
    elif isinstance(node, ast.Attribute):
        return f"{generate_expr(node.value)}.{node.attr}"
    elif isinstance(node, ast.Subscript):
        return f"{generate_expr(node.value)}[{generate_expr(node.slice)}]"
    elif isinstance(node, ast.Starred):
        return f"*{generate_expr(node.value)}"
    elif isinstance(node, ast.Name):
        return node.id
    elif isinstance(node, ast.List):
        return f"[{', '.join(generate_expr(elt) for elt in node.elts)}]"
    elif isinstance(node, ast.Tuple):
        return f"({', '.join(generate_expr(elt) for elt in node.elts)})"
    elif isinstance(node, ast.Slice):
        return f"{generate_expr(node.lower)}:{generate_expr(node.upper)}"
    else:
        return generate_error(node)


def generate_boolop(node):
    if isinstance(node, ast.And):
        return "And"
    elif isinstance(node, ast.Or):
        return "Or"
    else:
        return generate_error(node)


def generate_operator(node):
    if isinstance(node, ast.Add):
        return "+"
    elif isinstance(node, ast.Sub):
        return "-"
    elif isinstance(node, ast.Mult):
        return "*"
    elif isinstance(node, ast.MatMult):
        return "@"
    elif isinstance(node, ast.Div):
        return "/"
    elif isinstance(node, ast.Mod):
        return "%"
    elif isinstance(node, ast.Pow):
        return "**"
    elif isinstance(node, ast.LShift):
        return "<<"
    elif isinstance(node, ast.RShift):
        return ">>"
    elif isinstance(node, ast.BitOr):
        return "|"
    elif isinstance(node, ast.BitXor):
        return "^"
    elif isinstance(node, ast.BitAnd):
        return "&"
    elif isinstance(node, ast.FloorDiv):
        return "//"
    else:
        return generate_error(node)


def generate_unaryop(node):
    if isinstance(node, ast.Invert):
        return "~"
    elif isinstance(node, ast.Not):
        return "!"
    elif isinstance(node, ast.UAdd):
        return "+"
    elif isinstance(node, ast.USub):
        return "-"
    else:
        return generate_error(node)


def generate_cmpop(node):
    if isinstance(node, ast.Eq):
        return "=="
    elif isinstance(node, ast.NotEq):
        return "!="
    elif isinstance(node, ast.Lt):
        return "<"
    elif isinstance(node, ast.LtE):
        return "<="
    elif isinstance(node, ast.Gt):
        return ">"
    elif isinstance(node, ast.GtE):
        return ">="
    elif isinstance(node, ast.Is):
        return "Is"
    elif isinstance(node, ast.IsNot):
        return "IsNot"
    elif isinstance(node, ast.In):
        return "In"
    elif isinstance(node, ast.NotIn):
        return "NotIn"
    else:
        return generate_error(node)


def generate_arg(node):
    return "(" + node.arg + " : " + node.annotation.id + ")"


file_name = "../execution-specs/src/ethereum/paris/vm/instructions/arithmetic.py"
file_content = open(file_name).read()
parsed_tree = ast.parse(file_content)

# print(ast.dump(parsed_tree, indent=4))

# Generate Coq code from the AST
coq_code = generate_mod(parsed_tree)

# Print the generated Coq code
print(coq_code)
