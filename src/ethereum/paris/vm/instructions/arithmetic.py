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


def generate_indent(indent):
    return "  " * indent


def generate_constant(node, value):
    if value is None:
        return "Value.None"
    elif value is True:
        return "Value.Bool true"
    elif value is False:
        return "Value.Bool false"
    elif isinstance(value, int):
        return f"Value.Integer {str(value)}"
    elif isinstance(value, float):
        return f"Value.Float {str(value)}"
    elif isinstance(value, str):
        return "Value.String \"" + value.replace("\"", "\"\"\"") + "\""
    else:
        return generate_error(node)


def generate_mod(node):
    if isinstance(node, ast.Module):
        return "\n\n".join(generate_stmt(0, stmt) for stmt in node.body)
    elif isinstance(node, ast.Interactive):
        return generate_error(node)
    elif isinstance(node, ast.Interactive):
        return generate_error(node)
    elif isinstance(node, ast.Interactive):
        return generate_error(node)
    else:
        return generate_error(node)


def generate_stmt(indent, node):
    if isinstance(node, ast.FunctionDef):
        params = "; ".join(generate_arg(arg) for arg in node.args.args)
        body = "\n".join(generate_stmt(indent + 1, stmt) for stmt in node.body)

        return f"Definition {node.name} (args : list Value.t) : M :=\n" + \
            "  match args with\n" + \
            f"  | [{params}] => ltac:(M.monadic (\n" + \
            body + "))\n" \
            "  | _ => M.impossible\n" + \
            "  end."
    elif isinstance(node, ast.AsyncFunctionDef):
        return generate_error(node)
    elif isinstance(node, ast.ClassDef):
        return generate_error(node)
    elif isinstance(node, ast.Return):
        return generate_indent(indent) + "let _ := M.return (| " + generate_expr(node.value) + " |) in"
    elif isinstance(node, ast.Delete):
        return generate_error(node)
    elif isinstance(node, ast.Assign):
        if len(node.targets) >= 2:
            return generate_error(node)

        target = node.targets[0]

        if isinstance(target, ast.Name):
            return generate_indent(indent) + "let " + target.id + " := " + \
                generate_expr(node.value) + " in"

        return generate_indent(indent) + "let _ := M.assign (|\n" + \
            generate_indent(indent + 1) + generate_expr(target) + ",\n" + \
            generate_indent(indent + 1) + generate_expr(node.value) + "\n" +\
            generate_indent(indent) + "|) in"
    # elif isinstance(node, ast.TypeAlias):
    #     return generate_error(node)
    elif isinstance(node, ast.AugAssign):
        if isinstance(node.target, ast.Name):
            return generate_indent(indent) + "let " + node.target.id + " := " + \
                generate_operator(node.op) + "\n" + \
                generate_indent(indent + 1) + generate_expr(node.value) + "\n" + \
                generate_indent(indent + 1) + generate_expr(node.value) + " in"

        return generate_indent(indent) + "let _ := M.assign_op (|\n" + \
            generate_indent(indent + 1) + generate_operator(node.op) + ",\n" + \
            generate_indent(indent + 1) + generate_expr(node.target) + ",\n" + \
            generate_indent(indent + 1) + generate_expr(node.value) + "\n" +\
            generate_indent(indent) + "|) in"
    elif isinstance(node, ast.AnnAssign):
        return generate_error(node)
    elif isinstance(node, ast.For):
        return generate_indent(indent) + "For " + generate_expr(node.target) + " in " + \
            generate_expr(node.iter) + " do\n" + \
            "\n".join(generate_stmt(indent + 1, stmt) for stmt in node.body) + "\n" + \
            generate_indent(indent) + "EndFor."
    elif isinstance(node, ast.AsyncFor):
        return generate_error(node)
    elif isinstance(node, ast.While):
        return generate_indent(indent) + "While " + generate_expr(node.test) + " do\n" + \
            "\n".join(generate_stmt(indent + 1, stmt) for stmt in node.body) + "\n" + \
            generate_indent(indent) + "EndWhile."
    elif isinstance(node, ast.If):
        return generate_indent(indent) + "let _ :=\n" + \
            generate_indent(indent + 1) + "if M.is_true " + \
            generate_expr(node.test) + " then\n" + \
            "\n".join(generate_stmt(indent + 2, stmt) for stmt in node.body) + "\n" + \
            generate_indent(indent + 1) + "else\n" + \
            "\n".join(generate_stmt(indent + 2, stmt)
                      for stmt in node.orelse) + " in"
    elif isinstance(node, ast.With):
        generate_error(node)
    elif isinstance(node, ast.AsyncWith):
        return generate_error(node)
    elif isinstance(node, ast.Match):
        return generate_error(node)
    elif isinstance(node, ast.Raise):
        return generate_error(node)
    elif isinstance(node, ast.Try):
        generate_error(node)
    # elif isinstance(node, ast.TryStar):
    #     return generate_error(node)
    elif isinstance(node, ast.Assert):
        return generate_indent(indent) + "let _ := M.assert (| " + \
            generate_expr(node.test) + " |) in"
    elif isinstance(node, ast.Import):
        return "Require " + ", ".join(alias.name for alias in node.names) + "."
    elif isinstance(node, ast.ImportFrom):
        return "Require " + (node.module if node.module is not None else "?") + \
            ".[" + ", ".join(alias.name for alias in node.names) + "]."
    elif isinstance(node, ast.Global):
        return generate_error(node)
    elif isinstance(node, ast.Nonlocal):
        return generate_error(node)
    elif isinstance(node, ast.Expr):
        return generate_indent(indent) + "let _ := " + generate_expr(node.value) + " in"
    elif isinstance(node, ast.Pass):
        return generate_indent(indent) + "let _ := M.pass (| |) in"
    elif isinstance(node, ast.Break):
        return generate_indent(indent) + "let _ := M.break (| |) in"
    elif isinstance(node, ast.Continue):
        return generate_indent(indent) + "let _ := M.continue (| |) in"
    else:
        return generate_error(node)


def generate_expr(node):
    if isinstance(node, ast.BoolOp):
        return "(" + generate_boolop(node.op) + \
            " ".join(generate_expr(value) for value in node.values) + ")"
    elif isinstance(node, ast.NamedExpr):
        return generate_error(node)
    elif isinstance(node, ast.BinOp):
        return "(" + generate_operator(node.op) + " " + \
            generate_expr(node.left) + " " + generate_expr(node.right) + ")"
    elif isinstance(node, ast.UnaryOp):
        return "(" + generate_unaryop(node.op) + generate_expr(node.operand) + ")"
    elif isinstance(node, ast.Lambda):
        return f"(fun {generate_expr(node.args)} => {generate_expr(node.body)})"
    elif isinstance(node, ast.IfExp):
        return "(if M.is_true " + generate_expr(node.test) + " then " + \
            generate_expr(node.body) + " else " + \
            generate_expr(node.orelse) + ")"
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
        return f"(M.await (| {generate_expr(node.value)} |))"
    elif isinstance(node, ast.Yield):
        return f"(M.yield (| {generate_expr(node.value)} |))"
    elif isinstance(node, ast.YieldFrom):
        return f"(M.yield_from (| {generate_expr(node.value)} |))"
    elif isinstance(node, ast.Compare):
        if len(node.ops) >= 2 or len(node.comparators) >= 2:
            return generate_error(node)

        return f"({generate_cmpop(node.ops[0])} (| {generate_expr(node.left)}, {generate_expr(node.comparators[0])} |))"
    elif isinstance(node, ast.Call):
        return "(M.call (| " + generate_expr(node.func) + ", [" + \
            '; '.join(generate_expr(arg) for arg in node.args) + "] |))"
    elif isinstance(node, ast.FormattedValue):
        return generate_error(node)
    elif isinstance(node, ast.JoinedStr):
        return generate_error(node)
    elif isinstance(node, ast.Constant):
        return "(" + generate_constant(node, node.value) + ")"
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
        return "BoolOp.And"
    elif isinstance(node, ast.Or):
        return "BoolOp.Or"
    else:
        return generate_error(node)


def generate_operator(node):
    if isinstance(node, ast.Add):
        return "BinOp.Add"
    elif isinstance(node, ast.Sub):
        return "BinOp.Sub"
    elif isinstance(node, ast.Mult):
        return "BinOp.Mult"
    elif isinstance(node, ast.MatMult):
        return "BinOp.MatMult"
    elif isinstance(node, ast.Div):
        return "BinOp.Div"
    elif isinstance(node, ast.Mod):
        return "BinOp.Mod"
    elif isinstance(node, ast.Pow):
        return "BinOp.Pow"
    elif isinstance(node, ast.LShift):
        return "BinOp.LShift"
    elif isinstance(node, ast.RShift):
        return "BinOp.RShift"
    elif isinstance(node, ast.BitOr):
        return "BinOp.BitOr"
    elif isinstance(node, ast.BitXor):
        return "BinOp.BitXor"
    elif isinstance(node, ast.BitAnd):
        return "BinOp.BitAnd"
    elif isinstance(node, ast.FloorDiv):
        return "BinOp.FloorDiv"
    else:
        return generate_error(node)


def generate_unaryop(node):
    if isinstance(node, ast.Invert):
        return "UnOp.Invert"
    elif isinstance(node, ast.Not):
        return "UnOp.Not"
    elif isinstance(node, ast.UAdd):
        return "UnOp.Add"
    elif isinstance(node, ast.USub):
        return "UnOp.Sub"
    else:
        return generate_error(node)


def generate_cmpop(node):
    if isinstance(node, ast.Eq):
        return "Compare.Eq"
    elif isinstance(node, ast.NotEq):
        return "Compare.NotEq"
    elif isinstance(node, ast.Lt):
        return "Compare.Lt"
    elif isinstance(node, ast.LtE):
        return "Compare.LtE"
    elif isinstance(node, ast.Gt):
        return "Compare.Gt"
    elif isinstance(node, ast.GtE):
        return "Compare.GtE"
    elif isinstance(node, ast.Is):
        return "Compare.Is"
    elif isinstance(node, ast.IsNot):
        return "Compare.IsNot"
    elif isinstance(node, ast.In):
        return "Compare.In"
    elif isinstance(node, ast.NotIn):
        return "Compare.NotIn"
    else:
        return generate_error(node)


def generate_arg(node):
    return node.arg


file_name = "../execution-specs/src/ethereum/paris/vm/instructions/arithmetic.py"
file_content = open(file_name).read()
parsed_tree = ast.parse(file_content)

# print(ast.dump(parsed_tree, indent=4))

# Generate Coq code from the AST
coq_code = generate_mod(parsed_tree)

# Print the generated Coq code
print(coq_code)
