import ast
import sys


def generate_error(kind, node):
    message = f"(* At {kind}: unsupported node type: {type(node).__name__} *)"

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


def generate_name(name):
    reserved_names = {
        "Definition",
        "End",
        "Import",
        "in",
        "Ltac",
        "mod",
        "Module",
        "Require",
        "Set",
        "Type",
    }

    if name in reserved_names:
        return name + "_"

    return name


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
        return generate_error("constant", node)


def generate_mod(node):
    if isinstance(node, ast.Module):
        return "\n\n".join(generate_top_level_stmt(stmt) for stmt in node.body)
    elif isinstance(node, ast.Interactive):
        return generate_error("mod", node)
    elif isinstance(node, ast.Interactive):
        return generate_error("mod", node)
    elif isinstance(node, ast.Interactive):
        return generate_error("mod", node)
    else:
        return generate_error("mod", node)


def generate_top_level_stmt(node):
    if isinstance(node, ast.FunctionDef):
        params = "; ".join(generate_arg(arg) for arg in node.args.args)
        body = "\n".join(generate_stmt(1, stmt) for stmt in node.body)

        return f"Definition {node.name} (args : list Value.t) : M :=\n" + \
            "  match args with\n" + \
            f"  | [{params}] => ltac:(M.monadic (\n" + \
            body + "))\n" \
            "  | _ => M.impossible\n" + \
            "  end."
    elif isinstance(node, ast.AsyncFunctionDef):
        return generate_error("top_level_stmt", node)
    elif isinstance(node, ast.ClassDef):
        text = f"Definition {generate_name(node.name)} : Value.t :=\n"
        text += generate_indent(1) + \
            "Value.OfTy builtins.globals \"type\" (Value.Klass\n"

        # Bases
        text += generate_indent(2) + "["
        not_first = False
        for base in node.bases:
            if not_first:
                text += "; "
            if isinstance(base, ast.Name):
                text += f"(globals, \"{generate_name(base.id)}\")"
            else:
                text += generate_error("base", base)
            not_first = True
        text += "]\n"

        # Class methods
        text += generate_indent(2) + "["
        not_first = False
        for stmt in node.body:
            if isinstance(stmt, ast.FunctionDef):
                if len(stmt.decorator_list) == 1:
                    decorator = stmt.decorator_list[0]
                    if isinstance(decorator, ast.Name) and decorator.id == "classmethod":
                        if not_first:
                            text += "; "
                        text += f"\"{stmt.name}\""
                        not_first = True
        text += "]\n"

        # Methods
        text += generate_indent(2) + "["
        text += "]\n"

        text += generate_indent(1) + ")."

        return text
    elif isinstance(node, ast.Assign):
        if len(node.targets) >= 2:
            return generate_error("top_level_stmt", node)

        target = node.targets[0]

        if isinstance(target, ast.Name):
            return "Definition " + target.id + " : Value.t := M.run ltac:(M.monadic (\n" + \
                generate_indent(1) + generate_expr(node.value) + "))."

        return generate_error("top_level_stmt", node)
    elif isinstance(node, ast.Import):
        return generate_error("top_level_stmt", node)
    elif isinstance(node, ast.ImportFrom):
        module = node.module if node.module is not None else "__init__"
        snake_module = module.replace(".", "_")

        return f"Require {module}.\n" + \
            "\n".join(
                f"Axiom {snake_module}_{generate_name(alias.name)} :\n" +
                generate_indent(1) +
                f"IsGlobalAlias globals {module}.globals " +
                f"\"{generate_name(alias.name)}\"."
                for alias in node.names
            )
    elif isinstance(node, ast.Global):
        return generate_error("top_level_stmt", node)
    elif isinstance(node, ast.Nonlocal):
        return generate_error("top_level_stmt", node)
    elif isinstance(node, ast.Expr):
        return f"Definition expr_{node.lineno} : Value.t :=\n" + \
            generate_indent(1) + generate_expr(node.value) + "."
    else:
        return generate_error("top_level_stmt", node)


def generate_stmt(indent, node):
    if isinstance(node, ast.FunctionDef):
        return generate_error("stmt", node)
    elif isinstance(node, ast.AsyncFunctionDef):
        return generate_error("stmt", node)
    elif isinstance(node, ast.ClassDef):
        return generate_error("stmt", node)
    elif isinstance(node, ast.Return):
        return generate_indent(indent) + "let _ := M.return (| " + \
            generate_expr(node.value) + " |) in"
    elif isinstance(node, ast.Delete):
        return "\n".join(
            generate_indent(indent) + "let _ := M.delete (| " +
            generate_expr(target) + " |) in"
            for target in node.targets
        )
    elif isinstance(node, ast.Assign):
        if len(node.targets) >= 2:
            return generate_error("stmt", node)

        target = node.targets[0]

        if isinstance(target, ast.Name):
            return generate_indent(indent) + "let " + target.id + " := " + \
                generate_expr(node.value) + " in"

        return generate_indent(indent) + "let _ := M.assign (|\n" + \
            generate_indent(indent + 1) + generate_expr(target) + ",\n" + \
            generate_indent(indent + 1) + generate_expr(node.value) + "\n" + \
            generate_indent(indent) + "|) in"
    # elif isinstance(node, ast.TypeAlias):
    #     return generate_error("stmt", node)
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
        return generate_error("stmt", node)
    elif isinstance(node, ast.For):
        return generate_indent(indent) + "For " + generate_expr(node.target) + " in " + \
            generate_expr(node.iter) + " do\n" + \
            "\n".join(generate_stmt(indent + 1, stmt) for stmt in node.body) + "\n" + \
            generate_indent(indent) + "EndFor."
    elif isinstance(node, ast.AsyncFor):
        return generate_error("stmt", node)
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
        return generate_error("stmt", node)
    elif isinstance(node, ast.AsyncWith):
        return generate_error("stmt", node)
    elif isinstance(node, ast.Match):
        return generate_error("stmt", node)
    elif isinstance(node, ast.Raise):
        return generate_error("stmt", node)
    elif isinstance(node, ast.Try):
        return generate_error("stmt", node)
    # elif isinstance(node, ast.TryStar):
    #     return generate_error("stmt", node)
    elif isinstance(node, ast.Assert):
        return generate_indent(indent) + "let _ := M.assert (| " + \
            generate_expr(node.test) + " |) in"
    elif isinstance(node, ast.Import):
        return generate_error("stmt", node)
    elif isinstance(node, ast.ImportFrom):
        return generate_error("stmt", node)
    elif isinstance(node, ast.Global):
        return generate_error("stmt", node)
    elif isinstance(node, ast.Nonlocal):
        return generate_error("stmt", node)
    elif isinstance(node, ast.Expr):
        return generate_indent(indent) + "let _ := " + generate_expr(node.value) + " in"
    elif isinstance(node, ast.Pass):
        return generate_indent(indent) + "let _ := M.pass (| |) in"
    elif isinstance(node, ast.Break):
        return generate_indent(indent) + "let _ := M.break (| |) in"
    elif isinstance(node, ast.Continue):
        return generate_indent(indent) + "let _ := M.continue (| |) in"
    else:
        return generate_error("stmt", node)


def generate_expr(node):
    if isinstance(node, ast.BoolOp):
        return "(" + generate_boolop(node.op) + \
            " ".join(generate_expr(value) for value in node.values) + ")"
    elif isinstance(node, ast.NamedExpr):
        return generate_error("stmt", node)
    elif isinstance(node, ast.BinOp):
        return generate_operator(node.op) + " (| " + \
            generate_expr(node.left) + ", " + generate_expr(node.right) + " |)"
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
            return generate_error("stmt", node)

        return f"({generate_cmpop(node.ops[0])} (| {generate_expr(node.left)}, {generate_expr(node.comparators[0])} |))"
    elif isinstance(node, ast.Call):
        return "(M.call (| " + generate_expr(node.func) + ", [" + \
            '; '.join(generate_expr(arg) for arg in node.args) + "] |))"
    elif isinstance(node, ast.FormattedValue):
        return generate_error("stmt", node)
    elif isinstance(node, ast.JoinedStr):
        return generate_error("stmt", node)
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
        return generate_error("stmt", node)


def generate_boolop(node):
    if isinstance(node, ast.And):
        return "BoolOp.and"
    elif isinstance(node, ast.Or):
        return "BoolOp.or"
    else:
        return generate_error("boolop", node)


def generate_operator(node):
    if isinstance(node, ast.Add):
        return "BinOp.add"
    elif isinstance(node, ast.Sub):
        return "BinOp.sub"
    elif isinstance(node, ast.Mult):
        return "BinOp.mult"
    elif isinstance(node, ast.MatMult):
        return "BinOp.mat_mult"
    elif isinstance(node, ast.Div):
        return "BinOp.div"
    elif isinstance(node, ast.Mod):
        return "BinOp.mod_"
    elif isinstance(node, ast.Pow):
        return "BinOp.pow"
    elif isinstance(node, ast.LShift):
        return "BinOp.l_shift"
    elif isinstance(node, ast.RShift):
        return "BinOp.r_shift"
    elif isinstance(node, ast.BitOr):
        return "BinOp.bit_or"
    elif isinstance(node, ast.BitXor):
        return "BinOp.bit_xor"
    elif isinstance(node, ast.BitAnd):
        return "BinOp.bit_and"
    elif isinstance(node, ast.FloorDiv):
        return "BinOp.floor_div"
    else:
        return generate_error("operator", node)


def generate_unaryop(node):
    if isinstance(node, ast.Invert):
        return "UnOp.invert"
    elif isinstance(node, ast.Not):
        return "UnOp.not"
    elif isinstance(node, ast.UAdd):
        return "UnOp.add"
    elif isinstance(node, ast.USub):
        return "UnOp.sub"
    else:
        return generate_error("unaryop", node)


def generate_cmpop(node):
    if isinstance(node, ast.Eq):
        return "Compare.eq"
    elif isinstance(node, ast.NotEq):
        return "Compare.not_eq"
    elif isinstance(node, ast.Lt):
        return "Compare.lt"
    elif isinstance(node, ast.LtE):
        return "Compare.lt_e"
    elif isinstance(node, ast.Gt):
        return "Compare.gt"
    elif isinstance(node, ast.GtE):
        return "Compare.gt_e"
    elif isinstance(node, ast.Is):
        return "Compare.is"
    elif isinstance(node, ast.IsNot):
        return "Compare.is_not"
    elif isinstance(node, ast.In):
        return "Compare.in"
    elif isinstance(node, ast.NotIn):
        return "Compare.not_in"
    else:
        return generate_error("cmpop", node)


def generate_arg(node):
    return node.arg


input_file_name = "../execution-specs/src/ethereum/" + sys.argv[1]
output_file_name = "CoqOfPython/ethereum/" + sys.argv[1].replace(".py", ".v")

file_content = open(input_file_name).read()
parsed_tree = ast.parse(file_content)

# Generate Coq code from the AST
coq_code = f"""Require Import CoqOfPython.CoqOfPython.

Inductive globals : Set :=.

{generate_mod(parsed_tree)}
"""

# Output the generated Coq code
with open(output_file_name, "w") as output_file:
    output_file.write(coq_code)

# print(ast.dump(parsed_tree, indent=4))
