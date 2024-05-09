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
        "left",
        "Ltac",
        "mod",
        "Module",
        "Parameter",
        "Require",
        "right",
        "Set",
        "Type",
    }

    if name in reserved_names:
        return name + "_"

    return name


def generate_constant(node, value):
    if value is None:
        return "Constant.None_"
    elif value is True:
        return "Constant.bool true"
    elif value is False:
        return "Constant.bool false"
    elif isinstance(value, int):
        return f"Constant.int {str(value)}"
    elif isinstance(value, float):
        return f"Value.Float {str(value)}"
    elif isinstance(value, str):
        return "Constant.str \"" + value.replace("\"", "\"\"\"") + "\""
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
            "builtins.make_klass\n"

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
        text += generate_indent(2) + "[\n"
        not_first = False
        for stmt in node.body:
            if isinstance(stmt, ast.FunctionDef) and len(stmt.decorator_list) == 1:
                decorator = stmt.decorator_list[0]
                if isinstance(decorator, ast.Name) and decorator.id == "classmethod":
                    if not_first:
                        text += ";\n"
                    text += generate_indent(3) + "(\n"
                    text += generate_indent(4) + f"\"{stmt.name}\"," + "\n"
                    text += generate_function_def_body(4, stmt) + "\n"
                    text += generate_indent(3) + ")"
                    not_first = True
        text += "\n"
        text += generate_indent(2) + "]\n"

        # Methods
        text += generate_indent(2) + "[\n"
        not_first = False
        for stmt in node.body:
            if isinstance(stmt, ast.FunctionDef) and len(stmt.decorator_list) == 0:
                if not_first:
                    text += ";\n"
                text += generate_indent(3) + "(\n"
                text += generate_indent(4) + f"\"{stmt.name}\"," + "\n"
                text += generate_function_def_body(4, stmt) + "\n"
                text += generate_indent(3) + ")"
                not_first = True
        text += "\n"
        text += generate_indent(2) + "]."

        return text
    elif isinstance(node, ast.Assign):
        if len(node.targets) >= 2:
            return generate_error("top_level_stmt", node)

        target = node.targets[0]

        if isinstance(target, ast.Name):
            return "Definition " + target.id + \
                " : Value.t := M.run ltac:(M.monadic (\n" + \
                generate_indent(1) + generate_expr(1, False, node.value) + "\n" + \
                "))."

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
            generate_indent(1) + generate_expr(1, False, node.value) + "."
    else:
        return generate_error("top_level_stmt", node)


def generate_function_def_body(indent, node):
    params = "; ".join(generate_arg(arg) for arg in node.args.args)
    body = generate_stmts(indent + 2, node.body)

    return generate_indent(indent) + "fun (args : list Value.t) =>\n" + \
        generate_indent(indent + 1) + "match args with\n" + \
        generate_indent(indent + 1) + f"| [{params}] => ltac:(M.monadic (\n" + \
        generate_indent(indent + 2) + "let _ := M.set_locals (| [" + \
        "; ".join(
            f"(\"{arg.arg}\", {generate_arg(arg)})" for arg in node.args.args
    ) + "] |) in\n" + \
        body + "))\n" + \
        generate_indent(indent + 1) + "| _ => M.impossible\n" + \
        generate_indent(indent + 1) + "end"


def generate_if_then_else(indent, condition, success, error):
    return generate_indent(indent) + "(* if *)\n" + \
        generate_indent(indent) + "M.if_then_else (|\n" + \
        generate_indent(indent + 1) + generate_expr(indent + 1, False, condition) + ",\n" + \
        generate_indent(indent) + "(* then *)\n" + \
        generate_indent(indent) + "ltac:(M.monadic (\n" + \
        generate_stmts(indent + 1, success) + "\n" + \
        generate_indent(indent) + "(* else *)\n" + \
        generate_indent(indent) + ")), ltac:(M.monadic (\n" + \
        generate_stmts(indent + 1, error) + "\n" + \
        generate_indent(indent) + ")) |)"


def generate_stmts(indent, nodes):
    return "\n".join(
        [generate_stmt(indent, stmt) for stmt in nodes] +
        [generate_indent(indent) + "M.pure Constant.None_"]
    )


def generate_stmt(indent, node):
    if isinstance(node, ast.FunctionDef):
        return generate_error("stmt", node)
    elif isinstance(node, ast.AsyncFunctionDef):
        return generate_error("stmt", node)
    elif isinstance(node, ast.ClassDef):
        return generate_error("stmt", node)
    elif isinstance(node, ast.Return):
        return generate_indent(indent) + "let _ := M.return_ (|\n" + \
            generate_indent(indent + 1) + \
            generate_expr(indent + 1, False, node.value) + "\n" + \
            generate_indent(indent) + "|) in"
    elif isinstance(node, ast.Delete):
        return "\n".join(
            generate_indent(indent) + "let _ := M.delete (| " +
            generate_expr(1, False, target) + " |) in"
            for target in node.targets
        )
    elif isinstance(node, ast.Assign):
        if len(node.targets) >= 2:
            return generate_error("stmt", node)

        target = node.targets[0]

        if isinstance(target, ast.Name):
            return generate_indent(indent) + "let " + target.id + " :=\n" + \
                generate_indent(indent + 1) + \
                generate_expr(indent + 1, False, node.value) + " in"

        return generate_indent(indent) + "let _ := M.assign (|\n" + \
            generate_indent(indent + 1) + generate_expr(1, False, target) + ",\n" + \
            generate_indent(indent + 1) + generate_expr(1, False, node.value) + "\n" + \
            generate_indent(indent) + "|) in"
    # elif isinstance(node, ast.TypeAlias):
    #     return generate_error("stmt", node)
    elif isinstance(node, ast.AugAssign):
        if isinstance(node.target, ast.Name):
            return generate_indent(indent) + "let " + node.target.id + " := " + \
                generate_operator(node.op) + "\n" + \
                generate_indent(indent + 1) + generate_expr(1, False, node.value) + "\n" + \
                generate_indent(indent + 1) + \
                generate_expr(1, False, node.value) + " in"

        return generate_indent(indent) + "let _ := M.assign_op (|\n" + \
            generate_indent(indent + 1) + generate_operator(node.op) + ",\n" + \
            generate_indent(indent + 1) + generate_expr(1, False, node.target) + ",\n" + \
            generate_indent(indent + 1) + generate_expr(1, False, node.value) + "\n" +\
            generate_indent(indent) + "|) in"
    elif isinstance(node, ast.AnnAssign):
        return generate_error("stmt", node)
    elif isinstance(node, ast.For):
        return generate_indent(indent) + "For " + generate_expr(1, False, node.target) + " in " + \
            generate_expr(1, False, node.iter) + " do\n" + \
            "\n".join(generate_stmt(indent + 1, stmt) for stmt in node.body) + "\n" + \
            generate_indent(indent) + "EndFor."
    elif isinstance(node, ast.AsyncFor):
        return generate_error("stmt", node)
    elif isinstance(node, ast.While):
        return generate_indent(indent) + "While " + generate_expr(1, False, node.test) + " do\n" + \
            "\n".join(generate_stmt(indent + 1, stmt) for stmt in node.body) + "\n" + \
            generate_indent(indent) + "EndWhile."
    elif isinstance(node, ast.If):
        return generate_indent(indent) + "let _ :=\n" + \
            generate_if_then_else(indent + 1, node.test, node.body, node.orelse) + \
            " in"
    elif isinstance(node, ast.With):
        return generate_error("stmt", node)
    elif isinstance(node, ast.AsyncWith):
        return generate_error("stmt", node)
    elif isinstance(node, ast.Match):
        return generate_error("stmt", node)
    elif isinstance(node, ast.Raise):
        return generate_indent(indent) + "let _ := M.raise (| " + \
            generate_expr(indent, False, node.exc) + " |) in"
    elif isinstance(node, ast.Try):
        return generate_error("stmt", node)
    # elif isinstance(node, ast.TryStar):
    #     return generate_error("stmt", node)
    elif isinstance(node, ast.Assert):
        return generate_indent(indent) + "let _ := M.assert (| " + \
            generate_expr(1, False, node.test) + " |) in"
    elif isinstance(node, ast.Import):
        return generate_error("stmt", node)
    elif isinstance(node, ast.ImportFrom):
        return generate_error("stmt", node)
    elif isinstance(node, ast.Global):
        return generate_error("stmt", node)
    elif isinstance(node, ast.Nonlocal):
        return generate_error("stmt", node)
    elif isinstance(node, ast.Expr):
        return generate_indent(indent) + "let _ := " + generate_expr(1, False, node.value) + " in"
    elif isinstance(node, ast.Pass):
        return generate_indent(indent) + "let _ := M.pass (| |) in"
    elif isinstance(node, ast.Break):
        return generate_indent(indent) + "let _ := M.break (| |) in"
    elif isinstance(node, ast.Continue):
        return generate_indent(indent) + "let _ := M.continue (| |) in"
    else:
        return generate_error("stmt", node)


def paren(is_with_paren, text):
    return "(" + text + ")" if is_with_paren else text


def generate_bool_op(indent, is_with_paren, op, nodes):
    if len(nodes) == 0:
        return generate_error("expr", nodes)
    elif len(nodes) == 1:
        return generate_expr(indent + 1, False, nodes[0])

    return paren(
        is_with_paren,
        generate_boolop(op) + " (|\n" +
        generate_indent(indent + 1) +
        generate_expr(indent + 1, False, nodes[0]) + ",\n" +
        generate_indent(indent + 1) + "ltac:(M.monadic (\n" +
        generate_indent(indent + 2) +
        generate_bool_op(indent + 2, False, op, nodes[1:]) + "\n" +
        generate_indent(indent + 1) + "))\n" +
        generate_indent(indent) + "|)"
    )


def generate_single_list_or_node(indent, is_with_paren, nodes):
    if isinstance(nodes, list):
        return paren(
            is_with_paren,
            "make_list [\n" +
            ';\n'.join(
                generate_indent(indent + 1) +
                generate_expr(indent + 1, False, node)
                for node in nodes
            ) + "\n" +
            generate_indent(indent) + "]"
        )

    # In this case the [nodes] expression represents a list, but is not syntactically as
    # a list.
    return generate_expr(indent, is_with_paren, nodes)


def generate_list(indent, is_with_paren, nodes):
    lists_to_concat = []
    current_list = []

    for node in nodes:
        if isinstance(node, ast.Starred):
            if len(current_list) > 0:
                lists_to_concat.append(current_list)
            lists_to_concat.append(node.value)
            current_list = []
        else:
            current_list.append(node)

    if len(current_list) > 0:
        lists_to_concat.append(current_list)

    if len(lists_to_concat) == 0:
        return paren(
            is_with_paren,
            "make_list []"
        )
    elif len(lists_to_concat) == 1:
        return generate_single_list_or_node(indent, is_with_paren, lists_to_concat[0])

    return paren(
        is_with_paren,
        "make_list_concat [\n" +
        ';\n'.join(
            generate_indent(indent + 1) +
            generate_single_list_or_node(indent + 1, False, list_to_concat)
            for list_to_concat in lists_to_concat
        ) + "\n" +
        generate_indent(indent) + "]"
    )


def generate_expr(indent, is_with_paren, node):
    if isinstance(node, ast.BoolOp):
        return generate_bool_op(indent, is_with_paren, node.op, node.values)
    elif isinstance(node, ast.NamedExpr):
        return generate_error("expr", node)
    elif isinstance(node, ast.BinOp):
        return paren(
            is_with_paren,
            generate_operator(node.op) + " (| " +
            generate_expr(indent, False, node.left) + ", " +
            generate_expr(indent, False, node.right) + " |)"
        )
    elif isinstance(node, ast.UnaryOp):
        return paren(
            is_with_paren,
            generate_unaryop(node.op) + " (| " +
            generate_expr(indent, False, node.operand) +
            " |)"
        )
    elif isinstance(node, ast.Lambda):
        return paren(
            is_with_paren,
            f"fun {generate_expr(indent, False, node.args)} => {generate_expr(indent, False, node.body)}"
        )
    elif isinstance(node, ast.IfExp):
        return paren(
            is_with_paren,
            generate_if_then_else(0, node.test, node.body, node.orelse)
        )
    elif isinstance(node, ast.Dict):
        return "{" + ", ".join(generate_expr(indent, False, key) + ": " + generate_expr(indent, False, value) for key, value in zip(node.keys, node.values)) + "}"
    elif isinstance(node, ast.Set):
        return "{" + ", ".join(generate_expr(indent, False, elt) for elt in node.elts) + "}"
    elif isinstance(node, ast.ListComp):
        return f"[{generate_expr(indent, False, node.elt)} for {generate_expr(indent, False, node.generators)}]"
    elif isinstance(node, ast.SetComp):
        return f"{{{generate_expr(indent, False, node.elt)} for {generate_expr(indent, False, node.generators)}}}"
    elif isinstance(node, ast.DictComp):
        return f"{{{generate_expr(indent, False, node.key)}: {generate_expr(indent, False, node.value)} for {generate_expr(indent, False, node.generators)}}}"
    elif isinstance(node, ast.GeneratorExp):
        return f"({generate_expr(indent, False, node.elt)} for {generate_expr(indent, False, node.generators)})"
    elif isinstance(node, ast.Await):
        return paren(
            is_with_paren,
            f"M.await (| {generate_expr(indent, False, node.value)} |)"
        )
    elif isinstance(node, ast.Yield):
        return paren(
            is_with_paren,
            f"M.yield (| {generate_expr(indent, False, node.value)} |)"
        )
    elif isinstance(node, ast.YieldFrom):
        return paren(
            is_with_paren,
            f"M.yield_from (| {generate_expr(indent, False, node.value)} |)"
        )
    elif isinstance(node, ast.Compare):
        if len(node.ops) >= 2 or len(node.comparators) >= 2:
            return generate_error("expr", node)

        return paren(
            is_with_paren,
            f"{generate_cmpop(node.ops[0])} (| {generate_expr(indent, False, node.left)}, {generate_expr(indent, False, node.comparators[0])} |)"
        )
    elif isinstance(node, ast.Call):
        return paren(
            is_with_paren,
            "M.call (|\n" +
            generate_indent(indent + 1) + generate_expr(indent + 1, False, node.func) +
            ", [" +
            ("\n" if len(node.args) >= 1 else "") +
            ';\n'.join(
                generate_indent(indent + 1) +
                generate_expr(indent + 1, False, arg)
                for arg in node.args
            ) + "]\n" +
            generate_indent(indent) + "|)"
        )
    elif isinstance(node, ast.FormattedValue):
        return generate_error("expr", node)
    elif isinstance(node, ast.JoinedStr):
        return generate_error("expr", node)
    elif isinstance(node, ast.Constant):
        return paren(
            is_with_paren,
            generate_constant(node, node.value)
        )
    elif isinstance(node, ast.Attribute):
        return paren(
            is_with_paren,
            f"M.get_field (| {generate_expr(indent, False, node.value)}, \"{node.attr}\" |)"
        )
    elif isinstance(node, ast.Subscript):
        return paren(
            is_with_paren,
            f"M.get_subscript (| {generate_expr(indent, False, node.value)}, {generate_expr(indent, False, node.slice)} |)"
        )
    elif isinstance(node, ast.Starred):
        # We should handle this kind of expression as part of the enclosing expression
        return generate_error("expr", node)
    elif isinstance(node, ast.Name):
        return paren(
            is_with_paren,
            f"M.get_name (| globals, \"{node.id}\" |)"
        )
    elif isinstance(node, ast.List):
        return generate_list(indent, is_with_paren, node.elts)
    elif isinstance(node, ast.Tuple):
        return paren(
            is_with_paren,
            "make_tuple [ " +
            "; ".join(generate_expr(indent, False, elt) for elt in node.elts) +
            " ]"
        )
    elif isinstance(node, ast.Slice):
        return paren(
            is_with_paren,
            f"{generate_expr(indent, False, node.lower)}:{generate_expr(indent, False, node.upper)}"
        )
    else:
        return generate_error("expr", node)


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
    return generate_name(node.arg)


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
