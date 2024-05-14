import ast
import os
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

    if kind == "expr":
        return f"Constant.str \"{message}\""

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
        return f"Constant.float \"{str(value)}\""
    elif isinstance(value, str):
        return "Constant.str \"" + value.replace("\"", "\"\"") + "\""
    elif isinstance(value, bytes):
        return "Constant.bytes \"" + value.hex() + "\""
    elif value == ...:
        return "Constant.ellipsis"
    else:
        return generate_error(f"constant {type(value)}", node)


def generate_mod(node: ast.mod):
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


def get_globals_of_import(node: ast.ImportFrom) -> str:
    module = node.module.replace(".", "/") if node.module is not None else ""

    # If this is an absolute import
    if node.level == 0:
        return module.replace("/", ".")

    # If this is a relative path
    actual_path = input_file_name
    for _ in range(node.level):
        actual_path = os.path.dirname(actual_path)
    if module != "":
        actual_path += "/" + module

    return actual_path.replace("/", ".")


def generate_top_level_stmt(node: ast.stmt):
    if isinstance(node, ast.FunctionDef):
        return f"Definition {generate_name(node.name)} : Value.t -> Value.t -> M :=\n" + \
            generate_indent(1) + generate_function_def_body(1, node) + ".\n\n" + \
            f"Axiom {generate_name(node.name)}_in_globals :\n" +\
            generate_indent(1) + \
            f"IsInGlobals globals \"{node.name}\" (make_function {generate_name(node.name)})."
    elif isinstance(node, ast.AsyncFunctionDef):
        return generate_error("top_level_stmt", node)
    elif isinstance(node, ast.ClassDef):
        text = f"Definition {generate_name(node.name)} : Value.t := "
        text += "builtins.make_klass {|\n"

        # Bases
        text += generate_indent(1) + "Klass.bases := ["
        not_first = False
        for base in node.bases:
            if not_first:
                text += ";"
            text += "\n"
            text += generate_indent(2)
            if isinstance(base, ast.Name):
                text += f"(globals, \"{generate_name(base.id)}\")"
            else:
                text += generate_error("base", base)
            not_first = True
        text += "\n"
        text += generate_indent(1) + "];\n"

        # Class methods
        text += generate_indent(1) + "Klass.class_methods := ["
        not_first = False
        for stmt in node.body:
            if isinstance(stmt, ast.FunctionDef) and len(stmt.decorator_list) == 1:
                decorator = stmt.decorator_list[0]
                if isinstance(decorator, ast.Name) and decorator.id == "classmethod":
                    if not_first:
                        text += ";"
                    text += "\n"
                    text += generate_indent(2) + "(\n"
                    text += generate_indent(3) + f"\"{stmt.name}\"," + "\n"
                    text += generate_indent(3)
                    text += generate_function_def_body(3, stmt) + "\n"
                    text += generate_indent(2) + ")"
                    not_first = True
        text += "\n"
        text += generate_indent(1) + "];\n"

        # Methods
        text += generate_indent(1) + "Klass.methods := ["
        not_first = False
        for stmt in node.body:
            if isinstance(stmt, ast.FunctionDef) and len(stmt.decorator_list) == 0:
                if not_first:
                    text += ";"
                text += "\n"
                text += generate_indent(2) + "(\n"
                text += generate_indent(3) + f"\"{stmt.name}\"," + "\n"
                text += generate_indent(3)
                text += generate_function_def_body(3, stmt) + "\n"
                text += generate_indent(2) + ")"
                not_first = True
        text += "\n"
        text += generate_indent(1) + "]\n"
        text += "|}."

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
        module = get_globals_of_import(node)
        snake_module = module.replace(".", "_")

        return "\n".join(
            f"Axiom {snake_module}_imports_{alias.name} :\n" +
            generate_indent(1) +
            f"IsImported globals \"{module}\" \"{alias.name}\"."
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
    params = "; ".join(f"\"{arg.arg}\"" for arg in node.args.args)
    body = generate_stmts(indent + 1, node.body)

    return "fun (args kwargs : Value.t) =>\n" + \
        generate_indent(indent + 1) + \
        f"let- locals_stack := M.create_locals locals_stack args kwargs [ {params} ] in\n" + \
        generate_indent(indent + 1) + "ltac:(M.monadic (\n" + \
        body + "))"


def generate_if_then_else(
    indent,
    condition: ast.expr,
    success: ast.expr | list[ast.stmt],
    error: ast.expr | list[ast.stmt],
):
    return generate_indent(indent) + "(* if *)\n" + \
        generate_indent(indent) + "M.if_then_else (|\n" + \
        generate_indent(indent + 1) + generate_expr(indent + 1, False, condition) + ",\n" + \
        generate_indent(indent) + "(* then *)\n" + \
        generate_indent(indent) + "ltac:(M.monadic (\n" + \
        (generate_expr(indent + 1, False, success)
         if isinstance(success, ast.expr)
         else generate_stmts(indent + 1, success)) + \
        "\n" + \
        generate_indent(indent) + "(* else *)\n" + \
        generate_indent(indent) + ")), ltac:(M.monadic (\n" + \
        (generate_expr(indent + 1, False, error)
         if isinstance(error, ast.expr)
         else generate_stmts(indent + 1, error)) + \
        "\n" + \
        generate_indent(indent) + ")) |)"


def generate_stmts(indent, nodes: list[ast.stmt]):
    return "\n".join(
        [generate_stmt(indent, stmt) for stmt in nodes] +
        [generate_indent(indent) + "M.pure Constant.None_"]
    )


def generate_stmt(indent, node: ast.stmt):
    if isinstance(node, ast.FunctionDef):
        return generate_error("stmt", node)
    elif isinstance(node, ast.AsyncFunctionDef):
        return generate_error("stmt", node)
    elif isinstance(node, ast.ClassDef):
        return generate_error("stmt", node)
    elif isinstance(node, ast.Return):
        return generate_indent(indent) + "let _ := M.return_ (|\n" + \
            generate_indent(indent + 1) + \
            (generate_expr(indent + 1, False, node.value)
             if node.value is not None
             else "Constant.None_") + \
            "\n" + \
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
            return generate_indent(indent) + "let _ := M.assign_local (|\n" + \
                generate_indent(indent + 1) + \
                "\"" + target.id + "\" ,\n" + \
                generate_indent(indent + 1) + \
                generate_expr(indent + 1, False, node.value) + "\n" + \
                generate_indent(indent) + "|) in"

        return generate_indent(indent) + "let _ := M.assign (|\n" + \
            generate_indent(indent + 1) + \
            generate_expr(indent + 1, False, target) + ",\n" + \
            generate_indent(indent + 1) + \
            generate_expr(indent + 1, False, node.value) + "\n" + \
            generate_indent(indent) + "|) in"
    # elif isinstance(node, ast.TypeAlias):
    #     return generate_error("stmt", node)
    elif isinstance(node, ast.AugAssign):
        if isinstance(node.target, ast.Name):
            return generate_indent(indent) + "let _ := M.assign_op_local (|\n" + \
                generate_indent(indent + 1) + generate_operator(node.op) + ",\n" + \
                generate_indent(indent + 1) + "\"" + node.target.id + "\",\n" + \
                generate_indent(indent + 1) + generate_expr(1, False, node.value) + "\n" +\
                generate_indent(indent) + "|) in"

        return generate_indent(indent) + "let _ := M.assign_op (|\n" + \
            generate_indent(indent + 1) + generate_operator(node.op) + ",\n" + \
            generate_indent(indent + 1) + generate_expr(1, False, node.target) + ",\n" + \
            generate_indent(indent + 1) + generate_expr(1, False, node.value) + "\n" +\
            generate_indent(indent) + "|) in"
    elif isinstance(node, ast.AnnAssign):
        return generate_error("stmt", node)
    elif isinstance(node, ast.For):
        return generate_indent(indent) + "let _ :=\n" + \
            generate_indent(indent + 1) + "M.for_ (|\n" + \
            generate_indent(indent + 2) + generate_expr(2, False, node.target) + ",\n" + \
            generate_indent(indent + 2) + generate_expr(2, False, node.iter) + ",\n" + \
            generate_indent(indent + 2) + "ltac:(M.monadic (\n" + \
            generate_stmts(indent + 3, node.body) + "\n" + \
            generate_indent(indent + 2) + ")),\n" + \
            generate_indent(indent + 2) + "ltac:(M.monadic (\n" + \
            generate_stmts(indent + 3, node.orelse) + "\n" + \
            generate_indent(indent + 2) + "))\n" + \
            generate_indent(indent) + "|) in"
    elif isinstance(node, ast.AsyncFor):
        return generate_error("stmt", node)
    elif isinstance(node, ast.While):
        return generate_indent(indent) + "let _ :=\n" + \
            generate_indent(indent + 1) + "M.while (|\n" + \
            generate_indent(indent + 2) + generate_expr(2, False, node.test) + ",\n" + \
            generate_indent(indent + 2) + "ltac:(M.monadic (\n" + \
            generate_stmts(indent + 3, node.body) + "\n" + \
            generate_indent(indent + 2) + ")),\n" + \
            generate_indent(indent + 2) + "ltac:(M.monadic (\n" + \
            generate_stmts(indent + 3, node.orelse) + "\n" + \
            generate_indent(indent + 2) + "))\n" + \
            generate_indent(indent) + "|) in"
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
            ("Some (" + generate_expr(indent, False, node.exc) + ")"
             if node.exc is not None
             else "None") + \
            " |) in"
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
        return generate_expr(indent, False, nodes[0])

    return paren(
        is_with_paren,
        op + " (|\n" +
        generate_indent(indent + 1) +
        generate_expr(indent + 1, False, nodes[0]) + ",\n" +
        generate_indent(indent + 1) + "ltac:(M.monadic (\n" +
        generate_indent(indent + 2) +
        generate_bool_op(indent + 2, False, op, nodes[1:]) + "\n" +
        generate_indent(indent + 1) + "))\n" +
        generate_indent(indent) + "|)"
    )


def generate_compare(indent, is_with_paren, op, left, right):
    return paren(
        is_with_paren,
        generate_cmpop(op) + " (|\n" +
        generate_indent(indent + 1) +
        generate_expr(indent + 1, False, left) + ",\n" +
        generate_indent(indent + 1) +
        generate_expr(indent + 1, False, right) + "\n" +
        generate_indent(indent) + "|)"
    )


def generate_compares(indent, is_with_paren, left, ops, comparators):
    if len(ops) == 0:
        raise ValueError("No comparison operators provided")
    elif len(ops) == 1:
        return generate_compare(indent, is_with_paren, ops[0], left, comparators[0])

    return paren(
        is_with_paren,
        "BoolOp.and (|\n" +
        generate_indent(indent + 1) +
        generate_compare(indent + 1, is_with_paren, ops[0], left, comparators[0]) + ",\n" +
        generate_indent(indent + 1) + "ltac:(M.monadic (\n" +
        generate_indent(indent + 2) +
        generate_compares(indent + 2, False, comparators[0], ops[1:], comparators[1:]) +
        "\n" +
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
        "make_list_concat (| [\n" +
        ';\n'.join(
            generate_indent(indent + 1) +
            generate_single_list_or_node(indent + 1, False, list_to_concat)
            for list_to_concat in lists_to_concat
        ) + "\n" +
        generate_indent(indent) + "] |)"
    )


def generate_expr(indent, is_with_paren, node: ast.expr):
    if isinstance(node, ast.BoolOp):
        return generate_bool_op(
            indent, is_with_paren, generate_boolop(node.op), node.values
        )
    elif isinstance(node, ast.NamedExpr):
        return generate_error("expr", node)
    elif isinstance(node, ast.BinOp):
        return paren(
            is_with_paren,
            generate_operator(node.op) + " (|\n" +
            generate_indent(indent + 1) +
            generate_expr(indent + 1, False, node.left) + ",\n" +
            generate_indent(indent + 1) +
            generate_expr(indent + 1, False, node.right) + "\n" +
            generate_indent(indent) + "|)"
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
            f"fun (args kwargs : Value.t) => {generate_expr(indent, False, node.body)}"
        )
    elif isinstance(node, ast.IfExp):
        return paren(
            is_with_paren,
            generate_if_then_else(indent, node.test, node.body, node.orelse)
        )
    elif isinstance(node, ast.Dict):
        return generate_error("expr", node)
    elif isinstance(node, ast.Set):
        return generate_error("expr", node)
    elif isinstance(node, ast.ListComp):
        return generate_error("expr", node)
    elif isinstance(node, ast.SetComp):
        return generate_error("expr", node)
    elif isinstance(node, ast.DictComp):
        return generate_error("expr", node)
    elif isinstance(node, ast.GeneratorExp):
        return generate_error("expr", node)
    elif isinstance(node, ast.Await):
        return paren(
            is_with_paren,
            f"M.await (| {generate_expr(indent, False, node.value)} |)"
        )
    elif isinstance(node, ast.Yield):
        return paren(
            is_with_paren,
            "M.yield (| " +
            (generate_expr(indent, False, node.value)
             if node.value is not None
             else "Constant.None_") +
            " |)"
        )
    elif isinstance(node, ast.YieldFrom):
        return paren(
            is_with_paren,
            f"M.yield_from (| {generate_expr(indent, False, node.value)} |)"
        )
    elif isinstance(node, ast.Compare):
        return generate_compares(
            indent, is_with_paren, node.left, node.ops, node.comparators
        )
    elif isinstance(node, ast.Call):
        return paren(
            is_with_paren,
            "M.call (|\n" +
            generate_indent(indent + 1) + generate_expr(indent + 1, False, node.func) +
            ",\n" +
            generate_indent(indent + 1) +
            generate_list(indent + 1, False, node.args) + ",\n" +
            generate_indent(indent + 1) + "make_dict []\n" +
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
        slice = node.slice

        if isinstance(slice, ast.Slice):
            return paren(
                is_with_paren,
                "M.slice (|\n" +
                generate_indent(indent + 1) +
                generate_expr(indent + 1, False, node.value) + ",\n" +
                generate_indent(indent + 1) +
                (generate_expr(indent + 1, False, slice.lower)
                 if slice.lower is not None
                 else "Constant.None_") + ",\n" +
                generate_indent(indent + 1) +
                (generate_expr(indent + 1, False, slice.upper)
                 if slice.upper is not None
                 else "Constant.None_") + ",\n" +
                generate_indent(indent + 1) +
                (generate_expr(indent + 1, False, slice.step)
                 if slice.step is not None
                 else "Constant.None_") + "\n" +
                generate_indent(indent) + "|)"
            )

        return paren(
            is_with_paren,
            "M.get_subscript (|\n" +
            generate_indent(indent + 1) +
            generate_expr(indent + 1, False, node.value) + ",\n" +
            generate_indent(indent + 1) +
            generate_expr(indent + 1, False, slice) + "\n" +
            generate_indent(indent) + "|)"
        )
    elif isinstance(node, ast.Starred):
        # We should handle this kind of expression as part of the enclosing expression
        return generate_error("expr", node)
    elif isinstance(node, ast.Name):
        return paren(
            is_with_paren,
            f"M.get_name (| globals, locals_stack, \"{node.id}\" |)"
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
        # This case is supposed to only appear as part of a Subscript node, so we
        # do not handle it here.
        return paren(
            is_with_paren,
            "M.slice (| " +
            (generate_expr(indent, False, node.lower)
             if node.lower is not None
             else "Constant.None_") +
            ", " +
            (generate_expr(indent, False, node.upper)
             if node.upper is not None
             else "Constant.None_") +
            " |)"
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
        return "Compare.in_"
    elif isinstance(node, ast.NotIn):
        return "Compare.not_in"
    else:
        return generate_error("cmpop", node)


def generate_arg(node):
    return generate_name(node.arg)


input_file_name = sys.argv[1]
output_file_name = "../../coq-of-python/CoqOfPython/" + \
    input_file_name.replace(".py", ".v")

file_content = open(input_file_name).read()
parsed_tree = ast.parse(file_content)

globals = input_file_name.replace("/", ".").replace(".py", "")

# Generate Coq code from the AST
coq_code = f"""Require Import CoqOfPython.CoqOfPython.

Definition globals : Globals.t := "{globals}".

Definition locals_stack : list Locals.t := [].

{generate_mod(parsed_tree)}
"""

# Ensure that the directory exists
output_directory = os.path.dirname(output_file_name)
if not os.path.exists(output_directory):
    os.makedirs(output_directory)

# Output the generated Coq code only if the content changed
if os.path.exists(output_file_name):
    with open(output_file_name, "r") as output_file:
        if output_file.read() == coq_code:
            sys.exit(0)
with open(output_file_name, "w") as output_file:
    output_file.write(coq_code)

# print(ast.dump(parsed_tree, indent=4))
