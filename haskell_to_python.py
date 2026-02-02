import re
from dataclasses import dataclass
from textwrap import indent
import keyword


@dataclass
class TopLevel: pass

@dataclass
class Expr: pass

@dataclass
class Var(Expr):
    name: str


@dataclass
class Constr(Expr):
    name: str
    args: list[Expr]

@dataclass
class App(Expr):
    func: str
    args: list[Expr]

@dataclass
class Case(Expr):
    scrut: Expr
    alts: list[Expr]

@dataclass
class Alt:
    pattern: 'Pattern'
    body: Expr

@dataclass
class Pattern: pass

@dataclass
class PVar(Pattern):
    name: str

@dataclass
class PWild(Pattern): pass

@dataclass
class PConstr(Pattern):
    name: str
    vars: list[str]

@dataclass
class TConstr:
    name:  str
    tvars: list[str]

@dataclass
class DConstr:
    name: str
    args: list[TConstr]

@dataclass
class Data(TopLevel):
    datatype: TConstr
    constrs: list[DConstr]

@dataclass
class FunType:
    fun_type: list

@dataclass
class FunDecl:
    name: str
    fun_type: FunType

@dataclass
class FunClause:
    name: str
    binders: list[str]
    expr: Expr

@dataclass
class Function(TopLevel):
    declaration: FunDecl
    clause: FunClause

# =============================================================
# UTILITIES
# =============================================================
def clean(s: str) -> str:
    return '\n'.join(line.rstrip() for line in s.strip().splitlines())

def indent_lines(s: str, n: int = 4) -> str:
    return indent(s, ' ' * n)

def safe_py_name(name: str) -> str:
    cleaned = re.sub(r'[^0-9a-zA-Z_]', '_', name)

    if re.match(r'^[0-9]', cleaned):
        cleaned = "py_" + cleaned

    if keyword.iskeyword(cleaned) or cleaned in {"True", "False", "None"}:
        cleaned = cleaned + "_"

    if not cleaned:
        cleaned = "_"

    return cleaned

def apply_safe_names(unsafe):
    match unsafe:
        case Var():
            return Var(safe_py_name(unsafe.name))
        case Constr():
            return Constr(safe_py_name(unsafe.name), [apply_safe_names(e) for e in unsafe.args])
        case App():
            return App(safe_py_name(unsafe.func), [apply_safe_names(e) for e in unsafe.args])
        case Case():
            return Case(apply_safe_names(unsafe.scrut), [apply_safe_names(e) for e in unsafe.alts])
        case Alt():
            return Alt(apply_safe_names(unsafe.pattern), apply_safe_names(unsafe.body))
        case PVar():
            return PVar(safe_py_name(unsafe.name))
        case PConstr():
            return PConstr(safe_py_name(unsafe.name), [safe_py_name(e) for e in unsafe.vars])
        case TConstr():
            return TConstr(safe_py_name(unsafe.name), [safe_py_name(e) for e in unsafe.tvars])
        case DConstr():
            return DConstr(safe_py_name(unsafe.name), [apply_safe_names(e) for e in unsafe.args])
        case Data():
            return Data(apply_safe_names(unsafe.datatype), [apply_safe_names(e) for e in unsafe.constrs])
        case FunType():
            return FunType([apply_safe_names(e) for e in unsafe.fun_type])
        case FunDecl():
            return FunDecl(safe_py_name(unsafe.name), apply_safe_names(unsafe.fun_type))
        case FunClause():
            return FunClause(safe_py_name(unsafe.name), [safe_py_name(e) for e in unsafe.binders], apply_safe_names(unsafe.expr))
        case Function():
            return Function(apply_safe_names(unsafe.declaration), apply_safe_names(unsafe.clause))

# =============================================================
# TOKENIZER
# =============================================================
@dataclass
class Token:
    kind: str
    value: str

def tokenize(src: str):
    tokens = []
    i = 0
    decl = False
    while i < len(src):
        c = src[i]
        if decl and c == "\n":
            tokens.append(Token("ENDL", "\n"))
            i += 1
            decl = False
            continue
        if c.isspace():
            i += 1
            continue
        if src.startswith("->", i):
            tokens.append(Token("ARROW", "->"))
            i += 2
            continue
        if src.startswith("::", i):
            tokens.append(Token("::", "::"))
            i += 2
            decl = True
            continue
        if c in "{}();|=":
            tokens.append(Token(c, c))
            i += 1
            continue
        m = re.match(r"[0-9]+", src[i:])
        if m:
            tokens.append(Token("INT", m.group(0)))
            i += len(m.group(0))
            continue
        m = re.match(r"[a-zA-Z_][a-zA-Z0-9_']*", src[i:])
        if m:
            v = m.group(0)
            if v == "data": tokens.append(Token("DATA", v))
            elif v == "case": tokens.append(Token("CASE", v))
            elif v == "of": tokens.append(Token("OF", v))
            else: tokens.append(Token("IDENT", v))
            i += len(v)
            continue
        raise ValueError(f"Unexpected char {c}")
    return tokens

# =============================================================
# PARSER
# =============================================================
class Parser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.i = 0

    def peek(self, kind=None):
        if self.i >= len(self.tokens): return None
        t = self.tokens[self.i]
        if kind is None or t.kind == kind: return t
        return None

    def eat(self, kind=None):
        if self.i >= len(self.tokens): raise ValueError("Unexpected EOF")
        t = self.tokens[self.i]
        if kind and t.kind != kind: raise ValueError(f"Expected {kind} got {t.kind}")
        self.i += 1
        return t

    # -----------------------
    # TOP-LEVEL DECLARATION
    # -----------------------
    def parse_top_level(self):
        if self.peek("DATA"): return self.parse_data()
        return self.parse_function()
    # -----------------------
    # DATA DECLARATION
    # -----------------------
    def parse_data(self):
        self.eat("DATA")
        dtype = self.parse_type_constructor()
        constrs = []
        if not self.peek("="):
            return Data(dtype, constrs)
        self.eat("=")
        while True:
            constrs.append(self.parse_constructor())
            nxt = self.peek()
            if nxt and nxt.kind == "|":
                self.eat("|")
            else:
                break
        return Data(dtype, constrs)
    
    def parse_constructor(self):
        name = self.eat("IDENT").value
        args = []
        while True:
            nxt = self.peek()
            if nxt and nxt.kind == "IDENT":
                args.append(TConstr(self.eat("IDENT").value, []))
            elif nxt and nxt.kind == "(":
                self.eat("(")
                args.append(self.parse_function_type())
                self.eat(")")
            else:
                break
        return DConstr(name, args)

    def parse_type_constructor(self):
        name = self.eat("IDENT").value
        vars = []
        while self.peek("IDENT"):
            vars.append(self.eat("IDENT").value)
        return TConstr(name, vars)
    # -----------------------
    # FUNCTION DECLARATION
    # -----------------------
    def parse_function(self):
        decl = self.parse_function_declaration()
        self.eat("ENDL")
        clause = self.parse_function_clause()
        return Function(decl, clause)
    
    def parse_function_declaration(self):
        name = self.eat("IDENT").value
        self.eat("::")
        fun_type = self.parse_function_type()
        return FunDecl(name, fun_type)
    
    def parse_function_type(self):
        types = []
        while True:
            if self.peek("("):
                self.eat("(")
                types.append(self.parse_function_type())
                self.eat(")")
            else:
                types.append(self.parse_type_constructor())
            if self.peek("ARROW"):
                self.eat("ARROW")
            else:
                break
        return FunType(types)
                
    
    def parse_function_clause(self):
        name = self.eat("IDENT").value
        binders = []
        while not self.peek("="):
            binders.append(self.eat("IDENT").value)
        self.eat("=")
        expr = self.parse_expr()
        return FunClause(name, binders, expr)
        
    # -----------------------
    # EXPRESSION
    # -----------------------
    def parse_expr(self):
        if self.peek("CASE"): return self.parse_case()
        return self.parse_app()

    # -----------------------
    # CASE
    # -----------------------
    def parse_case(self):
        self.eat("CASE")
        scrut = self.parse_expr()
        self.eat("OF")
        self.eat("{")
        alts = self.parse_alts()
        self.eat("}")
        return Case(scrut, alts)

    def parse_alts(self):
        alts = [self.parse_alt()]
        while self.peek(";"):
            self.eat(";")
            alts.append(self.parse_alt())
        return alts

    def parse_alt(self):
        pat = self.parse_pattern()
        self.eat("ARROW")
        body = self.parse_expr()
        return Alt(pat, body)

    # -----------------------
    # PATTERNS
    # -----------------------
    def parse_pattern(self):
        tok = self.peek()   
        if tok.kind == "IDENT":
            name = self.eat("IDENT").value
            vars = []
            while self.peek("IDENT"):
                vars.append(self.eat("IDENT").value)
            if name[0].isupper(): return PConstr(name, vars)
            return PVar(name)
        if tok.kind == "_":
            self.eat("_")
            return PWild()
        raise ValueError("Invalid pattern")

    # -----------------------
    # APPLICATION / ATOMS
    # -----------------------
    def parse_app(self):
        atom = self.parse_atom()
        match atom:
            case Var() | Constr():
                args = []
                while True:
                    nxt = self.peek()
                    if nxt and nxt.kind in ("IDENT", "INT", "("):
                        args.append(self.parse_atom())
                    else:
                        break
                if atom.name[0].isupper():
                    return Constr(atom.name, args)
                if len(args) > 0:
                    return App(atom.name, args)
                return atom
            case _:
                return atom

    def parse_atom(self):
        tok = self.peek()
        if tok.kind == "IDENT":
            v = self.eat("IDENT").value
            if v[0].isupper():
                return Constr(v, [])
            return Var(v)
        if tok.kind == "(":
            self.eat("(")
            e = self.parse_expr()
            self.eat(")")
            return e
        raise ValueError("Bad atom")

# =============================================================
# TRANSLATION
# =============================================================
def translate_top_level(tl: TopLevel):
    match tl:
        case Data():
            return translate_data(tl)
        case Function():
            return translate_function(tl)
        
def translate_data(data: Data):
    lines = []
    name = data.datatype.name
    lines.append(f"class {name}:\n    pass")
    for con in data.constrs:
        con_class = []
        con_name = con.name
        con_class.append(f"@dataclass\nclass {con_name}({name}):")
        if len(con.args) == 0:
            con_class.append("    pass")
        else:
            fields = []
            for i, tok in enumerate(con.args):
                fields.append(f"field{i}")
            fields_decl = [f"    {f}: object" for f in fields]
            con_class += fields_decl
        lines.append("\n".join(con_class))
    return "\n\n".join(lines)

def translate_function(func: Function):
    #the declaration is ignored
    name = func.clause.name
    args = ", ".join(func.clause.binders)
    definition = f"def {name}({args}):"
    expr = translate_expression(func.clause.expr)
    if "\n" in expr:
        return definition + "\n" + indent_lines(expr, 4)
    return definition + "\n    return " + expr


def translate_expression(expr: Expr):
    match expr:
        case Var():
            return expr.name
        case Constr():
            args = ", ".join([translate_expression(arg) for arg in expr.args])
            return f"{expr.name}({args})"
        case App():
            args = ", ".join([translate_expression(arg) for arg in expr.args])
            return f"{expr.func}({args})"
        case Case():
            return translate_case(expr)
        case Alt():
            raise ValueError("rogue alt")

def translate_case(case: Case):
    lines = []
    scrut = translate_expression(case.scrut)
    for alt in case.alts:
        extra = []
        body = translate_expression(alt.body)
        match alt.pattern:
            case PVar():
                cond = f"if {scrut} == {alt.pattern.name}:"
            case PWild():
                cond = "if True:"
            case PConstr():
                cond = f"if isinstance({scrut}, {alt.pattern.name}):"
                for i, v in enumerate(alt.pattern.vars):
                    extra.append(f"    {v} = {scrut}.field{i}")
        lines.append(cond)
        if len(extra) > 0:
            lines += extra
        if "\n" in body:
            lines.append(indent_lines(body, 4))
        else:
            lines.append("    return " + body)
    lines.append("raise ValueError(\"Non-exhaustive patterns in function\")")
    return "\n".join(lines)

# =============================================================
# PUBLIC API
# =============================================================
def parse_hs_top_level(src: str) -> TopLevel:
    tokens = tokenize(src)
    parser = Parser(tokens)
    return parser.parse_top_level()