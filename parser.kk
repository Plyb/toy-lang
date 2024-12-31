import ast-simple
import std/text/parse
import tokenizer
import std/core/undiv
import non-empty-list

type exp {
  IntE(n: int)
  BlockE(exps: non-empty-list<exp_with_pos>)
  FnE(params: list<string>, body: exp_with_pos)
  IdE(name: string)
  AppE(operator: exp_with_pos, operands: list<exp_with_pos>)
  ValE(name: string, right_hand_side: exp_with_pos)
  DefE(name: string, params: list<string>, body: exp_with_pos)
  TypeDefE(name: string, options: non-empty-list<constructor_def>)
  MatchE(discriminee: exp_with_pos, cases: non-empty-list<case>)
}

fun exp/(==)(a: exp, b: exp): div bool {
  match (a, b) {
    (IntE(a_num), IntE(b_num)) -> a_num == b_num
    (BlockE(a_exps), BlockE(b_exps)) -> a_exps == b_exps
    (FnE(a_params, a_body), FnE(b_params, b_body)) -> a_params == b_params && a_body == b_body
    (IdE(a_name), IdE(b_name)) -> a_name == b_name
    (AppE(a_operator, a_operands), AppE(b_operator, b_operands)) ->
      a_operator == b_operator
      && list/(==)(a_operands, b_operands,
        ?(==) = fn(a_operand, b_operand) pretend-no-div(fn() a_operand == b_operand))
    (ValE(a_name, a_right_hand_side), ValE(b_name, b_right_hand_side)) ->
      a_name == b_name
      && a_right_hand_side == b_right_hand_side
    (DefE(a_name, a_params, a_body), DefE(b_name, b_params, b_body)) ->
      a_name == b_name
      && a_params == b_params
      && a_body == b_body
    (TypeDefE(a_name, a_options), TypeDefE(b_name, b_options)) ->
      a_name == b_name
      && a_options == b_options
    (MatchE(a_discriminee, a_cases), MatchE(b_discriminee, b_cases)) ->
      a_discriminee == b_discriminee
      && non-empty-list/(==)(a_cases, b_cases, ?(==) = fn(a_case, b_case) pretend-no-div(fn() a_case == b_case))
    _ -> False
  }
}

fun exp/show(exp: exp): div string {
  match exp {
    IntE(n) -> "IntE(" ++ n.show ++ ")"
    BlockE(exps) -> "BlockE(" ++ exps.non-empty-list/show(?show = fn(sub_exp) pretend-no-div(fn() sub_exp.show)) ++ ")"
    FnE(params, body) -> "FnE(" ++ params.show ++ ", " ++ body.show ++ ")"
    IdE(name) -> "IdE(" ++ name ++ ")"
    AppE(operator, operands) -> "AppE(" ++ operator.show ++ ", " ++ operands.show ++ ")"
    ValE(name, right_hand_side) -> "ValE(" ++ name ++ ", " ++ right_hand_side.show ++ ")"
    DefE(name, params, body) -> "DefE(" ++ name ++ ", " ++ params.show ++ ", " ++ body.show ++ ")"
    TypeDefE(name, options) -> "TypeDefE(" ++ name ++ ", " ++ options.show ++ ")"
    MatchE(discriminee, cases) -> "MatchE(" ++ discriminee.show ++ ", " ++ show(cases, ?show = fn(case) pretend-no-div(fn() case.show)) ++ ")"
  }
}

struct exp_with_pos {
  exp: exp
  start: pos
  end: pos
}

fun exp_with_pos/(==)(a: exp_with_pos, b: exp_with_pos): div bool {
  a.exp == b.exp
  && a.start == b.start
  && a.end == b.end
}

fun exp_with_pos/show(a: exp_with_pos): div string {
  a.exp.show ++ " @ " ++ a.start.show ++ "-" ++ a.end.show
}

value struct constructor_def {
  name: string
  params: list<string>
}

fun constructor_def/(==)(a: constructor_def, b: constructor_def): bool {
  a.name == b.name && a.params == b.params
}

fun constructor_def/show(a: constructor_def): string {
  "Constructor_Def(" ++ a.name ++ ", " ++ a.params.show ++ ")"
}

struct case {
  constructor_name: string
  params: list<string>
  body: exp_with_pos
}

fun case/(==)(a: case, b: case): div bool {
  a.constructor_name == b.constructor_name
  && a.params == b.params
  && a.body == b.body
}

fun case/show(a: case): div string {
  "Case(" ++ a.constructor_name ++ ", " ++ a.params.show ++ ", " ++ a.body.show ++ ")"
}

fun parse_error_to_maybe(parse_error: parse-error<o>): maybe<o> {
  match parse_error {
    ParseOk(res) -> Just(res)
    ParseError(_) -> Nothing
  }
}

fun p_eq(tok: token): ast<token_with_pos> token_with_pos {
  ptoken(tok.show, fn(tok_to_parse) 
    if (tok == tok_to_parse.token)
    then Just(tok_to_parse) 
    else Nothing
  )
}

fun p_keyword(str: string): ast<token_with_pos> token_with_pos {
  ptoken("keyword " ++ str, fn(tok) {
    match tok {
      TokenWithPos(WordToken(tok_str), _, _) ->
        if tok_str == str
        then Just(tok)
        else Nothing
      _ -> Nothing
    }
  })
}

fun p_word(): ast<token_with_pos> (string, pos, pos) {
  ptoken("word", fn(tok) {
    match tok {
      TokenWithPos(WordToken(str), start, end) -> Just((str, start, end))
      _ -> Nothing
    }
  })
}

fun p_open_brace(): ast<token_with_pos> token_with_pos -> p_eq(OpenBraceToken)
fun p_close_brace(): ast<token_with_pos> token_with_pos -> p_eq(CloseBraceToken)
fun p_line_separator(): ast<token_with_pos> token_with_pos -> p_eq(LineSeparatorToken)
fun p_open_paren(): ast<token_with_pos> token_with_pos -> p_eq(OpenParenToken)
fun p_close_paren(): ast<token_with_pos> token_with_pos -> p_eq(CloseParenToken)
fun p_fn_keyword(): ast<token_with_pos> token_with_pos -> p_keyword("fn")
fun p_assignment_operator(): ast<token_with_pos> token_with_pos -> p_eq(AssignmentOperatorToken)
fun p_val_keyword(): ast<token_with_pos> token_with_pos -> p_keyword("val")
fun p_def_keyword(): ast<token_with_pos> token_with_pos -> p_keyword("def")
fun p_list_separator(): ast<token_with_pos> token_with_pos -> p_eq(ListSeparatorToken)
fun p_typedef_keyword(): ast<token_with_pos> token_with_pos -> p_keyword("type")
fun p_option_separator(): ast<token_with_pos> token_with_pos -> p_eq(OptionSeparatorToken)
fun p_match_keyword(): ast<token_with_pos> token_with_pos -> p_keyword("match")

fun p_param_list(): ast<token_with_pos> list<string> {
  p-sep-by("parameter list", fn() p_word().fst, p_list_separator)
}

fun p_int(): <ast<token_with_pos>> exp_with_pos ->
  ptoken("int", fn(tok) {
    match tok {
      TokenWithPos(IntToken(num), start, end) ->
        Just(Exp_With_Pos(IntE(num), start, end))
      _ -> Nothing
    }
  })

fun p_block(): <ast<token_with_pos>> exp_with_pos {
  val start = p_open_brace().start
  val lines_with_poses = assert-non-empty(
    p-sep-by1("block sub-expression", p_exp, p_line_separator)
  )
  val end = p_close_brace().end
  Exp_With_Pos(BlockE(lines_with_poses), start, end)
}

fun p_fn(): <ast<token_with_pos>> exp_with_pos {
  val start = p_fn_keyword().start
  p_open_paren()
  val params = p_param_list()
  p_close_paren()
  val body = p_exp()
  Exp_With_Pos(FnE(params, body), start, body.end)
}

fun p_parenthesized(): <ast<token_with_pos>> exp_with_pos {
  val start = p_open_paren().start
  val inner = p_exp().exp
  val end = p_close_paren().end
  Exp_With_Pos(inner, start, end)
}

fun p_id(): <ast<token_with_pos>> exp_with_pos {
  val (str, start, end) = p_word()
  Exp_With_Pos(IdE(str), start, end)
}

fun p_val(): <ast<token_with_pos>> exp_with_pos {
  val start = p_val_keyword().start
  val (name, _, _) = p_word()
  p_assignment_operator()
  val right_hand_side = p_exp()
  Exp_With_Pos(ValE(name, right_hand_side), start, right_hand_side.end)
}

fun p_def(): <ast<token_with_pos>> exp_with_pos {
  val start = p_def_keyword().start
  val (name, _, _) = p_word()
  p_open_paren()
  val params = p_param_list()
  p_close_paren()
  p_assignment_operator()
  val body = p_exp()
  Exp_With_Pos(
    DefE(name, params, body),
    start,
    body.end
  )
}

fun p_constructor_def(): <ast<token_with_pos>> (constructor_def, pos) {
  val (name, _, _) = p_word()
  p_open_paren()
  val params = p_param_list()
  val end = p_close_paren().end
  (Constructor_Def(name, params), end)
}

fun p_typedef(): <ast<token_with_pos>> exp_with_pos {
  val start = p_typedef_keyword().start
  val (name, _, _) = p_word()
  val constructors_with_ends = assert-non-empty(
    p-sep-by1("options list", p_constructor_def, p_option_separator)
  )
  val constructors = constructors_with_ends.map(fst)
  val end = constructors_with_ends.last.snd
  Exp_With_Pos(TypeDefE(name, constructors), start, end)
}

fun p_case(): <ast<token_with_pos>> case {
  val constructor_name = p_word().fst
  p_open_paren()
  val params = p-sep-by("case params", fn() p_word().fst, p_list_separator)
  p_close_paren()
  val body = p_exp()
  Case(constructor_name, params, body)
}

fun p_match(): <ast<token_with_pos>> exp_with_pos {
  val start = p_match_keyword().start
  val discriminee = p_exp()
  p_open_brace()
  val cases = assert-non-empty(p-sep-by1("cases", p_case, p_option_separator))
  val end = p_close_brace().end
  Exp_With_Pos(MatchE(discriminee, cases), start, end)
}

fun p_operator(): <ast<token_with_pos>> exp_with_pos {
  // by doing a peek first, we can get better error messages
  val first_token_with_pos = match ppeek() {
    Just(tok) -> tok
    Nothing -> astError("Expected expression")
  }
  val first_token = first_token_with_pos.token
  match first_token {
    OpenBraceToken -> p_block()
    WordToken("fn") -> p_fn()
    WordToken("val") -> p_val()
    WordToken("def") -> p_def()
    WordToken("type") -> p_typedef()
    WordToken("match") -> p_match()
    _ -> pchoices("Atom", [
      p_int,
      p_parenthesized,
      p_id
    ])
  }
}

fun p_arg_list(): <ast<token_with_pos>> list<exp_with_pos> {
  p-sep-by("argument list", p_exp, p_list_separator)
}

fun p_app_or_operator(operator: exp_with_pos): <ast<token_with_pos>> exp_with_pos {
  val maybe_application = pmaybe("applier", fn() {
    p_open_paren()
    val operands = p_arg_list()
    val end = p_close_paren().end
    p_app_or_operator(Exp_With_Pos(AppE(operator, operands), operator.start, end))
  })

  match maybe_application {
    Just(application) -> application
    Nothing -> operator
  }
}

fun p_exp(): <ast<token_with_pos>> exp_with_pos {
  val operator = p_operator()

  p_app_or_operator(operator)
}

fun p_program(): <ast<token_with_pos>> exp_with_pos {
  val program = p_exp()
  peof()
  program
}

fun parse_exp(tokens: list<token_with_pos>): <pure> exp_with_pos
  with final ctl astError(msg)
    throw(msg)
  parseLexemes(tokens, p_program)