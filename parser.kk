import ast-simple
import std/text/parse
import tokenizer
import std/core/undiv
import non-empty-list

type exp {
  IntE(n: int)
  BlockE(exps: non-empty-list<exp_with_pos>)
  FnE(params: list<declaration>, body: exp_with_pos)
  IdE(name: string)
  AppE(operator: exp_with_pos, operands: list<exp_with_pos>)
  ValE(left_hand_side: declaration, right_hand_side: exp_with_pos)
  DefE(def: recursive_def)
}

struct recursive_def {
  name: string
  params: list<declaration>
  return_type: toy-type
  body: exp_with_pos
}

fun exp/(==)(a: exp, b: exp): div bool {
  match (a, b) {
    (IntE(a_num), IntE(b_num)) -> a_num == b_num
    (BlockE(a_exps), BlockE(b_exps)) -> a_exps == b_exps
    (FnE(a_params, a_body), FnE(b_params, b_body)) ->
      list/(==)(a_params, b_params,
        ?(==) = fn(a_param, b_param) pretend-no-div(fn() a_param == b_param))
      && a_body == b_body
    (IdE(a_name), IdE(b_name)) -> a_name == b_name
    (AppE(a_operator, a_operands), AppE(b_operator, b_operands)) ->
      a_operator == b_operator
      && list/(==)(a_operands, b_operands,
        ?(==) = fn(a_operand, b_operand) pretend-no-div(fn() a_operand == b_operand))
    (ValE(a_lhs, a_rhs), ValE(b_lhs, b_rhs)) ->
      a_lhs == b_lhs
      && a_rhs == b_rhs
    (DefE(Recursive_def(a_name, a_params, a_return_type, a_body)),
        DefE(Recursive_def(b_name, b_params, b_return_type, b_body))) ->
      a_name == b_name
      && list/(==)(a_params, b_params,
        ?(==) = fn(a_param, b_param) pretend-no-div(fn() a_param == b_param))
      && a_return_type == b_return_type
      && a_body == b_body
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
    ValE(lhs, rhs) -> "ValE(" ++ lhs.show ++ ", " ++ rhs.show ++ ")"
    DefE(Recursive_def(name, params, return_type, body)) -> "DefE(" ++ name ++ ", " ++ params.show ++ ", " ++ return_type.show ++ "," ++ body.show ++ ")"  
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

type toy-type {
  IntT
  ArrowT(params: list<toy-type>, return_type: toy-type)
}

fun toy-type/(==)(a: toy-type, b: toy-type): div bool {
  match (a, b) {
    (IntT, IntT) -> True
    (ArrowT(a_params, a_return_type), ArrowT(b_params, b_return_type)) ->
      list/(==)(a_params, b_params,
        ?(==) = fn(a_param, b_param) pretend-no-div(fn() a_param == b_param))
      && a_return_type == b_return_type
    (_, _) -> False
  }
}

fun toy-type/show(a: toy-type): div string {
  match a {
    IntT -> "IntT()"
    ArrowT(params, return_type) -> "ArrowT(" ++ params.show ++ ", " ++ return_type.show ++ ")"
  }
}

value struct declaration {
  name: string
  type_tag: toy-type
}

fun declaration/(==)(a: declaration, b: declaration): div bool {
  a.name == b.name && a.type_tag == b.type_tag
}

fun declaration/show(a: declaration): div string {
  "Declaration(" ++ a.name ++ ", " ++ a.type_tag.show ++ ")"
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
fun p_period(): ast<token_with_pos> token_with_pos -> p_eq(PeriodToken)
fun p_open_paren(): ast<token_with_pos> token_with_pos -> p_eq(OpenParenToken)
fun p_close_paren(): ast<token_with_pos> token_with_pos -> p_eq(CloseParenToken)
fun p_colon(): ast<token_with_pos> token_with_pos -> p_eq(ColonToken)
fun p_fn_keyword(): ast<token_with_pos> token_with_pos -> p_keyword("fn")
fun p_eq_token(): ast<token_with_pos> token_with_pos -> p_eq(EqToken)
fun p_val_keyword(): ast<token_with_pos> token_with_pos -> p_keyword("val")
fun p_def_keyword(): ast<token_with_pos> token_with_pos -> p_keyword("def")
fun p_list_separator(): ast<token_with_pos> token_with_pos -> p_eq(ListSeparatorToken)
fun p_arrow(): ast<token_with_pos> token_with_pos -> p_eq(ArrowToken)

fun p_int_type(): ast<token_with_pos> toy-type -> {
  p_keyword("int")
  IntT
}
fun p_arrow_type(): ast<token_with_pos> toy-type -> {
  p_open_paren()
  val params = p-sep-by("parameter type list", p_type, p_list_separator)
  p_close_paren()
  p_arrow()
  val return_type = p_type()
  ArrowT(params, return_type)
}

fun p_type(): ast<token_with_pos> toy-type {// by doing a peek first, we can get better error messages
  val first_token_with_pos = match ppeek() {
    Just(tok) -> tok
    Nothing -> astError("Expected type")
  }
  val first_token = first_token_with_pos.token
  match first_token {
    OpenParenToken -> p_arrow_type()
    _ -> p_int_type()
  }
}

fun p_delcaration(): ast<token_with_pos> declaration {
  val (name, _, _) = p_word()
  p_colon()
  val type_tag = p_type()
  Declaration(name, type_tag)
}

fun p_param_list(): ast<token_with_pos> list<declaration> {
  p-sep-by("parameter list", p_delcaration, p_list_separator)
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
    p-sep-by1("block sub-expression", p_exp, p_period)
  )
  val end = p_close_brace().end
  Exp_With_Pos(BlockE(lines_with_poses), start, end)
}

fun p_fn(): <ast<token_with_pos>> exp_with_pos {
  val start = p_fn_keyword().start
  p_open_paren()
  val params = p_param_list()
  p_close_paren()
  p_colon()
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
  val lhs = p_delcaration()
  p_eq_token()
  val rhs = p_exp()
  Exp_With_Pos(ValE(lhs, rhs), start, rhs.end)
}

fun p_def(): <ast<token_with_pos>> exp_with_pos {
  val start = p_def_keyword().start
  val (name, _, _) = p_word()
  p_open_paren()
  val params = p_param_list()
  p_close_paren()
  p_colon()
  val return_type = p_type()
  val body = p_exp()
  Exp_With_Pos(
    DefE(Recursive_def(name, params, return_type, body)),
    start,
    body.end
  )
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