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
  val (name, _, _) = p_word()
  p_eq_token()
  val right_hand_side = p_exp()
  Exp_With_Pos(ValE(name, right_hand_side), start, right_hand_side.end)
}

fun p_def(): <ast<token_with_pos>> exp_with_pos {
  val start = p_def_keyword().start
  val (name, _, _) = p_word()
  p_open_paren()
  val params = p_param_list()
  p_close_paren()
  p_colon()
  val body = p_exp()
  Exp_With_Pos(
    DefE(name, params, body),
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