import std/text/parse
import std/core/undiv

fun token_parser(p)
  many(whitespace)
  p()

fun non_whitespace(): <parse> char {
  char-is("non-whitespace", fn(c) !c.is-white)
}

value type token {
  WordToken(str: string)
  IntToken(num: int)
  OpenBraceToken
  CloseBraceToken
  PeriodToken
  OpenParenToken
  CloseParenToken
  ColonToken
  EqToken
  ListSeparatorToken
}

fun token/(==)(a: token, b: token): bool {
  match (a, b) {
    (WordToken(a_str), WordToken(b_str)) -> a_str == b_str
    (IntToken(a_num), IntToken(b_num)) -> a_num == b_num
    (OpenBraceToken, OpenBraceToken) -> True
    (CloseBraceToken, CloseBraceToken) -> True
    (PeriodToken, PeriodToken) -> True
    (OpenParenToken, OpenParenToken) -> True
    (CloseParenToken, CloseParenToken) -> True
    (ColonToken, ColonToken) -> True
    (EqToken, EqToken) -> True
    (ListSeparatorToken, ListSeparatorToken) -> True
    _ -> False
  }
}

fun token/show(tok: token): string {
  match tok {
    WordToken(str) -> "WordToken(" ++ str ++ ")"
    IntToken(num) -> "IntToken(" ++ num.show ++ ")"
    OpenBraceToken -> "OpenBraceToken"
    CloseBraceToken -> "CloseBraceToken"
    PeriodToken -> "PeriodToken"
    OpenParenToken -> "OpenParenToken"
    CloseParenToken -> "CloseParenToken"
    ColonToken -> "ColonToken"
    EqToken -> "EqToken"
    ListSeparatorToken -> "ListSeparatorToken"
  }
}

type token_with_pos {
  TokenWithPos(token: token, start: pos, end: pos)
}

fun token_with_pos/show(token_with_pos: token_with_pos): string {
  val start = token_with_pos.start
  val end = token_with_pos.end
  val token = token_with_pos.token
  token.show ++ " @ " ++ start.show ++ "-" ++ end.show
}

fun p_word_token(): <parse> token {
  val str = many1(alpha).string
  WordToken(str)
}

fun p_int_token(): <parse> token {
  val num = pint()
  IntToken(num)
}

fun p_open_brace_token(): <parse> token {
  char('{')
  OpenBraceToken
}

fun p_close_brace_token(): <parse> token {
  char('}')
  CloseBraceToken
}

fun ensure_next_char_not_digit(): <parse> () {
  match next(current-input()) {
    Just((next_char, _)) ->
      if (is-digit(next_char)) then {
        fail("digit following period")
      }
    _ -> ()
  }
}

fun p_period_token(): <parse> token {
  char('.')
  ensure_next_char_not_digit()
  PeriodToken
}

fun p_open_paren_token(): <parse> token {
  char('(')
  OpenParenToken
}

fun p_close_paren_token(): <parse> token {
  char(')')
  CloseParenToken
}

fun p_def_symbol_token(): <parse> token {
  char('=')
  EqToken
}

fun p_colon_token(): <parse> token {
  char(':')
  ColonToken
}

fun p_list_separator_token(): <parse> token {
  char(',')
  ListSeparatorToken
}

fun p_token(): <parse, get_pos> token_with_pos {
  val start = get_pos()
  val res = TokenWithPos(
    choose([
      p_word_token,
      p_int_token,
      p_open_brace_token,
      p_close_brace_token,
      p_period_token,
      p_open_paren_token,
      p_close_paren_token,
      p_def_symbol_token,
      p_colon_token,
      p_list_separator_token
    ]), start, get_pos())
  many(whitespace)
  res
}

fun p_tokens(): <parse, get_pos> list<token_with_pos> {
  many(whitespace)
  many(p_token)
}

fun run_parser(s: string, p: parser<pure,a>): <pure> a {
  match parse(s.slice, {val e = p(); eof(); e}) {
    ParseOk(e) -> e
    ParseError(e) -> throw("Failed to tokenize: " ++ e)
  }
}

value type pos {
  Pos(line_number: int, column: int)
}

fun pos/show(pos: pos): string {
  "(" ++ pos.line_number.show ++ "," ++ pos.column.show ++ ")"
}

fun pos/(==)(a: pos, b: pos) {
  a.line_number == b.line_number && a.column == b.column
}

effect get_pos {
  fun get_pos(): pos
}

fun count_lines(s: string): int {
  s.list.filter(fn(c) c == '\n').length
}

fun tokenize(s: string): <pure,console> list<token_with_pos> {
  var line_number := 0
  var column := 0
  val parser = fn(p: parser<<get_pos>,a>): _ a {
    with override<parse> {
      fun current-input() current-input()

      brk fail(msg) fail("Unknown token at "
        ++ Pos(line_number, column).show ++ ": "
        ++ (match parse(current-input(), fn() many(non_whitespace)) {
          ParseOk(res) -> res.string
          ParseError(_) -> "should never get here" // because many always succeeds
        }))

      fun satisfy(pred) {
        val before = current-input()
        val result = satisfy(pred)
        val after = current-input()
        val length_difference = before.count - after.count
        if (length_difference > 0) then {
          before.take(length_difference).foreach(fn(c) {
            match c {
              '\n' -> {
                line_number := line_number + 1
                column := 0
              }
              '\r' -> ()
              _ -> column := column + 1
            }
          })
        }
        result
      }

      ctl pick() {
        val line_number_save = line_number
        val column_save = column
        if pick()
        then resume(True)
        else {
          line_number := line_number_save
          column := column_save
          resume(False)
        }
      }
    }
    with handler<get_pos> {
      fun get_pos() Pos(line_number, column)
    }
    p()
  }

  match parse(s.slice, fn() parser(p_tokens)) {
    ParseOk(res, rest) -> {
      // Do an extra parse with non-det eof to get a better error message
      // in the case the tokenization fails
      match parse(rest, fn() { (fn() { parser(p_token); () }) || eof}) {
        ParseOk(_) -> res
        ParseError(e) -> throw("Failed to tokenize: " ++ e)
      }}
    ParseError(_) -> throw("should never get here 2") // because many always succeeds
  }
}