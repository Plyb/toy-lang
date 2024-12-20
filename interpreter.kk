import std/core/undiv
import tokenizer
import parser
import std/data/hashmap
import non-empty-list
import std/data/hash
import std/text/parse

fun check(expected: a, f: () -> <console,pure|e> a, ?(==): (a, a) -> div bool, ?kk-file-line: string, ?show: a -> div string): <console,div|e> ()
  println("Checking (" ++ kk-file-line ++ ") ...")
  match try(f)
    Error(e) -> println("Failed! " ++ e.message)
    Ok(actual) -> if actual == expected then println("Passed!") else println("Failed!\n\tExpected: " ++ expected.show ++ "\n\tActual: " ++ actual.show) 

fun check-exn(expected-err: string, f: () -> <console,exn|e> a, ?kk-file-line: string): <console|e> ()
  println("Checking exception (" ++ kk-file-line ++ ") ...")
  match try(f)
    Error(e) -> if expected-err == e.message then println("Passed!") else println("Failed!")
    _ -> println("Failed!")

///////////////////// interpreter //////////////////////

type toy-value {
  IntV(n: int)
  CloV(param: string, body: exp_with_pos, env: env)
  RecV(param: string, body: exp_with_pos, env: env, recs: list<recursive_def>)
}

fun toy-value/(==)(a: toy-value, b: toy-value): div bool {
  match (a, b) {
    (IntV(a_n), IntV(b_n)) -> a_n == b_n
    (CloV(a_param, a_body, _), CloV(b_param, b_body, _)) ->
      a_param == b_param
      && a_body == b_body
    (RecV(a_param, a_body, _, _), RecV(b_param, b_body, _, _)) ->
      a_param == b_param
      && a_body == b_body
    _ -> False
  }
}

fun toy-value/show(value: toy-value): div string {
  match value {
    IntV(n) -> "IntV(" ++ n.show ++ ")"
    CloV(param, body, _) -> "CloV(" ++ param ++ ", " ++ body.show ++ ")"
    RecV(param, body, _, _) -> "RecV(" ++ param ++ ", " ++ body.show ++ ")"
  }
}

alias env = hash-map<string, toy-value>;

fun add_block_statements(env: env, exps_with_poses: list<exp_with_pos>) {
  val rec_defs = exps_with_poses.flatmap-maybe(fn(exp_with_pos) {
    match exp_with_pos.exp {
      DefE(rec_def) -> Just(rec_def)
      _ -> Nothing
    }
  })

  exps_with_poses.foldl(env, fn(acc_env, block_exp) {
    match block_exp.exp {
      ValE(name, right_hand_side) -> {
        val rhs_value = right_hand_side.interp(acc_env)
        acc_env.insert(name, rhs_value)
      }
      DefE(Recursive_def(name, param, body)) ->
        acc_env.insert(name, RecV(param, body, acc_env, rec_defs))
      _ -> {
        block_exp.interp(acc_env) // run for possible effect
        acc_env
      }
    }
  })
}

fun inflate(rec_def: recursive_def, env: env, recs: list<recursive_def>) {
  RecV(rec_def.param, rec_def.body, env, recs)
}

fun insert_all_if_absent(env: env, entries: list<(string, toy-value)>) {
  entries.foldl(env, fn(acc_env, (key, value)) {
    match acc_env.get(key) {
      Just(_) -> acc_env
      Nothing -> acc_env.insert(key, value)
    }
  })
}

fun interp(exp_with_pos: exp_with_pos, env: env): pure toy-value {
  val exp = exp_with_pos.exp
  val start = exp_with_pos.start
  val end = exp_with_pos.end
  match exp {
    IntE(n) -> IntV(n)
    BlockE(exps) -> {
      val extended_env = env.add_block_statements(exps.all_but_last)
      exps.last.interp(extended_env)
    }
    FnE(param, body) -> CloV(param, body, env)
    IdE(name) -> match env.get(name) {
      Just(value) -> value
      Nothing -> throw("Unbound identifier: " ++ name)
    }
    AppE(operator, operand) -> {
      val operator_value = operator.interp(env);
      val operand_value = operand.interp(env);
      match operator_value {
        CloV(param, body, clo_env) -> {
          val extended_env = clo_env.insert(param, operand_value);
          body.interp(extended_env)
        }
        RecV(param, body, clo_env, recs) -> {
          val inflated_recs = recs.map(fn(rec_def) {
            (rec_def.name, rec_def.inflate(clo_env, recs))
          })
          val env_with_inflated = clo_env.insert_all_if_absent(inflated_recs)
          val extended_env = env_with_inflated.insert(param, operand_value)
          body.interp(extended_env)
        }
        _ -> throw("Cannot apply non-function")
      }
    }
    ValE(_, right_hand_side) -> right_hand_side.interp(env)
    DefE(_) -> throw("Recursive definition does not evaluate") // mostly because I'm lazy and don't want to figure out how to get the other recursive defs here
  }
}

fun run(prog: string): <pure,console> toy-value {
  prog.tokenize.parse_exp.interp(thread/hash-map())
}

fun main()
  // check([WordToken("blah"), PeriodToken, OpenBraceToken, IntToken(12), CloseBraceToken, OpenParenToken, CloseParenToken, ColonToken])
  //   tokenize("blah.\n; {12} ():")
  check(IntE(1))
    parse_exp(tokenize("1")).exp
  check(BlockE(NELast(Exp_With_Pos(IntE(1), Pos(0,1), Pos(0,2)))))
    parse_exp(tokenize("{1}")).exp
  check(BlockE(
    NECons(Exp_With_Pos(BlockE(
      NECons(Exp_With_Pos(IntE(1), Pos(0,2), Pos(0,3)),
      NELast(Exp_With_Pos(IntE(2), Pos(0,5), Pos(0,6))))), Pos(0,1), Pos(0,7)),
    NECons(Exp_With_Pos(IntE(3), Pos(0,9), Pos(0,10)),
    NELast(Exp_With_Pos(IntE(4), Pos(0,12), Pos(0,13))
  )))))
    parse_exp(tokenize("{{1. 2}. 3. 4}")).exp
  // check([WordToken("fn"), OpenParenToken, WordToken("x"), CloseParenToken, ColonToken, IntToken(1)])
  //   tokenize("fn(x): 1")
  check(FnE("x", Exp_With_Pos(IntE(1), Pos(0,7), Pos(0,8))))
    parse_exp(tokenize("fn(x): 1")).exp
  check(FnE("x", Exp_With_Pos(BlockE(
      NECons(Exp_With_Pos(IntE(1), Pos(0,9), Pos(0,10)),
      NELast(Exp_With_Pos(IntE(2), Pos(0,12), Pos(0,13))))), Pos(0,7), Pos(0,15))))
    parse_exp(tokenize("fn(x): { 1. 2 }")).exp
  check(FnE("x", Exp_With_Pos(IdE("x"), Pos(0,7), Pos(0,8))))
    parse_exp(tokenize("fn(x): x")).exp
  check(AppE(
      Exp_With_Pos(IntE(1), Pos(0,0), Pos(0,1)),
      Exp_With_Pos(IntE(2), Pos(0,2), Pos(0,3))))
    parse_exp(tokenize("1(2)")).exp
  check(AppE(
    Exp_With_Pos(FnE("x",
      Exp_With_Pos(IdE("x"), Pos(0,8), Pos(0,9))), Pos(0,0), Pos(0,10)),
    Exp_With_Pos(IntE(1), Pos(0,11), Pos(0,12))))
    parse_exp(tokenize("(fn(x): x)(1)")).exp
  check(IntV(42))
    "(fn(x): x)(42)".run
  check(IntV(42))
    "{ val x = 42. val y = x. y }".run
  check(IntV(42))
    "{ val x = (fn(x): x)(42). x }".run
  check(DefE(Recursive_def("recur", "x",
      Exp_With_Pos(AppE(
        Exp_With_Pos(IdE("recur"), Pos(0,14), Pos(0,19)),
        Exp_With_Pos(IdE("x"), Pos(0,20), Pos(0,21))), Pos(0,14), Pos(0,22)))))
    "def recur(x): recur(x)".tokenize.parse_exp.exp
  check(IntV(42))
    "{ def g(x): f(x). def f(x): x. g(42) }".run
  check(IntV(42))
    "(fn(x): fn(y): x)(42)(0)".run
  