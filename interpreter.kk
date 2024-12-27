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
  CloV(params: list<string>, body: exp_with_pos, env: env)
  RecV(params: list<string>, body: exp_with_pos, env: env, recs: list<recursive_def>)
}

fun toy-value/(==)(a: toy-value, b: toy-value): div bool {
  match (a, b) {
    (IntV(a_n), IntV(b_n)) -> a_n == b_n
    (CloV(a_params, a_body, _), CloV(b_params, b_body, _)) ->
      a_params == b_params
      && a_body == b_body
    (RecV(a_params, a_body, _, _), RecV(b_params, b_body, _, _)) ->
      a_params == b_params
      && a_body == b_body
    _ -> False
  }
}

fun toy-value/show(value: toy-value): div string {
  match value {
    IntV(n) -> "IntV(" ++ n.show ++ ")"
    CloV(params, body, _) -> "CloV(" ++ params.show ++ ", " ++ body.show ++ ")"
    RecV(params, body, _, _) -> "RecV(" ++ params.show ++ ", " ++ body.show ++ ")"
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
      ValE(Declaration(name, _), right_hand_side) -> {
        val rhs_value = right_hand_side.interp(acc_env)
        acc_env.insert(name, rhs_value)
      }
      DefE(Recursive_def(name, params, _, body)) ->
        acc_env.insert(name, RecV(params.map(declaration/name), body, acc_env, rec_defs))
      _ -> {
        block_exp.interp(acc_env) // run for possible effect
        acc_env
      }
    }
  })
}

fun inflate(rec_def: recursive_def, env: env, recs: list<recursive_def>) {
  RecV(rec_def.params.map(name), rec_def.body, env, recs)
}

fun insert_all_if_absent(env: env, entries: list<(string, toy-value)>) {
  entries.foldl(env, fn(acc_env, (key, value)) {
    match acc_env.get(key) {
      Just(_) -> acc_env
      Nothing -> acc_env.insert(key, value)
    }
  })
}

fun insert_all(env: env, entries: list<(string, toy-value)>) {
  entries.foldl(env, fn(acc_env, (key, value)) acc_env.insert(key, value))
}

fun interp_with_env(env: env) {
  fn(exp_with_pos: exp_with_pos) {
    exp_with_pos.interp(env)
  }
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
    FnE(params, body) -> CloV(params.map(name), body, env)
    IdE(name) -> match env.get(name) {
      Just(value) -> value
      Nothing -> throw("Unbound identifier: " ++ name)
    }
    AppE(operator, operands) -> {
      val operator_value = operator.interp(env);
      val operand_values = operands.map(fn(operand) operand.interp(env))
      match operator_value {
        CloV(params, body, clo_env) -> {
          if (params.length != operands.length) then {
            throw("Unexpected number of arguments. Expected " ++ params.length.show ++ ", but got " ++ operands.length.show)
          }
          val extended_env = clo_env.insert_all(params.zip(operand_values))
          body.interp(extended_env)
        }
        RecV(params, body, clo_env, recs) -> {
          if (params.length != operands.length) then {
            throw("Unexpected number of arguments. Expected " ++ params.length.show ++ ", but got " ++ operands.length.show)
          }
          
          val inflated_recs = recs.map(fn(rec_def) {
            (rec_def.name, rec_def.inflate(clo_env, recs))
          })
          val env_with_inflated = clo_env.insert_all_if_absent(inflated_recs)

          val extended_env = env_with_inflated.insert_all(params.zip(operand_values))

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
  check(FnE([Declaration("x", IntT)], Exp_With_Pos(IntE(1), Pos(0,12), Pos(0,13))))
    parse_exp(tokenize("fn(x: int): 1")).exp
  check(FnE([Declaration("x", IntT)], Exp_With_Pos(BlockE(
      NECons(Exp_With_Pos(IntE(1), Pos(0,14), Pos(0,15)),
      NELast(Exp_With_Pos(IntE(2), Pos(0,17), Pos(0,18))))), Pos(0,12), Pos(0,20))))
    parse_exp(tokenize("fn(x: int): { 1. 2 }")).exp
  check(FnE([Declaration("x", IntT)], Exp_With_Pos(IdE("x"), Pos(0,12), Pos(0,13))))
    parse_exp(tokenize("fn(x: int): x")).exp
  check(AppE(
      Exp_With_Pos(IntE(1), Pos(0,0), Pos(0,1)),
      [Exp_With_Pos(IntE(2), Pos(0,2), Pos(0,3))]))
    parse_exp(tokenize("1(2)")).exp
  check(AppE(
    Exp_With_Pos(FnE([Declaration("x", IntT)],
      Exp_With_Pos(IdE("x"), Pos(0,13), Pos(0,14))), Pos(0,0), Pos(0,15)),
    [Exp_With_Pos(IntE(1), Pos(0,16), Pos(0,17))]))
    parse_exp(tokenize("(fn(x: int): x)(1)")).exp
  check(IntV(42))
    "(fn(x: int): x)(42)".run
  check(IntV(42))
    "{ val x: int = 42. val y: int = x. y }".run
  check(IntV(42))
    "{ val x: int = (fn(x: int): x)(42). x }".run
  check(DefE(Recursive_def("recur", [Declaration("x", IntT)], IntT,
      Exp_With_Pos(AppE(
        Exp_With_Pos(IdE("recur"), Pos(0,23), Pos(0,28)),
        [Exp_With_Pos(IdE("x"), Pos(0,29), Pos(0,30))]), Pos(0,23), Pos(0,31)))))
    "def recur(x: int): int recur(x)".tokenize.parse_exp.exp
  check(IntV(42))
    "{ def g(x: int): int f(x). def f(x: int): int x. g(42) }".run
  check(IntV(42))
    "(fn(x: int): fn(): x)(42)()".run
  check(IntV(1))
    "(fn(x: int, y: int): x)(1, 2)".run
  check(IntV(42))
    r"{
      def true(x: int, y: int): int x.
      def false(x: int, y: int): int y.
      def if(cond: (int, int) -> int, then: int, else: int): int cond(then(), else()).

      val whatWeWant: int = 42.
      val dontReturnThis: int = 0.

      if(true,
        fn(): whatWeWant,
        fn(): dontReturnThis
      )
    }".run
  