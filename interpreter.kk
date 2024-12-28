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
}

fun toy-value/(==)(a: toy-value, b: toy-value): div bool {
  match (a, b) {
    (IntV(a_n), IntV(b_n)) -> a_n == b_n
    (CloV(a_params, a_body, _), CloV(b_params, b_body, _)) ->
      a_params == b_params
      && a_body == b_body
    _ -> False
  }
}

fun toy-value/show(value: toy-value): div string {
  match value {
    IntV(n) -> "IntV(" ++ n.show ++ ")"
    CloV(params, body, _) -> "CloV(" ++ params.show ++ ", " ++ body.show ++ ")"
  }
}

fun maybe/get_or_throw(maybe: maybe<a>): exn a {
  match maybe {
    Just(value) -> value
    Nothing -> throw("Expected Just, but got Nothing")
  }
}

fun hash-map/get_or_throw(map: hash-map<k, v>, key: k, ?hash: (k, int64) -> int, ?(==): (k, k) -> bool): exn v {
  map.get(key).get_or_throw()
}

alias addr = int
alias env = hash-map<string, addr>
alias store = hash-map<addr, toy-value>

effect store_update {
  fun get(addr: addr): maybe<toy-value>
  fun set(addr: addr, value: toy-value): ()
  fun fresh_addr(): addr
}

fun add_block_statements(env: env, exps_with_poses: list<exp_with_pos>): <pure, store_update> env {
  val rec_defs = exps_with_poses.flatmap-maybe(fn(exp_with_pos) {
    match exp_with_pos.exp {
      DefE(rec_def) -> Just(rec_def)
      _ -> Nothing
    }
  })

  val updated_env = exps_with_poses.foldl(env, fn(acc_env, block_exp) {
    match block_exp.exp {
      ValE(name, _) -> acc_env.insert(name, fresh_addr())
      DefE(Recursive_def(name, _, _)) -> acc_env.insert(name, fresh_addr())
      _ -> acc_env
    }
  })

  // hoist def functions
  exps_with_poses.foreach(fn(block_exp) {
    match block_exp.exp {
      DefE(Recursive_def(name, params, body)) -> set(updated_env.get_or_throw(name), CloV(params, body, updated_env))
      _ -> ()
    }
  })

  // interp other lines
  exps_with_poses.foreach(fn(block_exp) {
    match block_exp.exp {
      ValE(name, rhs) -> set(updated_env.get_or_throw(name), rhs.interp(updated_env))
      _ -> {
        block_exp.interp(updated_env)
        ()
      }
    }
  })

  updated_env
}

fun insert_all(env: env, entries: list<(string, toy-value)>): <exn, store_update> env {
  val updated_env = entries.foldl(env, fn(acc_env, (key, _)) acc_env.insert(key, fresh_addr()))
  entries.foreach(fn((key, value)) set(updated_env.get_or_throw(key), value))
  updated_env
}

fun interp(exp_with_pos: exp_with_pos, env: env): <pure, store_update> toy-value {
  val exp = exp_with_pos.exp
  val start = exp_with_pos.start
  val end = exp_with_pos.end
  match exp {
    IntE(n) -> IntV(n)
    BlockE(exps) -> {
      val extended_env = env.add_block_statements(exps.all_but_last)
      exps.last.interp(extended_env)
    }
    FnE(params, body) -> CloV(params, body, env)
    IdE(name) -> match env.get(name) {
      Just(addr) -> {
        match get(addr) {
          Just(value) -> value
          Nothing -> throw("Uninitialized identifier: " ++ name)
        }
      }
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
        _ -> throw("Cannot apply non-function")
      }
    }
    ValE(_, right_hand_side) -> right_hand_side.interp(env)
    DefE(Recursive_def(_, params, body)) -> CloV(params, body, env)
  }
}

fun run(prog: string): <pure, console> toy-value {
  var store := thread/hash-map()
  var last_addr := 0

  with handler<store_update> {
    fun get(addr: addr) store.get(addr)
    fun set(addr: addr, value: toy-value) store := store.insert(addr, value)
    fun fresh_addr() {
      last_addr := last_addr + 1
      last_addr
    }
  }
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
  check(FnE(["x"], Exp_With_Pos(IntE(1), Pos(0,7), Pos(0,8))))
    parse_exp(tokenize("fn(x): 1")).exp
  check(FnE(["x"], Exp_With_Pos(BlockE(
      NECons(Exp_With_Pos(IntE(1), Pos(0,9), Pos(0,10)),
      NELast(Exp_With_Pos(IntE(2), Pos(0,12), Pos(0,13))))), Pos(0,7), Pos(0,15))))
    parse_exp(tokenize("fn(x): { 1. 2 }")).exp
  check(FnE(["x"], Exp_With_Pos(IdE("x"), Pos(0,7), Pos(0,8))))
    parse_exp(tokenize("fn(x): x")).exp
  check(AppE(
      Exp_With_Pos(IntE(1), Pos(0,0), Pos(0,1)),
      [Exp_With_Pos(IntE(2), Pos(0,2), Pos(0,3))]))
    parse_exp(tokenize("1(2)")).exp
  check(AppE(
    Exp_With_Pos(FnE(["x"],
      Exp_With_Pos(IdE("x"), Pos(0,8), Pos(0,9))), Pos(0,0), Pos(0,10)),
    [Exp_With_Pos(IntE(1), Pos(0,11), Pos(0,12))]))
    parse_exp(tokenize("(fn(x): x)(1)")).exp
  check(IntV(42))
    "(fn(x): x)(42)".run
  check(IntV(42))
    "{ val x = 42. val y = x. y }".run
  check(IntV(42))
    "{ val x = (fn(x): x)(42). x }".run
  check(DefE(Recursive_def("recur", ["x"],
      Exp_With_Pos(AppE(
        Exp_With_Pos(IdE("recur"), Pos(0,14), Pos(0,19)),
        [Exp_With_Pos(IdE("x"), Pos(0,20), Pos(0,21))]), Pos(0,14), Pos(0,22)))))
    "def recur(x): recur(x)".tokenize.parse_exp.exp
  check(IntV(42))
    "{ def g(x): f(x). def f(x): x. g(42) }".run
  check(IntV(42))
    "(fn(x): fn(): x)(42)()".run
  check(IntV(1))
    "(fn(x, y): x)(1, 2)".run
  check(IntV(42))
    r"{
      def true(x, y): x.
      def false(x, y): y.
      def if(cond, then, else): cond(then(), else()).

      val whatWeWant = 42.
      val dontReturnThis = 0.

      if(true,
        fn(): whatWeWant,
        fn(): dontReturnThis
      )
    }".run
  