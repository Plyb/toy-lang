module interpreter

import std/core/undiv
import tokenizer
import parser
import std/data/hashmap
import non-empty-list
import std/data/hash
import std/text/parse
import typecheck
import test-helper


type toy-value {
  IntV(n: int)
  CloV(params: list<string>, body: exp_with_pos, env: env)
  ConstructorV(option_name: string, params: list<string>)
  AlgebraicV(option_name: string, args: list<toy-value>)
}

fun toy-value/(==)(a: toy-value, b: toy-value): div bool {
  match (a, b) {
    (IntV(a_n), IntV(b_n)) -> a_n == b_n
    (CloV(a_params, a_body, _), CloV(b_params, b_body, _)) ->
      a_params == b_params
      && a_body == b_body
    (ConstructorV(a_option_name, a_params), ConstructorV(b_option_name, b_params)) ->
      a_option_name == b_option_name
      && a_params == b_params
    (AlgebraicV(a_option_name, a_args), AlgebraicV(b_option_name, b_args)) ->
      a_option_name == b_option_name
      && list/(==)(a_args, b_args, ?(==) = fn(a_arg, b_arg) pretend-no-div(fn() a_arg == b_arg))
    _ -> False
  }
}

fun toy-value/show(value: toy-value): div string {
  match value {
    IntV(n) -> "IntV(" ++ n.show ++ ")"
    CloV(params, body, _) -> "CloV(" ++ params.show ++ ", " ++ body.show ++ ")"
    ConstructorV(option_name, params) -> "ConstructorV(" ++ option_name ++ ", " ++ params.show ++ ")"
    AlgebraicV(option_name, args) -> "AlgebraicV(" ++ option_name ++ ", " ++ args.show ++ ")"
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
  val updated_env = exps_with_poses.foldl(env, fn(acc_env, block_exp) {
    match block_exp.exp {
      ValE(Declaration(name, _), _) -> acc_env.insert(name, fresh_addr())
      DefE(name, _, _) -> acc_env.insert(name, fresh_addr())
      TypeDefE(_, options) -> acc_env.insert_all(options.map(fn(option) (option.name, fresh_addr())).to_list)
      _ -> acc_env
    }
  })

  // hoist def functions and constructors
  exps_with_poses.foreach(fn(block_exp) {
    match block_exp.exp {
      DefE(name, params, _, body) -> set(updated_env.get_or_throw(name), CloV(params.map(declaration/name), body, updated_env))
      TypeDefE(_, options) -> options.to_list.foreach(fn(option)
        set(updated_env.get_or_throw(option.name), ConstructorV(option.name, option.params.map(name)))
      )
      _ -> ()
    }
  })

  // interp other lines
  exps_with_poses.foreach(fn(block_exp) {
    match block_exp.exp {
      ValE(Declaration(name, _), rhs) -> set(updated_env.get_or_throw(name), rhs.interp(updated_env))
      DefE(_, _, _) -> ()
      TypeDefE(_, _) -> ()
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

fun env/insert_all(env: env, entries: list<(string, addr)>): env {
  entries.foldl(env, fn(acc_env, (key, addr)) acc_env.insert(key, addr))
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
    FnE(params, body) -> CloV(params.map(name), body, env)
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
        ConstructorV(option_name, params) -> {
          if (params.length != operands.length) then {
            throw("Unexpected number of arguments. Expected " ++ params.length.show ++ ", but got " ++ operands.length.show)
          }
          AlgebraicV(option_name, operand_values)
        }
        _ -> throw("Cannot apply non-function")
      }
    }
    ValE(_, right_hand_side) -> right_hand_side.interp(env)
    DefE(_, params, _, body) -> CloV(params.map(declaration/name), body, env)
    TypeDefE(_, _) -> throw("Type definition does not evaluate")
    MatchE(discriminee, cases) -> {
      val discriminee_value = discriminee.interp(env)
      match discriminee_value {
        AlgebraicV(option_name, args) -> {
          val case = match cases.to_list.find(fn(case) case.constructor_name == option_name) {
            Just(case) -> case
            Nothing -> throw("No matching case for " ++ option_name ++ " at " ++ exp.show)
          }
          if (!(case.params.length == args.length)) then {
            throw("Unexpected number of case arguments. The case has " ++ case.params.length.show ++ ", but the discriminee has " ++ args.length.show ++ ". At " ++ exp.show)
          }
          val extended_env = env.insert_all(case.params.zip(args))
          case.body.interp(extended_env)
        }
      }
    }
  }
}

fun run(prog: string): <pure, console> toy-value {
  val exp = prog.tokenize.parse_exp
  exp.typecheck(thread/hash-map(), thread/hash-map())

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
  exp.interp(thread/hash-map())
}

pub fun test()
  check(IntV(42))
    "(fn(x: int) x)(42)".run
  check(IntV(42))
    "{ val x: int = 42; val y: int = x; y }".run
  check(IntV(42))
    "{ val x: int = (fn(x: int) x)(42); x }".run
  check(IntV(42))
    "{ def g(x: int): int = f(x); def f(x: int): int = x; g(42) }".run
  check(IntV(42))
    "(fn(x: int) fn() x)(42)()".run
  check(IntV(1))
    "(fn(x: int, y: int) x)(1, 2)".run
  check(IntV(42))
    r"{
      def true(x: int, y: int): int = x;
      def false(x: int, y: int): int = y;
      def if(cond: (int, int) -> int, then: () -> int, else: () -> int): int = cond(then(), else());

      val whatWeWant: int = 42;
      val dontReturnThis: int = 0;

      if(true,
        fn() whatWeWant,
        fn() dontReturnThis
      )
    }".run
  check(IntV(1))
    r"{
      type myType
        pair(fst: int, snd: int);
      match pair(1, 2) {
        pair(x, y) x
      }
    }".run
  check(IntV(1))
    r"{
      type pair
        pair(fst: int, snd: int);
      def getFirst(thePair: pair): int = {
        match thePair {
          pair(x, y) x
        }
      };
      getFirst(pair(1, 2))
    }".run
  