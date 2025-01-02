module interpreter

import std/core/undiv
import tokenizer
import parser
import std/data/hashmap
import non-empty-list
import std/data/hash
import std/text/parse
import test-helper


type toy-value {
  IntV(n: int)
  CloV(params: list<string>, body: exp_with_pos, env: env)
  ConstructorV(option_name: string, params: list<string>)
  AlgebraicV(option_name: string, args: list<toy-value>)
  GetV
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
    (GetV, GetV) -> True
    _ -> False
  }
}

fun toy-value/show(value: toy-value): div string {
  match value {
    IntV(n) -> "IntV(" ++ n.show ++ ")"
    CloV(params, body, _) -> "CloV(" ++ params.show ++ ", " ++ body.show ++ ")"
    ConstructorV(option_name, params) -> "ConstructorV(" ++ option_name ++ ", " ++ params.show ++ ")"
    AlgebraicV(option_name, args) -> "AlgebraicV(" ++ option_name ++ ", " ++ args.show ++ ")"
    GetV -> "GetV"
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
      ValE(name, _) -> acc_env.insert(name, fresh_addr())
      DefE(name, _, _) -> acc_env.insert(name, fresh_addr())
      TypeDefE(_, options) -> acc_env.insert_all(options.map(fn(option) (option.name, fresh_addr())).to_list)
      _ -> acc_env
    }
  })

  // hoist def functions and constructors
  exps_with_poses.foreach(fn(block_exp) {
    match block_exp.exp {
      DefE(name, params, body) -> set(updated_env.get_or_throw(name), CloV(params, body, updated_env))
      TypeDefE(_, options) -> options.to_list.foreach(fn(option)
        set(updated_env.get_or_throw(option.name), ConstructorV(option.name, option.params))
      )
      _ -> ()
    }
  })

  // interp other lines
  exps_with_poses.foreach(fn(block_exp) {
    match block_exp.exp {
      ValE(name, rhs) -> set(updated_env.get_or_throw(name), rhs.interp(updated_env))
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

fun list/at(list: list<a>, i: int): maybe<a> {
  if (i == 0) then {
    list.head()
  } else {
    match list {
      Nil -> Nothing
      Cons(_, tail) -> tail.at(i - 1)
    }
  }
}

fun list/cross(a: list<a>, b: list<b>, joiner: (a, b) -> e c): e list<c> {
  match a {
    Nil -> []
    Cons(a_head, a_tail) -> {
      b.map(fn(b_elem) -> joiner(a_head, b_elem))
      ++ a_tail.cross(b, joiner)
    }
  }
}

fun toy_nat_to_int(toy_nat: toy-value) {
  match toy_nat {
    AlgebraicV("O", []) -> 0
    AlgebraicV("S", [n_value]) -> 1 + n_value.toy_nat_to_int
  }
}

fun to_toy_nat(n: int) {
  if (n == 0) then {
    AlgebraicV("O", [])
  } else {
    AlgebraicV("S", [(n - 1).to_toy_nat])
  }
}

fun toy_list_to_list(toy_list: toy-value) {
  match toy_list {
    AlgebraicV("nil", []) -> []
    AlgebraicV("cons", [head, tail]) -> Cons(head, tail.toy_list_to_list)
  }
}

fun to_toy_list(list: list<toy-value>) {
  match list {
    Nil -> AlgebraicV("nil", [])
    Cons(head, tail) -> AlgebraicV("cons", [head, tail.to_toy_list])
  }
}

fun predicate_value(predicate_value_value: toy-value, tuple: toy-value) {
  match predicate_value_value {
    AlgebraicV("column", [index_value]) -> {
      val column_index = index_value.toy_nat_to_int
      match tuple {
        AlgebraicV("tuple", args) -> args.at(column_index).get_or_throw()
      }
    }
    AlgebraicV("literal", [value]) -> value
  }
}

fun filter_on_predicate(tuples: list<toy-value>, predicate: toy-value) {
  match predicate {
    AlgebraicV("eq", [a, b]) -> {
      tuples.filter(fn(tuple) {
        val a_value = a.predicate_value(tuple)
        val b_value = b.predicate_value(tuple)
        a_value == b_value
      })
    }
  }
}

fun execute(query: toy-value) {
  match query {
    AlgebraicV("table", [AlgebraicV("A", [])]) -> {
      [
        AlgebraicV("tuple", [0.to_toy_nat, 0.to_toy_nat, 0.to_toy_nat]),
        AlgebraicV("tuple", [1.to_toy_nat, 0.to_toy_nat, 2.to_toy_nat]),
        AlgebraicV("tuple", [2.to_toy_nat, 1.to_toy_nat, 4.to_toy_nat]),
      ]
    }
    AlgebraicV("table", [AlgebraicV("B", [])]) -> {
      [
        AlgebraicV("tuple", [0.to_toy_nat, 6.to_toy_nat]),
        AlgebraicV("tuple", [1.to_toy_nat, 8.to_toy_nat]),
      ]
    }
    AlgebraicV("select", [sub_query, predicate]) -> {
      sub_query.execute.filter_on_predicate(predicate)
    }
    AlgebraicV("project", [sub_query, column_indices_value]) -> {
      val column_indicies: list<int> = column_indices_value
        .toy_list_to_list
        .map(toy_nat_to_int)
      sub_query.execute.map(fn(tuple_value) {
        match tuple_value {
          AlgebraicV("tuple", args) -> {
            val column_values = column_indicies.map(fn(column_index) {
              args.at(column_index).get_or_throw()
            })
            AlgebraicV("tuple", column_values)
          }
        }
      })
    }
    AlgebraicV("cross", [a_query, b_query]) -> {
      val a_query_tuples = a_query.execute
      val b_query_tuples = b_query.execute
      a_query_tuples.cross(b_query_tuples, fn(a_query_tuple, b_query_tuple) {
        match a_query_tuple {
          AlgebraicV("tuple", a_args) -> {
            match b_query_tuple {
              AlgebraicV("tuple", b_args) ->
                AlgebraicV("tuple", a_args ++ b_args)
            }
          }
        }
      })
    }
    AlgebraicV("diff", [a_query, b_query]) -> { // unoptimized
      val a_query_tuples = a_query.execute
      val b_query_tuples = b_query.execute
      a_query_tuples.filter(fn(a_query_tuple)
        !b_query_tuples.any(fn(b_query_tuple) a_query_tuple == b_query_tuple)
      )
    }
    AlgebraicV("union", [a_query, b_query]) -> {
      val a_query_tuples = a_query.execute
      val b_query_tuples = b_query.execute
      a_query_tuples ++ b_query_tuples
    }
  }
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
        ConstructorV(option_name, params) -> {
          if (params.length != operands.length) then {
            throw("Unexpected number of arguments. Expected " ++ params.length.show ++ ", but got " ++ operands.length.show)
          }
          AlgebraicV(option_name, operand_values)
        }
        GetV -> {
          if (operand_values.length != 1) then {
            throw("Unexpected number of arguments. Expected 1, but got " ++ operands.length.show)
          }
          val operand_value = assert-non-empty(operand_values).first()
          operand_value.execute.to_toy_list
        }
        _ -> throw("Cannot apply non-function")
      }
    }
    ValE(_, right_hand_side) -> right_hand_side.interp(env)
    DefE(_, params, body) -> CloV(params, body, env)
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

fun create_prelude_env(): <pure, store_update> env {
  val prelude_statements = [
    "def true(x, y) = x",
    "def false(x, y) = y",
    "def if(cond, then, else) = cond(then, else)()",
    r"type nat {
      O()
    | S(n)
    }",
    r"type list {
      nil()
    | cons(head, tail)
    }",
    r"type tables {
      A()
    | B()
    }", // A = (pk, fk, data), B = (pk, data)
    r"type predicateValue {
      column(index)
    | literal(value)
    }",
    r"type predicate {
      eq(a, b)
    }",
    r"type query {
      table(name)
    | select(query, predicate)
    | project(query, columnIndices)
    | cross(a, b)
    | diff(a, b)
    | union(a, b)
    }",
  ]

  val parsed_prelude_statements = prelude_statements.map(fn(statement) statement.tokenize.parse_exp)


  thread/hash-map()
    .insert_all([("get", GetV)]) // atomic functions
    .add_block_statements(parsed_prelude_statements)
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
  prog.tokenize.parse_exp.interp(create_prelude_env())
}

pub fun test()
  check(IntV(42))
    "(fn(x) x)(42)".run
  check(IntV(42))
    "{ val x = 42; val y = x; y }".run
  check(IntV(42))
    "{ val x = (fn(x) x)(42); x }".run
  check(IntV(42))
    "{ def g(x) = f(x); def f(x) = x; g(42) }".run
  check(IntV(42))
    "(fn(x) fn() x)(42)()".run
  check(IntV(1))
    "(fn(x, y) x)(1, 2)".run
  check(IntV(42))
    r"{
      def true(x, y) = x;
      def false(x, y) = y;
      def if(cond, then, else) = cond(then(), else());

      val whatWeWant = 42;
      val dontReturnThis = 0;

      if(true,
        fn() whatWeWant,
        fn() dontReturnThis
      )
    }".run
  check(IntV(1))
    r"{
      type myType {
        pair(fst, snd)
      };
      match pair(1, 2) {
        pair(x, y) x
      }
    }".run
  check(IntV(1))
    r"{
      match cons(1, nil()) {
        cons(head, tail) head
      }
    }".run
  check([
        AlgebraicV("tuple", [0.to_toy_nat, 0.to_toy_nat, 0.to_toy_nat]),
        AlgebraicV("tuple", [1.to_toy_nat, 0.to_toy_nat, 2.to_toy_nat]),
        AlgebraicV("tuple", [2.to_toy_nat, 1.to_toy_nat, 4.to_toy_nat]),
      ].to_toy_list)
    r"{
      get(table(A()))
    }".run
  check([
        AlgebraicV("tuple", [0.to_toy_nat, 6.to_toy_nat]),
        AlgebraicV("tuple", [1.to_toy_nat, 8.to_toy_nat]),
      ].to_toy_list)
    r"{
      get(table(B()))
    }".run
  check([
        AlgebraicV("tuple", [0.to_toy_nat, 0.to_toy_nat, 0.to_toy_nat]),
      ].to_toy_list)
    r"{
      get(select(table(A()), eq(column(O()), literal(O()))))
    }".run
  check([
        AlgebraicV("tuple", [0.to_toy_nat]),
        AlgebraicV("tuple", [2.to_toy_nat]),
        AlgebraicV("tuple", [4.to_toy_nat]),
      ].to_toy_list)
    r"{
      get(project(table(A()), cons(S(S(O())), nil())))
    }".run
  check([
        AlgebraicV("tuple", [0.to_toy_nat, 0.to_toy_nat, 0.to_toy_nat, 0.to_toy_nat, 6.to_toy_nat]),
        AlgebraicV("tuple", [0.to_toy_nat, 0.to_toy_nat, 0.to_toy_nat, 1.to_toy_nat, 8.to_toy_nat]),
        AlgebraicV("tuple", [1.to_toy_nat, 0.to_toy_nat, 2.to_toy_nat, 0.to_toy_nat, 6.to_toy_nat]),
        AlgebraicV("tuple", [1.to_toy_nat, 0.to_toy_nat, 2.to_toy_nat, 1.to_toy_nat, 8.to_toy_nat]),
        AlgebraicV("tuple", [2.to_toy_nat, 1.to_toy_nat, 4.to_toy_nat, 0.to_toy_nat, 6.to_toy_nat]),
        AlgebraicV("tuple", [2.to_toy_nat, 1.to_toy_nat, 4.to_toy_nat, 1.to_toy_nat, 8.to_toy_nat]),
      ].to_toy_list)
    r"{
      get(cross(table(A()), table(B())))
    }".run
  check([
        AlgebraicV("tuple", [1.to_toy_nat, 0.to_toy_nat, 2.to_toy_nat]),
        AlgebraicV("tuple", [2.to_toy_nat, 1.to_toy_nat, 4.to_toy_nat]),
      ].to_toy_list)
    r"{
      val first = select(table(A()), eq(column(O()), literal(O())));
      get(diff(table(A()), first))
    }".run
  check([
        AlgebraicV("tuple", [1.to_toy_nat, 0.to_toy_nat, 2.to_toy_nat]),
        AlgebraicV("tuple", [2.to_toy_nat, 1.to_toy_nat, 4.to_toy_nat]),
      ].to_toy_list)
    r"{
      val second = select(table(A()), eq(column(O()), literal(S(O()))));
      val third = select(table(A()), eq(column(O()), literal(S(S(O())))));
      get(union(second, third))
    }".run
  check([
        AlgebraicV("tuple", [0.to_toy_nat, 0.to_toy_nat, 0.to_toy_nat, 0.to_toy_nat, 6.to_toy_nat]),
        AlgebraicV("tuple", [1.to_toy_nat, 0.to_toy_nat, 2.to_toy_nat, 0.to_toy_nat, 6.to_toy_nat]),
        AlgebraicV("tuple", [2.to_toy_nat, 1.to_toy_nat, 4.to_toy_nat, 1.to_toy_nat, 8.to_toy_nat]),
      ].to_toy_list)
    r"{
      def join(a, b, pred) = {
        select(cross(a, b), pred)
      };
      get(join(table(A()), table(B()), eq(column(S(O())), column(S(S(S(O())))))))
    }".run
  // not quite right since we're not doing uniques
  check([
    AlgebraicV("tuple", [1.to_toy_nat, 0.to_toy_nat, 2.to_toy_nat]),
    AlgebraicV("tuple", [1.to_toy_nat, 0.to_toy_nat, 2.to_toy_nat]),
  ].to_toy_list)
    r"{
      def intersection(a, b) = {
        val left = diff(a, b);
        val right = diff(b, a);
        val xor = union(left, right);
        val all = union(a, b);
        diff(all, xor)
      };
      val first = select(table(A()), eq(column(O()), literal(O())));
      val second = select(table(A()), eq(column(O()), literal(S(O()))));
      val third = select(table(A()), eq(column(O()), literal(S(S(O())))));
      val firstAndSecond = union(first, second);
      val secondAndThird = union(second, third);

      get(intersection(firstAndSecond, secondAndThird))
    }".run
  