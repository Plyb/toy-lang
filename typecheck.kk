import parser
import std/data/hashmap
import std/data/hash
import non-empty-list
import std/core/undiv
import tokenizer

alias type-env = hash-map<string, toy-type>

fun insert_all(env: type-env, entries: list<(string, toy-type)>) {
  entries.foldl(env, fn(acc_env, (key, value)) acc_env.insert(key, value))
}

fun add_block_statements(env: type-env, exps_with_poses: list<exp_with_pos>): pure type-env {
  val updated_env = exps_with_poses.foldl(env, fn(acc_env, block_exp) {
    match block_exp.exp {
      ValE(Declaration(name, type_tag), right_hand_side) -> {
        val rhs_type = right_hand_side.typecheck(acc_env)
        if (!(rhs_type == type_tag)) then {
          throw("Expected type " ++ type_tag.show ++ ", but got " ++ rhs_type.show)
        }
        acc_env.insert(name, rhs_type)
      }
      DefE(name, params, return_type, _) -> {
        val param_types = params.map(declaration/type_tag)
        acc_env.insert(name, ArrowT(param_types, return_type))
      }
      TypeDefE(type_name, options) -> acc_env.insert_all(options.map(fn(option) {
        val param_types = option.params.map(type_tag)
        (option.name, ArrowT(param_types, AlgebraicT(type_name, block_exp.start)))
      }).to_list)
      _ -> acc_env
    }
  })

  // ensure recursive functions have correct type
  exps_with_poses.foreach(fn(block_exp) {
    match block_exp.exp {
      DefE(_, params, return_type, body) -> {
        val env_with_params = updated_env.insert_all(params.map(fn(param) (param.name, param.type_tag)))
        val inferred_return_type = body.typecheck(env_with_params)
        if (!(inferred_return_type == return_type)) then {
          throw("Expected type " ++ return_type.show ++ ", but got " ++ inferred_return_type.show)
        }
      }
      _ -> ()
    }
  })

  updated_env
}

fun typecheck(exp_with_pos: exp_with_pos, env: type-env): pure toy-type {
  val exp = exp_with_pos.exp
  val start = exp_with_pos.start
  match exp {
    IntE(_) -> IntT
    BlockE(exps) -> {
      val extended_env = env.add_block_statements(exps.all_but_last)
      val last_type = exps.last.typecheck(extended_env)
      
      match last_type {
        AlgebraicT(_) -> {
          // ensure algebraic types don't escape their definitions
          val there_are_constructors_for_last_type_in_outer_env = env.data.list.concat.any(fn((_, toy-type))
            match toy-type {
              ArrowT(_, return_type) -> return_type == last_type
              _ -> False
            }
          )
          if (!there_are_constructors_for_last_type_in_outer_env) then {
            throw("Typecheck: type " ++ last_type.show ++ " should not escape its definition, but it does at " ++ exps.last.show)
          }
        }
        _ -> ()
      }
      

      last_type
    }
    FnE(params, body) -> {
      val extended_env = env.insert_all(params.map(fn(param) (param.name, param.type_tag)))
      val return_type = body.typecheck(extended_env)
      ArrowT(params.map(declaration/type_tag), return_type)
    }
    IdE(name) -> {
      match env.get(name) {
        Just(toy-type) -> toy-type
        Nothing -> throw("Typecheck: Unbound identifier: " ++ name ++ " @ " ++ start.show)
      }
    }
    AppE(operator, operands) -> {
      val operator_type = operator.typecheck(env)
      val operand_types = operands.map(fn(operand) operand.typecheck(env))
      match operator_type {
        ArrowT(params, return_type) ->
          if (list/(==)(params, operand_types, ?(==) = fn(param, operand_type) pretend-no-div(fn() param == operand_type)))
          then return_type
          else throw("Typecheck: Expected parameter types " ++ params.show ++ ", but got " ++ operand_types.show)
        _ -> throw("Typecheck: Cannot apply non-function: " ++ exp.show ++ " @ " ++ start.show)
      }
    }
    ValE(_, rhs) -> rhs.typecheck(env)
    DefE(_, params, return_type, _) -> ArrowT(params.map(declaration/type_tag), return_type)
    TypeDefE(_, _) -> throw("Typecheck: type definitions don't have a type: " ++ exp.show ++ " @ " ++ start.show)
    MatchE(discriminee, cases) -> {
      val discriminee_type = discriminee.typecheck(env)
      val all_constructors_for_type = env.data.list.concat
        .filter(fn((_, toy_type)) {
          match toy_type {
            ArrowT(_, return_type) -> return_type == discriminee_type
            _ -> False
          }
        })
        .map(fn((constructor_name, toy_type)) {
          val params = match toy_type {
            ArrowT(params, _) -> params
            _ -> throw("Internal error: expected arrow type")
          }
          (constructor_name, params)
        })
      // if (!(all_constructors_for_type.length == cases.length)) then {
      //   throw("Typecheck: Unexpected number of cases. Discriminee has type " ++ discriminee_type.show
      //     ++ ", which has " ++ all_constructors_for_type.length.show ++ " constructors, but there are "
      //     ++ cases.length.show ++ "cases. At " ++ exp.show )
      // }
      val case_types = cases.map(fn(case) {
        val corresponding_constructor = match all_constructors_for_type.find(fn(constructor) case.constructor_name == constructor.tuple2/fst) {
          Just(constructor) -> constructor
          Nothing -> throw("Typecheck: unknown case " ++ case.constructor_name ++ " at " ++ exp.show)
        }
        // if (!(corresponding_constructor.snd.length == case.params.length)) then {
        //   throw("Typecheck: incorrect number of parameters. "
        //     ++ corresponding_constructor.fst.show ++ " should have " ++ corresponding_constructor.snd.length.show
        //     ++ ", but it has " ++ case.params.list/length.show ++ " at " ++ exp.show)
        // }

        val extended_env = env.insert_all(case.params.zip(corresponding_constructor.snd))
        case.body.typecheck(extended_env)
      })

      val first_case_type = case_types.non-empty-list/first
      val other_case_types = case_types.all_but_first
      other_case_types.foreach(fn(other_case_type) {
        if (!(first_case_type == other_case_type)) then {
          throw("Typecheck: case types do not match at " ++ exp_with_pos.exp_with_pos/exp.show) // current koka compiler causes a segfault if we use `exp` here instead of `exp_with_pos.exp_with_pos/exp`
        }
      })
      first_case_type
    }
  }
}