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

fun add_block_statements(env: type-env, exps_with_poses: list<exp_with_pos>) {
  val rec_defs = exps_with_poses.flatmap-maybe(fn (exp_with_pos) {
    match exp_with_pos.exp {
      DefE(rec_def) -> Just(rec_def)
      _ -> Nothing
    }
  })

  // ensure recursive functions have correct type
  val env_with_rec_defs = exps_with_poses.foldl(env, fn(acc_env, block_exp) {
    match block_exp.exp {
      DefE(name, params, return_type, _)-> {
        val param_types = params.map(declaration/type_tag)
        acc_env.insert(name, ArrowT(param_types, return_type))
      }
      _ -> acc_env
    }
  })
  exps_with_poses.foreach(fn(block_exp) {
    match block_exp.exp {
      DefE(_, params, return_type, body) -> {
        val env_with_params = env_with_rec_defs.insert_all(params.map(fn(param) (param.name, param.type_tag)))
        val inferred_return_type = body.typecheck(env_with_params)
        if (!(inferred_return_type == return_type)) then {
          throw("Expected type " ++ return_type.show ++ ", but got " ++ inferred_return_type.show)
        }
      }
      _ -> ()
    }
  })

  exps_with_poses.foldl(env, fn(acc_env, block_exp) {
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
      _ -> acc_env
    }
  })
}

fun typecheck(exp_with_pos: exp_with_pos, env: type-env): pure toy-type {
  val exp = exp_with_pos.exp
  val start = exp_with_pos.start
  match exp {
    IntE(_) -> IntT
    BlockE(exps) -> {
      val extended_env = env.add_block_statements(exps.all_but_last)
      exps.last.typecheck(extended_env)
    }
    FnE(params, body) -> {
      val extended_env = env.insert_all(params.map(fn(param) (param.name, param.type_tag)))
      val return_type = body.typecheck(extended_env)
      ArrowT(params.map(declaration/type_tag), return_type)
    }
    IdE(name) -> {
      match env.get(name) {
        Just(toy-type) -> toy-type
        Nothing -> throw("Unbound identifier: " ++ name ++ " @ " ++ start.show)
      }
    }
    AppE(operator, operands) -> {
      val operator_type = operator.typecheck(env)
      val operand_types = operands.map(fn(operand) operand.typecheck(env))
      match operator_type {
        ArrowT(params, return_type) ->
          if (list/(==)(params, operand_types, ?(==) = fn(param, operand_type) pretend-no-div(fn() param == operand_type)))
          then return_type
          else throw("Expected parameter types " ++ params.show ++ ", but got " ++ operand_types.show)
        _ -> throw("Cannot apply non-function: " ++ exp.show ++ " @ " ++ start.show)
      }
    }
    ValE(_, rhs) -> rhs.typecheck(env)
    DefE(_, params, return_type, _) -> ArrowT(params.map(declaration/type_tag), return_type)
  }
}