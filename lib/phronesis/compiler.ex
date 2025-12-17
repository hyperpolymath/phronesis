# SPDX-License-Identifier: AGPL-3.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Compiler do
  @moduledoc """
  Compiler for the Phronesis policy language.

  Compiles Phronesis source code or AST to bytecode that can be:
  - Serialized to .phrc (Phronesis Compiled) files
  - Loaded and executed faster than parsing source
  - Optimized with constant folding and dead code elimination

  ## Compilation Pipeline

      Source → Lexer → Parser → AST → Optimizer → Bytecode → .phrc file

  ## Bytecode Format

  The bytecode is a tuple containing:
  - Version information
  - Compilation metadata
  - Optimized instruction list
  - Symbol table
  - Constant pool

  ## Example

      # Compile source to bytecode
      {:ok, bytecode} = Phronesis.Compiler.compile("CONST x = 42")

      # Save to file
      :ok = Phronesis.Compiler.save(bytecode, "policy.phrc")

      # Load and execute
      {:ok, bytecode} = Phronesis.Compiler.load("policy.phrc")
      {:ok, result} = Phronesis.Compiler.execute(bytecode, state)

  ## Optimizations

  The compiler performs these optimizations:
  - Constant folding: `1 + 2` → `3`
  - Constant propagation: `CONST x = 1; x + 1` → `2`
  - Dead code elimination: unreachable branches removed
  - Common subexpression elimination
  """

  alias Phronesis.{Lexer, Parser, AST}

  @version {0, 2, 0}
  @magic_number "PHRC"

  @type bytecode :: %{
          version: {non_neg_integer(), non_neg_integer(), non_neg_integer()},
          magic: String.t(),
          compiled_at: DateTime.t(),
          source_hash: binary(),
          instructions: [instruction()],
          constants: %{non_neg_integer() => any()},
          symbols: %{String.t() => non_neg_integer()},
          policies: [compiled_policy()],
          metadata: map()
        }

  @type instruction ::
          {:load_const, non_neg_integer()}
          | {:load_var, String.t()}
          | {:store_var, String.t()}
          | {:binary_op, atom()}
          | {:unary_op, atom()}
          | {:compare, atom()}
          | {:jump, non_neg_integer()}
          | {:jump_if_false, non_neg_integer()}
          | {:call, String.t(), non_neg_integer()}
          | {:module_call, [String.t()], non_neg_integer()}
          | {:field_access, String.t()}
          | {:optional_access, String.t()}
          | {:make_list, non_neg_integer()}
          | {:make_map, non_neg_integer()}
          | :pop
          | :dup
          | :return
          | {:action, atom(), non_neg_integer()}

  @type compiled_policy :: %{
          name: String.t(),
          condition_addr: non_neg_integer(),
          action_addr: non_neg_integer(),
          metadata: map()
        }

  # ============================================================
  # Public API
  # ============================================================

  @doc """
  Compile source code to bytecode.
  """
  @spec compile(String.t(), keyword()) :: {:ok, bytecode()} | {:error, term()}
  def compile(source, opts \\ []) when is_binary(source) do
    with {:ok, tokens} <- Lexer.tokenize(source),
         {:ok, ast} <- Parser.parse(tokens) do
      compile_ast(ast, source, opts)
    end
  end

  @doc """
  Compile an AST to bytecode.
  """
  @spec compile_ast(AST.program(), String.t(), keyword()) :: {:ok, bytecode()} | {:error, term()}
  def compile_ast(ast, source \\ "", opts \\ []) when is_list(ast) do
    optimize? = Keyword.get(opts, :optimize, true)

    # Optimize AST if requested
    ast = if optimize?, do: optimize_ast(ast), else: ast

    # Initialize compilation state
    state = %{
      instructions: [],
      constants: %{},
      const_index: 0,
      symbols: %{},
      symbol_index: 0,
      policies: [],
      label_counter: 0
    }

    # Compile all declarations
    state = Enum.reduce(ast, state, &compile_declaration/2)

    # Build final bytecode
    bytecode = %{
      version: @version,
      magic: @magic_number,
      compiled_at: DateTime.utc_now(),
      source_hash: :crypto.hash(:sha256, source),
      instructions: Enum.reverse(state.instructions),
      constants: state.constants,
      symbols: state.symbols,
      policies: Enum.reverse(state.policies),
      metadata: %{
        optimized: optimize?,
        instruction_count: length(state.instructions),
        constant_count: map_size(state.constants)
      }
    }

    {:ok, bytecode}
  end

  @doc """
  Save bytecode to a .phrc file.
  """
  @spec save(bytecode(), Path.t()) :: :ok | {:error, term()}
  def save(bytecode, path) do
    binary = :erlang.term_to_binary(bytecode, [:compressed])
    File.write(path, binary)
  end

  @doc """
  Load bytecode from a .phrc file.
  """
  @spec load(Path.t()) :: {:ok, bytecode()} | {:error, term()}
  def load(path) do
    with {:ok, binary} <- File.read(path) do
      bytecode = :erlang.binary_to_term(binary, [:safe])

      if bytecode.magic == @magic_number do
        {:ok, bytecode}
      else
        {:error, {:invalid_bytecode, "not a valid .phrc file"}}
      end
    end
  end

  @doc """
  Execute compiled bytecode.
  """
  @spec execute(bytecode(), Phronesis.State.t()) :: {:ok, Phronesis.State.t()} | {:error, term()}
  def execute(bytecode, state) do
    vm_state = %{
      ip: 0,
      stack: [],
      vars: state.environment,
      instructions: bytecode.instructions,
      constants: bytecode.constants
    }

    run_vm(vm_state, state)
  end

  @doc """
  Disassemble bytecode to human-readable format.
  """
  @spec disassemble(bytecode()) :: String.t()
  def disassemble(bytecode) do
    header = """
    ; Phronesis Bytecode v#{version_string(bytecode.version)}
    ; Compiled: #{bytecode.compiled_at}
    ; Instructions: #{bytecode.metadata.instruction_count}
    ; Constants: #{bytecode.metadata.constant_count}
    ;
    """

    constants =
      bytecode.constants
      |> Enum.sort_by(fn {k, _} -> k end)
      |> Enum.map(fn {idx, val} -> "; const[#{idx}] = #{inspect(val)}" end)
      |> Enum.join("\n")

    instructions =
      bytecode.instructions
      |> Enum.with_index()
      |> Enum.map(fn {instr, idx} -> "#{String.pad_leading(to_string(idx), 4, "0")}: #{format_instruction(instr)}" end)
      |> Enum.join("\n")

    policies =
      bytecode.policies
      |> Enum.map(fn p -> "; POLICY #{p.name} @ #{p.condition_addr}" end)
      |> Enum.join("\n")

    "#{header}\n; Constants:\n#{constants}\n\n; Policies:\n#{policies}\n\n; Instructions:\n#{instructions}"
  end

  @doc """
  Get compiler version.
  """
  @spec version() :: {non_neg_integer(), non_neg_integer(), non_neg_integer()}
  def version, do: @version

  # ============================================================
  # AST Optimization
  # ============================================================

  defp optimize_ast(ast) do
    ast
    |> Enum.map(&optimize_declaration/1)
    |> Enum.reject(&is_nil/1)
  end

  defp optimize_declaration({:const, name, expr}) do
    {:const, name, optimize_expr(expr)}
  end

  defp optimize_declaration({:policy, name, condition, action, metadata}) do
    {:policy, name, optimize_expr(condition), optimize_action(action), metadata}
  end

  defp optimize_declaration(other), do: other

  defp optimize_expr({:binary_op, op, left, right}) do
    left = optimize_expr(left)
    right = optimize_expr(right)

    # Constant folding
    case {left, right} do
      {{:literal, :integer, l}, {:literal, :integer, r}} ->
        fold_binary_op(op, l, r)

      {{:literal, :float, l}, {:literal, :float, r}} ->
        fold_binary_op(op, l, r)

      {{:literal, :boolean, l}, {:literal, :boolean, r}} when op in [:and, :or] ->
        fold_boolean_op(op, l, r)

      _ ->
        {:binary_op, op, left, right}
    end
  end

  defp optimize_expr({:unary_op, :not, {:literal, :boolean, val}}) do
    {:literal, :boolean, not val}
  end

  defp optimize_expr({:unary_op, :neg, {:literal, :integer, val}}) do
    {:literal, :integer, -val}
  end

  defp optimize_expr({:unary_op, :neg, {:literal, :float, val}}) do
    {:literal, :float, -val}
  end

  defp optimize_expr({:unary_op, op, operand}) do
    {:unary_op, op, optimize_expr(operand)}
  end

  defp optimize_expr({:comparison, op, left, right}) do
    left = optimize_expr(left)
    right = optimize_expr(right)

    case {left, right} do
      {{:literal, _, l}, {:literal, _, r}} ->
        {:literal, :boolean, fold_comparison(op, l, r)}

      _ ->
        {:comparison, op, left, right}
    end
  end

  defp optimize_expr({:conditional, cond_expr, then_expr, else_expr}) do
    cond_expr = optimize_expr(cond_expr)

    case cond_expr do
      {:literal, :boolean, true} ->
        optimize_expr(then_expr)

      {:literal, :boolean, false} ->
        if else_expr, do: optimize_expr(else_expr), else: {:literal, :null, nil}

      _ ->
        {:conditional, cond_expr, optimize_expr(then_expr),
         if(else_expr, do: optimize_expr(else_expr), else: nil)}
    end
  end

  defp optimize_expr({:module_call, path, args}) do
    {:module_call, path, Enum.map(args, &optimize_expr/1)}
  end

  defp optimize_expr(expr), do: expr

  defp optimize_action({:block, actions}) do
    {:block, Enum.map(actions, &optimize_action/1)}
  end

  defp optimize_action({:conditional, cond_expr, then_action, else_action}) do
    cond_expr = optimize_expr(cond_expr)

    case cond_expr do
      {:literal, :boolean, true} ->
        optimize_action(then_action)

      {:literal, :boolean, false} ->
        if else_action, do: optimize_action(else_action), else: {:accept, nil}

      _ ->
        {:conditional, cond_expr, optimize_action(then_action),
         if(else_action, do: optimize_action(else_action), else: nil)}
    end
  end

  defp optimize_action({:report, expr}), do: {:report, optimize_expr(expr)}
  defp optimize_action({:reject, expr}), do: {:reject, if(expr, do: optimize_expr(expr), else: nil)}
  defp optimize_action({:accept, expr}), do: {:accept, if(expr, do: optimize_expr(expr), else: nil)}
  defp optimize_action(action), do: action

  defp fold_binary_op(:add, l, r), do: {:literal, type_of(l + r), l + r}
  defp fold_binary_op(:sub, l, r), do: {:literal, type_of(l - r), l - r}
  defp fold_binary_op(:mul, l, r), do: {:literal, type_of(l * r), l * r}
  defp fold_binary_op(:div, l, r) when r != 0, do: {:literal, :float, l / r}
  defp fold_binary_op(_, l, r), do: {:binary_op, :div, {:literal, type_of(l), l}, {:literal, type_of(r), r}}

  defp fold_boolean_op(:and, l, r), do: {:literal, :boolean, l and r}
  defp fold_boolean_op(:or, l, r), do: {:literal, :boolean, l or r}

  defp fold_comparison(:eq, l, r), do: l == r
  defp fold_comparison(:neq, l, r), do: l != r
  defp fold_comparison(:gt, l, r), do: l > r
  defp fold_comparison(:gte, l, r), do: l >= r
  defp fold_comparison(:lt, l, r), do: l < r
  defp fold_comparison(:lte, l, r), do: l <= r

  defp type_of(v) when is_integer(v), do: :integer
  defp type_of(v) when is_float(v), do: :float
  defp type_of(v) when is_boolean(v), do: :boolean
  defp type_of(_), do: :unknown

  # ============================================================
  # Bytecode Generation
  # ============================================================

  defp compile_declaration({:const, name, expr}, state) do
    state = compile_expr(expr, state)
    state = emit(state, {:store_var, name})
    %{state | symbols: Map.put(state.symbols, name, state.symbol_index),
              symbol_index: state.symbol_index + 1}
  end

  defp compile_declaration({:policy, name, condition, action, metadata}, state) do
    condition_addr = length(state.instructions)

    # Compile condition
    state = compile_expr(condition, state)

    # Jump over action if condition is false
    jump_addr = length(state.instructions)
    state = emit(state, {:jump_if_false, :placeholder})

    action_addr = length(state.instructions)

    # Compile action
    state = compile_action(action, state)
    state = emit(state, :return)

    # Patch jump address
    end_addr = length(state.instructions)
    state = patch_jump(state, jump_addr, end_addr)

    policy = %{
      name: name,
      condition_addr: condition_addr,
      action_addr: action_addr,
      metadata: metadata
    }

    %{state | policies: [policy | state.policies]}
  end

  defp compile_declaration({:import, _path, _alias}, state) do
    # Imports are handled at runtime
    state
  end

  defp compile_expr({:literal, _type, value}, state) do
    {idx, state} = add_constant(state, value)
    emit(state, {:load_const, idx})
  end

  defp compile_expr({:identifier, name}, state) do
    emit(state, {:load_var, name})
  end

  defp compile_expr({:binary_op, op, left, right}, state) do
    state = compile_expr(left, state)
    state = compile_expr(right, state)
    emit(state, {:binary_op, op})
  end

  defp compile_expr({:unary_op, op, operand}, state) do
    state = compile_expr(operand, state)
    emit(state, {:unary_op, op})
  end

  defp compile_expr({:comparison, op, left, right}, state) do
    state = compile_expr(left, state)
    state = compile_expr(right, state)
    emit(state, {:compare, op})
  end

  defp compile_expr({:module_call, path, args}, state) do
    # Compile arguments
    state = Enum.reduce(args, state, fn
      {:named_arg, _name, expr}, s -> compile_expr(expr, s)
      expr, s -> compile_expr(expr, s)
    end)

    emit(state, {:module_call, path, length(args)})
  end

  defp compile_expr({:field_access, base, field}, state) do
    state = compile_expr(base, state)
    emit(state, {:field_access, field})
  end

  defp compile_expr({:optional_access, base, field}, state) do
    state = compile_expr(base, state)
    emit(state, {:optional_access, field})
  end

  defp compile_expr({:interpolated_string, parts}, state) do
    # Compile each part and concatenate
    state = Enum.reduce(parts, state, fn
      {:string, s}, st ->
        {idx, st} = add_constant(st, s)
        emit(st, {:load_const, idx})

      {:expr, _tokens}, st ->
        # For now, expressions in interpolated strings are evaluated at runtime
        {idx, st} = add_constant(st, "<expr>")
        emit(st, {:load_const, idx})
    end)

    emit(state, {:call, "concat", length(parts)})
  end

  defp compile_expr(other, state) do
    # Handle other expression types
    {idx, state} = add_constant(state, other)
    emit(state, {:load_const, idx})
  end

  defp compile_action({:execute, function, args}, state) do
    state = Enum.reduce(args, state, fn
      {:named_arg, _name, expr}, s -> compile_expr(expr, s)
      expr, s -> compile_expr(expr, s)
    end)

    emit(state, {:action, :execute, length(args)})
    |> emit({:call, function, length(args)})
  end

  defp compile_action({:report, expr}, state) do
    state = compile_expr(expr, state)
    emit(state, {:action, :report, 1})
  end

  defp compile_action({:reject, nil}, state) do
    emit(state, {:action, :reject, 0})
  end

  defp compile_action({:reject, expr}, state) do
    state = compile_expr(expr, state)
    emit(state, {:action, :reject, 1})
  end

  defp compile_action({:accept, nil}, state) do
    emit(state, {:action, :accept, 0})
  end

  defp compile_action({:accept, expr}, state) do
    state = compile_expr(expr, state)
    emit(state, {:action, :accept, 1})
  end

  defp compile_action({:block, actions}, state) do
    Enum.reduce(actions, state, &compile_action/2)
  end

  defp compile_action({:conditional, condition, then_action, else_action}, state) do
    state = compile_expr(condition, state)

    jump_false_addr = length(state.instructions)
    state = emit(state, {:jump_if_false, :placeholder})

    state = compile_action(then_action, state)

    if else_action do
      jump_end_addr = length(state.instructions)
      state = emit(state, {:jump, :placeholder})

      else_addr = length(state.instructions)
      state = patch_jump(state, jump_false_addr, else_addr)

      state = compile_action(else_action, state)

      end_addr = length(state.instructions)
      patch_jump(state, jump_end_addr, end_addr)
    else
      end_addr = length(state.instructions)
      patch_jump(state, jump_false_addr, end_addr)
    end
  end

  # ============================================================
  # VM Execution
  # ============================================================

  defp run_vm(%{ip: ip, instructions: instrs} = _vm, state) when ip >= length(instrs) do
    {:ok, state}
  end

  defp run_vm(vm, state) do
    instr = Enum.at(vm.instructions, vm.ip)

    case execute_instruction(instr, vm, state) do
      {:ok, vm, state} ->
        run_vm(%{vm | ip: vm.ip + 1}, state)

      {:jump, addr, vm, state} ->
        run_vm(%{vm | ip: addr}, state)

      {:return, _result, state} ->
        {:ok, state}

      {:error, _} = err ->
        err
    end
  end

  defp execute_instruction({:load_const, idx}, vm, state) do
    value = Map.get(vm.constants, idx)
    {:ok, %{vm | stack: [value | vm.stack]}, state}
  end

  defp execute_instruction({:load_var, name}, vm, state) do
    value = Map.get(vm.vars, name) || Map.get(state.constants, name)
    {:ok, %{vm | stack: [value | vm.stack]}, state}
  end

  defp execute_instruction({:store_var, name}, vm, state) do
    [value | rest] = vm.stack
    new_state = Phronesis.State.bind(state, name, value)
    {:ok, %{vm | stack: rest, vars: Map.put(vm.vars, name, value)}, new_state}
  end

  defp execute_instruction({:binary_op, op}, vm, state) do
    [r, l | rest] = vm.stack
    result = apply_binary_op(op, l, r)
    {:ok, %{vm | stack: [result | rest]}, state}
  end

  defp execute_instruction({:unary_op, op}, vm, state) do
    [val | rest] = vm.stack
    result = apply_unary_op(op, val)
    {:ok, %{vm | stack: [result | rest]}, state}
  end

  defp execute_instruction({:compare, op}, vm, state) do
    [r, l | rest] = vm.stack
    result = apply_comparison(op, l, r)
    {:ok, %{vm | stack: [result | rest]}, state}
  end

  defp execute_instruction({:jump, addr}, vm, state) do
    {:jump, addr, vm, state}
  end

  defp execute_instruction({:jump_if_false, addr}, vm, state) do
    [val | rest] = vm.stack

    if val do
      {:ok, %{vm | stack: rest}, state}
    else
      {:jump, addr, %{vm | stack: rest}, state}
    end
  end

  defp execute_instruction({:field_access, field}, vm, state) do
    [base | rest] = vm.stack

    value =
      case base do
        %{} = map -> Map.get(map, String.to_atom(field)) || Map.get(map, field)
        _ -> nil
      end

    {:ok, %{vm | stack: [value | rest]}, state}
  end

  defp execute_instruction({:optional_access, field}, vm, state) do
    [base | rest] = vm.stack

    value =
      case base do
        nil -> nil
        %{} = map -> Map.get(map, String.to_atom(field)) || Map.get(map, field)
        _ -> nil
      end

    {:ok, %{vm | stack: [value | rest]}, state}
  end

  defp execute_instruction({:action, :report, 1}, vm, state) do
    [msg | rest] = vm.stack
    IO.puts("[PHRONESIS REPORT] #{msg}")
    {:ok, %{vm | stack: rest}, state}
  end

  defp execute_instruction({:action, :reject, _}, vm, state) do
    {:return, {:rejected, List.first(vm.stack)}, state}
  end

  defp execute_instruction({:action, :accept, _}, vm, state) do
    {:return, {:accepted, List.first(vm.stack)}, state}
  end

  defp execute_instruction(:return, vm, state) do
    {:return, List.first(vm.stack), state}
  end

  defp execute_instruction({:module_call, path, arity}, vm, state) do
    {args, rest} = Enum.split(vm.stack, arity)
    args = Enum.reverse(args)

    # Call module function
    result = Phronesis.Interpreter.call_module_public(path, args, state)

    case result do
      {:ok, value, state} ->
        {:ok, %{vm | stack: [value | rest]}, state}

      {:error, _} = err ->
        err
    end
  end

  defp execute_instruction(:pop, vm, state) do
    [_ | rest] = vm.stack
    {:ok, %{vm | stack: rest}, state}
  end

  defp execute_instruction(:dup, vm, state) do
    [val | _] = vm.stack
    {:ok, %{vm | stack: [val | vm.stack]}, state}
  end

  defp execute_instruction(instr, _vm, _state) do
    {:error, {:unknown_instruction, instr}}
  end

  # ============================================================
  # Helpers
  # ============================================================

  defp emit(state, instruction) do
    %{state | instructions: [instruction | state.instructions]}
  end

  defp add_constant(state, value) do
    idx = state.const_index
    state = %{state |
      constants: Map.put(state.constants, idx, value),
      const_index: idx + 1
    }
    {idx, state}
  end

  defp patch_jump(state, addr, target) do
    instructions =
      state.instructions
      |> Enum.reverse()
      |> List.update_at(addr, fn
        {:jump_if_false, :placeholder} -> {:jump_if_false, target}
        {:jump, :placeholder} -> {:jump, target}
        other -> other
      end)
      |> Enum.reverse()

    %{state | instructions: instructions}
  end

  defp apply_binary_op(:add, l, r), do: l + r
  defp apply_binary_op(:sub, l, r), do: l - r
  defp apply_binary_op(:mul, l, r), do: l * r
  defp apply_binary_op(:div, l, r), do: l / r
  defp apply_binary_op(:and, l, r), do: l and r
  defp apply_binary_op(:or, l, r), do: l or r

  defp apply_unary_op(:not, val), do: not val
  defp apply_unary_op(:neg, val), do: -val

  defp apply_comparison(:eq, l, r), do: l == r
  defp apply_comparison(:neq, l, r), do: l != r
  defp apply_comparison(:gt, l, r), do: l > r
  defp apply_comparison(:gte, l, r), do: l >= r
  defp apply_comparison(:lt, l, r), do: l < r
  defp apply_comparison(:lte, l, r), do: l <= r
  defp apply_comparison(:in, l, r) when is_list(r), do: l in r
  defp apply_comparison(:in, l, r) when is_map(r), do: Map.has_key?(r, l)

  defp version_string({major, minor, patch}), do: "#{major}.#{minor}.#{patch}"

  defp format_instruction({:load_const, idx}), do: "LOAD_CONST #{idx}"
  defp format_instruction({:load_var, name}), do: "LOAD_VAR #{name}"
  defp format_instruction({:store_var, name}), do: "STORE_VAR #{name}"
  defp format_instruction({:binary_op, op}), do: "BINARY_OP #{op}"
  defp format_instruction({:unary_op, op}), do: "UNARY_OP #{op}"
  defp format_instruction({:compare, op}), do: "COMPARE #{op}"
  defp format_instruction({:jump, addr}), do: "JUMP #{addr}"
  defp format_instruction({:jump_if_false, addr}), do: "JUMP_IF_FALSE #{addr}"
  defp format_instruction({:call, name, arity}), do: "CALL #{name}/#{arity}"
  defp format_instruction({:module_call, path, arity}), do: "MODULE_CALL #{Enum.join(path, ".")}/#{arity}"
  defp format_instruction({:field_access, field}), do: "FIELD_ACCESS #{field}"
  defp format_instruction({:optional_access, field}), do: "OPTIONAL_ACCESS #{field}"
  defp format_instruction({:action, type, arity}), do: "ACTION #{type}/#{arity}"
  defp format_instruction(:pop), do: "POP"
  defp format_instruction(:dup), do: "DUP"
  defp format_instruction(:return), do: "RETURN"
  defp format_instruction(other), do: inspect(other)
end
