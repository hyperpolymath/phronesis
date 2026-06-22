# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Reflexion.ClaimExtractor do
  @moduledoc """
  Turns Phronesis toolchain artefacts into explicit `Phronesis.Reflexion.Claim`s.

  Day one this walks a *parsed program* — exactly what `Phronesis.parse/1` returns
  (`{:ok, [declaration()]}` where declarations are `Phronesis.AST` tuples). The
  load-bearing case is the map-territory mandate: when a policy's action subtree
  contains a `{:report, _}` node, the extractor emits a `:safety_preservation`
  claim that the policy preserves *REPORT-adequacy* (epistemic safety) under the
  policy's match condition.

  Ingest from the compiler, the formal/proof layer, and the benchmark suite are
  declared but stubbed (returning `[]` with a documented `TODO`) so the rest of
  the pipeline runs end-to-end today.
  """

  alias Phronesis.Reflexion.Claim

  @doc "Parse `source` and extract claims. Propagates parse errors."
  @spec extract_from_source(String.t()) :: {:ok, [Claim.t()]} | {:error, term()}
  def extract_from_source(source) when is_binary(source) do
    case Phronesis.parse(source) do
      {:ok, program} -> {:ok, extract(program)}
      {:error, _} = err -> err
    end
  end

  @doc "Extract claims from a parsed program (a list of `Phronesis.AST` declarations)."
  @spec extract([tuple()] | {:ok, [tuple()]}) :: [Claim.t()]
  def extract({:ok, program}), do: extract(program)

  def extract(program) when is_list(program) do
    Enum.flat_map(program, &claims_for_declaration/1)
  end

  @doc "TODO: ingest claims from compiler artefacts (`.phrc` / `Phronesis.Compiler`)."
  @spec extract_from_compiler(term()) :: [Claim.t()]
  def extract_from_compiler(_artifacts), do: []

  @doc "TODO: ingest proof obligations from `formal/` and `academic/formal-verification/`."
  @spec extract_from_proofs(term()) :: [Claim.t()]
  def extract_from_proofs(_paths), do: []

  @doc "TODO: ingest benchmark outcomes from `bench/` as evidence claims."
  @spec extract_from_benchmarks(term()) :: [Claim.t()]
  def extract_from_benchmarks(_results), do: []

  @doc "Human-readable rendering of an AST expression (used for path/claim labels)."
  @spec describe_expr(term()) :: String.t()
  def describe_expr({:literal, _type, value}), do: inspect(value)
  def describe_expr({:identifier, name}), do: name
  def describe_expr({:comparison, op, l, r}), do: "#{describe_expr(l)} #{op} #{describe_expr(r)}"
  def describe_expr({:binary_op, op, l, r}), do: "#{describe_expr(l)} #{op} #{describe_expr(r)}"
  def describe_expr({:unary_op, op, operand}), do: "#{op} #{describe_expr(operand)}"
  def describe_expr({:module_call, path, _args}), do: "#{Enum.join(path, ".")}(...)"
  def describe_expr(other), do: inspect(other)

  # --- per-declaration extraction --------------------------------------------

  defp claims_for_declaration({:const, name, expr}) do
    [
      Claim.provenance("const #{name}", describe_expr(expr),
        source: {:ast, :const},
        confidence: :asserted
      )
    ]
  end

  defp claims_for_declaration({:import, path, _alias}) do
    [
      Claim.provenance("import #{Enum.join(path, ".")}", "external module",
        source: {:ast, :import},
        confidence: :asserted
      )
    ]
  end

  defp claims_for_declaration({:policy, name, condition, action, _metadata}) do
    subject = "policy #{name}"
    condition_label = describe_expr(condition)

    discharge =
      Claim.obligation_discharge(subject, "decision-completeness",
        source: {:ast, :policy},
        confidence: :asserted,
        conditions: [condition_label]
      )

    [discharge] ++ report_claims(subject, condition_label, action) ++ decision_claims(subject, action)
  end

  defp claims_for_declaration(_other), do: []

  defp report_claims(subject, condition_label, action) do
    if contains_report?(action) do
      [
        Claim.safety_preservation(subject, "REPORT-adequacy", [condition_label],
          source: {:ast, :report},
          confidence: :asserted,
          metadata: %{property: "epistemic-safety", construct: "REPORT"}
        )
      ]
    else
      []
    end
  end

  defp decision_claims(subject, action) do
    case decision_kind(action) do
      nil ->
        []

      kind ->
        [
          Claim.evidence_for(subject, "decision:#{kind}",
            source: {:ast, kind},
            confidence: :asserted
          )
        ]
    end
  end

  # walk an action subtree looking for a REPORT node (the map-territory mandate)
  defp contains_report?({:report, _}), do: true
  defp contains_report?({:block, actions}), do: Enum.any?(actions, &contains_report?/1)

  defp contains_report?({:conditional, _cond, then_action, else_action}) do
    contains_report?(then_action) or (else_action != nil and contains_report?(else_action))
  end

  defp contains_report?(_), do: false

  defp decision_kind({:accept, _}), do: :accept
  defp decision_kind({:reject, _}), do: :reject
  defp decision_kind({:block, actions}), do: Enum.find_value(actions, &decision_kind/1)

  defp decision_kind({:conditional, _cond, then_action, else_action}) do
    decision_kind(then_action) || if(else_action, do: decision_kind(else_action))
  end

  defp decision_kind(_), do: nil
end
