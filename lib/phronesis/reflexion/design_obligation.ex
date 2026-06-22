# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Reflexion.DesignObligation do
  @moduledoc """
  A design obligation produced by the revaluation loop.

  Reflexion never silently mutates the language's semantics. When a change is
  classified as risky (a weakening, a drift, a contradiction, or an unresolved
  delta), the revaluation loop emits an *obligation* — a statement plus a small
  menu of acceptable resolutions (typically: prove the property still holds,
  mark the change as an intentional documented shift, or reject the change).
  """

  @type status :: :open | :discharged | :accepted_shift | :rejected

  @type t :: %__MODULE__{
          id: String.t(),
          classification: atom(),
          decision_id: String.t(),
          statement: String.t(),
          options: [String.t()],
          status: status()
        }

  defstruct id: nil,
            classification: :unresolved,
            decision_id: "—",
            statement: "",
            options: [],
            status: :open

  @doc "Create an open obligation."
  @spec new(atom(), String.t(), String.t(), [String.t()]) :: t()
  def new(classification, decision_id, statement, options) do
    %__MODULE__{
      id: :crypto.strong_rand_bytes(8) |> Base.encode16(case: :lower),
      classification: classification,
      decision_id: decision_id,
      statement: statement,
      options: options,
      status: :open
    }
  end

  @doc "A JSON-serialisable map."
  @spec to_map(t()) :: map()
  def to_map(%__MODULE__{} = o), do: Map.from_struct(o)
end
