# SPDX-License-Identifier: MPL-2.0
# Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.Reflexion.DesignLedgerTest do
  use ExUnit.Case, async: true

  alias Phronesis.Reflexion.DesignLedger

  test "append is monotonic and never mutates prior entries" do
    ledger = DesignLedger.new()
    l1 = DesignLedger.append(ledger, :note, %{n: 1})
    [first] = DesignLedger.entries(l1)
    l2 = DesignLedger.append(l1, :note, %{n: 2})

    assert length(DesignLedger.entries(l2)) == 2
    # the original first entry is unchanged
    assert hd(DesignLedger.entries(l2)) == first
  end

  test "each entry's hash chains off the previous entry" do
    ledger =
      DesignLedger.new()
      |> DesignLedger.append(:note, %{n: 1})
      |> DesignLedger.append(:note, %{n: 2})

    [e1, e2] = DesignLedger.entries(ledger)
    assert e1.prev_hash == nil
    assert e2.prev_hash == e1.hash
    assert e1.hash != e2.hash
    assert DesignLedger.verify(ledger) == :ok
  end

  test "tampering with a payload breaks integrity verification" do
    ledger =
      DesignLedger.new()
      |> DesignLedger.append(:note, %{n: 1})
      |> DesignLedger.append(:note, %{n: 2})

    [e1, e2] = DesignLedger.entries(ledger)
    tampered = %{ledger | entries: [%{e1 | payload: %{n: 999}}, e2]}

    assert {:error, _} = DesignLedger.verify(tampered)
  end
end
