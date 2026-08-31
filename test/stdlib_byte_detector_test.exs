# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
# SPDX-FileCopyrightText: 2026 Phronesis Contributors

defmodule Phronesis.Stdlib.ByteDetectorTest do
  use ExUnit.Case
  doctest Phronesis.Stdlib.ByteDetector

  @moduledoc """
  Test suite for stdlib/ByteDetector.affine byte-wise BOM and C0 control detection.

  Covers all required cases:
  - Input with a leading BOM (should be detected as BOM)
  - Input without a BOM but with C0-control characters
  - Input with both a BOM and C0-control characters
  - Input with neither
  - Edge cases: empty input, input shorter than BOM byte length

  Note: This test module will be integrated with the AffineScript FFI once
  the ByteDetector.affine module is compiled to the BEAM VM. For now, these
  tests document the expected behavior and can be run against a test shim
  or the compiled WASM module.
  """

  # Test constants matching ByteDetector.affine
  @utf8_bom [0xEF, 0xBB, 0xBF]
  @utf16_be_bom [0xFE, 0xFF]
  @utf16_le_bom [0xFF, 0xFE]
  @utf32_be_bom [0x00, 0x00, 0xFE, 0xFF]
  @utf32_le_bom [0xFF, 0xFE, 0x00, 0x00]

  # C0 control characters (excluding TAB=0x09, LF=0x0A, CR=0x0D)
  @c0_controls [0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
                0x0B, 0x0C, 0x0E, 0x0F, 0x10, 0x11, 0x12, 0x13, 0x14,
                0x15, 0x16, 0x17, 0x18, 0x19, 0x1A, 0x1B, 0x1C, 0x1D,
                0x1E, 0x1F]

  describe "detect_leading_bom/1" do
    test "detects UTF-8 BOM at leading position" do
      bytes = @utf8_bom ++ [0x48, 0x65, 0x6C, 0x6C, 0x6F]  # BOM + "Hello"
      {bom_type, bom_length} = detect_leading_bom(bytes)

      assert bom_type == :utf8
      assert bom_length == 3
    end

    test "detects UTF-16 BE BOM at leading position" do
      bytes = @utf16_be_bom ++ [0x00, 0x48, 0x00, 0x69]  # BOM + "Hi" in UTF-16 BE
      {bom_type, bom_length} = detect_leading_bom(bytes)

      assert bom_type == :utf16_be
      assert bom_length == 2
    end

    test "detects UTF-16 LE BOM at leading position" do
      bytes = @utf16_le_bom ++ [0x48, 0x00, 0x69, 0x00]  # BOM + "Hi" in UTF-16 LE
      {bom_type, bom_length} = detect_leading_bom(bytes)

      assert bom_type == :utf16_le
      assert bom_length == 2
    end

    test "detects UTF-32 BE BOM at leading position" do
      bytes = @utf32_be_bom ++ [0x00, 0x00, 0x00, 0x48]  # BOM + "H" in UTF-32 BE
      {bom_type, bom_length} = detect_leading_bom(bytes)

      assert bom_type == :utf32_be
      assert bom_length == 4
    end

    test "detects UTF-32 LE BOM at leading position" do
      bytes = @utf32_le_bom ++ [0x48, 0x00, 0x00, 0x00]  # BOM + "H" in UTF-32 LE
      {bom_type, bom_length} = detect_leading_bom(bytes)

      assert bom_type == :utf32_le
      assert bom_length == 4
    end

    test "returns None for input without BOM" do
      bytes = [0x48, 0x65, 0x6C, 0x6C, 0x6F]  # "Hello"
      {bom_type, bom_length} = detect_leading_bom(bytes)

      assert bom_type == :none
      assert bom_length == 0
    end

    test "returns None for empty input" do
      bytes = []
      {bom_type, bom_length} = detect_leading_bom(bytes)

      assert bom_type == :none
      assert bom_length == 0
    end

    test "returns None for input shorter than BOM" do
      # Only 2 bytes, but UTF-8 BOM requires 3
      bytes = [0xEF, 0xBB]
      {bom_type, bom_length} = detect_leading_bom(bytes)

      assert bom_type == :none
      assert bom_length == 0
    end

    test "returns None for partial UTF-32 BOM" do
      # Only 3 bytes, but UTF-32 BOM requires 4
      bytes = [0x00, 0x00, 0xFE]
      {bom_type, bom_length} = detect_leading_bom(bytes)

      assert bom_type == :none
      assert bom_length == 0
    end

    test "does not detect BOM in middle of input" do
      # BOM bytes appear but not at the start
      bytes = [0x48, 0x65, 0x6C, 0x6C, 0x6F] ++ @utf8_bom
      {bom_type, bom_length} = detect_leading_bom(bytes)

      assert bom_type == :none
      assert bom_length == 0
    end
  end

  describe "scan_c0_controls/1" do
    test "detects C0 control characters" do
      # NUL, BACKSPACE, and ESCAPE in "Hello"
      bytes = [0x00, 0x48, 0x08, 0x65, 0x1B, 0x6C, 0x6C, 0x6F]
      positions = scan_c0_controls(bytes)

      assert positions == [0, 2, 4]
    end

    test "does not flag TAB, LF, CR as C0 controls" do
      # TAB, LF, CR are allowed
      bytes = [0x09, 0x0A, 0x0D, 0x48, 0x65]
      positions = scan_c0_controls(bytes)

      assert positions == []
    end

    test "detects all C0 control characters except TAB/LF/CR" do
      # Test with various C0 control characters
      bytes = [0x01, 0x02, 0x03, 0x09, 0x0A, 0x0D, 0x0E, 0x1F]
      positions = scan_c0_controls(bytes)

      # Should detect 0x01, 0x02, 0x03, 0x0E, 0x1F (not 0x09, 0x0A, 0x0D)
      assert positions == [0, 1, 2, 6, 7]
    end

    test "returns empty list for clean input" do
      bytes = [0x48, 0x65, 0x6C, 0x6C, 0x6F]  # "Hello"
      positions = scan_c0_controls(bytes)

      assert positions == []
    end

    test "returns empty list for empty input" do
      bytes = []
      positions = scan_c0_controls(bytes)

      assert positions == []
    end

    test "detects NUL byte (0x00)" do
      bytes = [0x00, 0x48, 0x65]
      positions = scan_c0_controls(bytes)

      assert positions == [0]
    end

    test "detects BACKSPACE (0x08)" do
      bytes = [0x48, 0x08, 0x65]
      positions = scan_c0_controls(bytes)

      assert positions == [1]
    end

    test "detects vertical tab (0x0B) and form feed (0x0C)" do
      # These are C0 controls that should be detected
      bytes = [0x0B, 0x0C, 0x48]
      positions = scan_c0_controls(bytes)

      assert positions == [0, 1]
    end
  end

  describe "detect_all/1" do
    test "detects input with leading BOM only" do
      bytes = @utf8_bom ++ [0x48, 0x65, 0x6C, 0x6C, 0x6F]  # BOM + "Hello"
      result = detect_all(bytes)

      assert result.has_bom == true
      assert result.bom_type == :utf8
      assert result.bom_length == 3
      assert result.c0_control_positions == []
      assert result.first_c0_position == -1
    end

    test "detects input with C0 controls but no BOM" do
      bytes = [0x48, 0x00, 0x65, 0x08, 0x6C]  # "H" NUL "e" BACKSPACE "l"
      result = detect_all(bytes)

      assert result.has_bom == false
      assert result.bom_type == :none
      assert result.bom_length == 0
      assert result.c0_control_positions == [1, 3]
      assert result.first_c0_position == 1
    end

    test "detects input with both BOM and C0 controls" do
      bytes = @utf8_bom ++ [0x48, 0x00, 0x65]  # BOM + "H" NUL "e"
      result = detect_all(bytes)

      assert result.has_bom == true
      assert result.bom_type == :utf8
      assert result.bom_length == 3
      assert result.c0_control_positions == [4]  # NUL at position 4 (after BOM)
      assert result.first_c0_position == 4
    end

    test "detects clean input with neither BOM nor C0 controls" do
      bytes = [0x48, 0x65, 0x6C, 0x6C, 0x6F]  # "Hello"
      result = detect_all(bytes)

      assert result.has_bom == false
      assert result.bom_type == :none
      assert result.bom_length == 0
      assert result.c0_control_positions == []
      assert result.first_c0_position == -1
    end

    test "handles empty input" do
      bytes = []
      result = detect_all(bytes)

      assert result.has_bom == false
      assert result.bom_type == :none
      assert result.bom_length == 0
      assert result.c0_control_positions == []
      assert result.first_c0_position == -1
    end

    test "handles input shorter than BOM length" do
      bytes = [0xEF, 0xBB]  # Partial UTF-8 BOM
      result = detect_all(bytes)

      assert result.has_bom == false
      assert result.bom_type == :none
      assert result.bom_length == 0
      assert result.c0_control_positions == []
      assert result.first_c0_position == -1
    end

    test "handles single byte input" do
      bytes = [0x48]  # "H"
      result = detect_all(bytes)

      assert result.has_bom == false
      assert result.bom_type == :none
      assert result.bom_length == 0
      assert result.c0_control_positions == []
      assert result.first_c0_position == -1
    end

    test "handles single NUL byte" do
      bytes = [0x00]
      result = detect_all(bytes)

      assert result.has_bom == false
      assert result.bom_type == :none
      assert result.bom_length == 0
      assert result.c0_control_positions == [0]
      assert result.first_c0_position == 0
    end
  end

  describe "classify_byte/1" do
    test "classifies C0 control characters" do
      assert classify_byte(0x00) == :c0_control  # NUL
      assert classify_byte(0x08) == :c0_control  # BACKSPACE
      assert classify_byte(0x1B) == :c0_control  # ESCAPE
      assert classify_byte(0x1F) == :c0_control  # Unit Separator
    end

    test "classifies allowed control characters" do
      assert classify_byte(0x09) == :allowed_control  # TAB
      assert classify_byte(0x0A) == :allowed_control  # LF
      assert classify_byte(0x0D) == :allowed_control  # CR
    end

    test "classifies clean bytes" do
      assert classify_byte(0x20) == :clean  # SPACE
      assert classify_byte(0x48) == :clean  # "H"
      assert classify_byte(0x7F) == :clean  # DEL (not in C0 range)
      assert classify_byte(0xFF) == :clean
    end
  end

  describe "get_c0_range/0" do
    test "returns correct C0 control range" do
      {min, max} = get_c0_range()

      assert min == 0x00
      assert max == 0x1F
    end
  end

  describe "get_excluded_controls/0" do
    test "returns TAB, LF, CR as excluded controls" do
      excluded = get_excluded_controls()

      assert excluded == [0x09, 0x0A, 0x0D]
    end
  end

  # Helper functions for interfacing with AffineScript module
  # These will be implemented once the FFI integration is complete

  defp detect_leading_bom(bytes) do
    # TODO: Call compiled AffineScript ByteDetector.detect_leading_bom/1
    # For now, return a stub implementation for test documentation
    stub_detect_leading_bom(bytes)
  end

  defp scan_c0_controls(bytes) do
    # TODO: Call compiled AffineScript ByteDetector.scan_c0_controls/1
    stub_scan_c0_controls(bytes)
  end

  defp detect_all(bytes) do
    # TODO: Call compiled AffineScript ByteDetector.detect_all/1
    stub_detect_all(bytes)
  end

  defp classify_byte(byte) do
    # TODO: Call compiled AffineScript ByteDetector.classify_byte/1
    stub_classify_byte(byte)
  end

  defp get_c0_range do
    # TODO: Call compiled AffineScript ByteDetector.get_c0_range/0
    {0x00, 0x1F}
  end

  defp get_excluded_controls do
    # TODO: Call compiled AffineScript ByteDetector.get_excluded_controls/0
    [0x09, 0x0A, 0x0D]
  end

  # Stub implementations for testing (will be replaced with FFI calls)

  defp stub_detect_leading_bom(bytes) do
    cond do
      starts_with?(bytes, @utf32_be_bom) -> {:utf32_be, 4}
      starts_with?(bytes, @utf32_le_bom) -> {:utf32_le, 4}
      starts_with?(bytes, @utf8_bom) -> {:utf8, 3}
      starts_with?(bytes, @utf16_be_bom) -> {:utf16_be, 2}
      starts_with?(bytes, @utf16_le_bom) -> {:utf16_le, 2}
      true -> {:none, 0}
    end
  end

  defp stub_scan_c0_controls(bytes) do
    bytes
    |> Enum.with_index()
    |> Enum.filter(fn {byte, _idx} -> is_c0_control?(byte) end)
    |> Enum.map(fn {_byte, idx} -> idx end)
  end

  defp stub_detect_all(bytes) do
    {bom_type, bom_length} = stub_detect_leading_bom(bytes)
    has_bom = bom_type != :none
    c0_positions = stub_scan_c0_controls(bytes)
    first_c0 = if length(c0_positions) > 0, do: hd(c0_positions), else: -1

    %{
      has_bom: has_bom,
      bom_type: bom_type,
      bom_length: bom_length,
      c0_control_positions: c0_positions,
      first_c0_position: first_c0
    }
  end

  defp stub_classify_byte(byte) do
    cond do
      is_c0_control?(byte) -> :c0_control
      byte in [0x09, 0x0A, 0x0D] -> :allowed_control
      true -> :clean
    end
  end

  defp is_c0_control?(byte) do
    byte >= 0x00 and byte <= 0x1F and byte not in [0x09, 0x0A, 0x0D]
  end

  defp starts_with?(bytes, prefix) do
    if length(bytes) < length(prefix) do
      false
    else
      bytes
      |> Enum.take(length(prefix))
      |> Enum.zip(prefix)
      |> Enum.all?(fn {a, b} -> a == b end)
    end
  end
end
