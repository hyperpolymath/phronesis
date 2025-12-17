# SPDX-License-Identifier: AGPL-3.0-or-later
# Tests for Phronesis Lexer v0.2.x features

defmodule Phronesis.LexerV02Test do
  use ExUnit.Case, async: true
  alias Phronesis.Lexer

  describe "hex integers (0x...)" do
    test "parses simple hex" do
      {:ok, tokens} = Lexer.tokenize("0xFF")
      assert [{:hex_integer, 255, 1, 1}, {:eof, nil, 1, 5}] = tokens
    end

    test "parses uppercase hex prefix" do
      {:ok, tokens} = Lexer.tokenize("0XFF")
      assert [{:hex_integer, 255, 1, 1}, {:eof, nil, 1, 5}] = tokens
    end

    test "parses multi-digit hex" do
      {:ok, tokens} = Lexer.tokenize("0xDEADBEEF")
      assert [{:hex_integer, 0xDEADBEEF, 1, 1}, _] = tokens
    end

    test "parses lowercase hex" do
      {:ok, tokens} = Lexer.tokenize("0xabcdef")
      assert [{:hex_integer, 0xABCDEF, 1, 1}, _] = tokens
    end

    test "errors on invalid hex digit" do
      {:error, {:lexer_error, msg, _, _}} = Lexer.tokenize("0xGG")
      assert msg =~ "invalid hex"
    end

    test "errors on empty hex" do
      {:error, {:lexer_error, msg, _, _}} = Lexer.tokenize("0x ")
      assert msg =~ "expected hex digits"
    end
  end

  describe "binary integers (0b...)" do
    test "parses simple binary" do
      {:ok, tokens} = Lexer.tokenize("0b1010")
      assert [{:binary_integer, 10, 1, 1}, {:eof, nil, 1, 7}] = tokens
    end

    test "parses uppercase binary prefix" do
      {:ok, tokens} = Lexer.tokenize("0B1111")
      assert [{:binary_integer, 15, 1, 1}, _] = tokens
    end

    test "parses long binary" do
      {:ok, tokens} = Lexer.tokenize("0b11110000")
      assert [{:binary_integer, 240, 1, 1}, _] = tokens
    end

    test "errors on invalid binary digit" do
      {:error, {:lexer_error, msg, _, _}} = Lexer.tokenize("0b2")
      assert msg =~ "invalid binary"
    end

    test "errors on empty binary" do
      {:error, {:lexer_error, msg, _, _}} = Lexer.tokenize("0b ")
      assert msg =~ "expected binary digits"
    end
  end

  describe "octal integers (0o...)" do
    test "parses simple octal" do
      {:ok, tokens} = Lexer.tokenize("0o755")
      assert [{:octal_integer, 493, 1, 1}, {:eof, nil, 1, 6}] = tokens
    end

    test "parses uppercase octal prefix" do
      {:ok, tokens} = Lexer.tokenize("0O777")
      assert [{:octal_integer, 511, 1, 1}, _] = tokens
    end

    test "errors on invalid octal digit" do
      {:error, {:lexer_error, msg, _, _}} = Lexer.tokenize("0o8")
      assert msg =~ "invalid octal"
    end

    test "errors on empty octal" do
      {:error, {:lexer_error, msg, _, _}} = Lexer.tokenize("0o ")
      assert msg =~ "expected octal digits"
    end
  end

  describe "scientific notation" do
    test "parses simple scientific" do
      {:ok, tokens} = Lexer.tokenize("1e10")
      assert [{:float, 1.0e10, 1, 1}, _] = tokens
    end

    test "parses with decimal" do
      {:ok, tokens} = Lexer.tokenize("1.5e10")
      assert [{:float, 1.5e10, 1, 1}, _] = tokens
    end

    test "parses negative exponent" do
      {:ok, tokens} = Lexer.tokenize("3e-5")
      assert [{:float, 3.0e-5, 1, 1}, _] = tokens
    end

    test "parses positive exponent" do
      {:ok, tokens} = Lexer.tokenize("2.5e+3")
      assert [{:float, 2500.0, 1, 1}, _] = tokens
    end

    test "parses uppercase E" do
      {:ok, tokens} = Lexer.tokenize("1E6")
      assert [{:float, 1.0e6, 1, 1}, _] = tokens
    end
  end

  describe "raw strings (r\"...\")" do
    test "parses raw string" do
      {:ok, tokens} = Lexer.tokenize(~S(r"hello"))
      assert [{:raw_string, "hello", 1, 1}, _] = tokens
    end

    test "preserves backslashes" do
      {:ok, tokens} = Lexer.tokenize(~S(r"path\to\file"))
      assert [{:raw_string, "path\\to\\file", 1, 1}, _] = tokens
    end

    test "preserves escape sequences" do
      {:ok, tokens} = Lexer.tokenize(~S(r"no\nnewline"))
      assert [{:raw_string, "no\\nnewline", 1, 1}, _] = tokens
    end

    test "handles empty raw string" do
      {:ok, tokens} = Lexer.tokenize(~S(r""))
      assert [{:raw_string, "", 1, 1}, _] = tokens
    end
  end

  describe "multi-line strings (\"\"\"...\"\"\")" do
    test "parses multi-line string" do
      {:ok, tokens} = Lexer.tokenize(~S("""hello"""))
      assert [{:multiline_string, "hello", 1, 1}, _] = tokens
    end

    test "preserves newlines" do
      input = ~S("""line1
line2""")
      {:ok, tokens} = Lexer.tokenize(input)
      assert [{:multiline_string, "line1\nline2", 1, 1}, _] = tokens
    end

    test "handles empty multi-line string" do
      {:ok, tokens} = Lexer.tokenize(~S(""""""))
      assert [{:multiline_string, "", 1, 1}, _] = tokens
    end
  end

  describe "modulo operator (%)" do
    test "parses modulo" do
      {:ok, tokens} = Lexer.tokenize("10 % 3")
      assert [
        {:integer, 10, 1, 1},
        {:percent, "%", 1, 4},
        {:integer, 3, 1, 6},
        {:eof, nil, _, _}
      ] = tokens
    end
  end

  describe "optional chaining (?.)" do
    test "parses optional chaining" do
      {:ok, tokens} = Lexer.tokenize("a?.b")
      assert [
        {:identifier, "a", 1, 1},
        {:question_dot, "?.", 1, 2},
        {:identifier, "b", 1, 4},
        {:eof, nil, _, _}
      ] = tokens
    end
  end

  describe "null coalescing (??)" do
    test "parses null coalescing" do
      {:ok, tokens} = Lexer.tokenize("a ?? b")
      assert [
        {:identifier, "a", 1, 1},
        {:double_question, "??", 1, 3},
        {:identifier, "b", 1, 6},
        {:eof, nil, _, _}
      ] = tokens
    end
  end

  describe "null keyword" do
    test "parses null" do
      {:ok, tokens} = Lexer.tokenize("null")
      assert [{:null, "null", 1, 1}, {:eof, nil, _, _}] = tokens
    end
  end

  describe "brackets and braces" do
    test "parses square brackets" do
      {:ok, tokens} = Lexer.tokenize("[1, 2]")
      assert [
        {:lbracket, "[", 1, 1},
        {:integer, 1, 1, 2},
        {:comma, ",", 1, 3},
        {:integer, 2, 1, 5},
        {:rbracket, "]", 1, 6},
        {:eof, nil, _, _}
      ] = tokens
    end

    test "parses curly braces" do
      {:ok, tokens} = Lexer.tokenize("{a: 1}")
      assert [
        {:lbrace, "{", 1, 1},
        {:identifier, "a", 1, 2},
        {:colon, ":", 1, 3},
        {:integer, 1, 1, 5},
        {:rbrace, "}", 1, 6},
        {:eof, nil, _, _}
      ] = tokens
    end
  end

  describe "IPv6 addresses" do
    test "parses full IPv6 address" do
      {:ok, tokens} = Lexer.tokenize("2001:0db8:85a3:0000:0000:8a2e:0370:7334")
      assert [{:ipv6_address, "2001:0db8:85a3:0000:0000:8a2e:0370:7334", 1, 1}, _] = tokens
    end

    test "parses compressed IPv6 (::1)" do
      {:ok, tokens} = Lexer.tokenize("::1")
      assert [{:ipv6_address, "::1", 1, 1}, {:eof, nil, _, _}] = tokens
    end

    test "parses compressed IPv6 (fe80::1)" do
      {:ok, tokens} = Lexer.tokenize("fe80::1")
      assert [{:ipv6_address, "fe80::1", 1, 1}, _] = tokens
    end

    test "parses IPv6 with CIDR notation" do
      {:ok, tokens} = Lexer.tokenize("2001:db8::/32")
      assert [{:ipv6_address, "2001:db8::/32", 1, 1}, _] = tokens
    end

    test "parses loopback with CIDR" do
      {:ok, tokens} = Lexer.tokenize("::1/128")
      assert [{:ipv6_address, "::1/128", 1, 1}, _] = tokens
    end

    test "parses IPv4-mapped IPv6" do
      {:ok, tokens} = Lexer.tokenize("::ffff:192.168.1.1")
      assert [{:ipv6_address, "::ffff:192.168.1.1", 1, 1}, _] = tokens
    end

    test "parses link-local prefix" do
      {:ok, tokens} = Lexer.tokenize("fe80::/10")
      assert [{:ipv6_address, "fe80::/10", 1, 1}, _] = tokens
    end

    test "parses uppercase hex in IPv6" do
      {:ok, tokens} = Lexer.tokenize("2001:DB8::ABCD")
      assert [{:ipv6_address, "2001:DB8::ABCD", 1, 1}, _] = tokens
    end
  end

  describe "string interpolation" do
    test "parses simple interpolation" do
      {:ok, tokens} = Lexer.tokenize(~S("Hello ${name}!"))

      assert [{:interpolated_string, parts, 1, 1}, {:eof, nil, _, _}] = tokens
      assert [
        {:string, "Hello "},
        {:expr, [{:identifier, "name", _, _}]},
        {:string, "!"}
      ] = parts
    end

    test "parses multiple interpolations" do
      {:ok, tokens} = Lexer.tokenize(~S("${a} and ${b}"))

      assert [{:interpolated_string, parts, 1, 1}, _] = tokens
      assert [
        {:expr, [{:identifier, "a", _, _}]},
        {:string, " and "},
        {:expr, [{:identifier, "b", _, _}]}
      ] = parts
    end

    test "parses expression in interpolation" do
      {:ok, tokens} = Lexer.tokenize(~S("Result: ${x + 1}"))

      assert [{:interpolated_string, parts, 1, 1}, _] = tokens
      assert [
        {:string, "Result: "},
        {:expr, [
          {:identifier, "x", _, _},
          {:plus, "+", _, _},
          {:integer, 1, _, _}
        ]}
      ] = parts
    end

    test "parses string without interpolation as regular string" do
      {:ok, tokens} = Lexer.tokenize(~S("no interpolation"))

      assert [{:string, "no interpolation", 1, 1}, {:eof, nil, _, _}] = tokens
    end

    test "handles escaped dollar sign" do
      {:ok, tokens} = Lexer.tokenize(~S("price is \$100"))

      assert [{:string, "price is $100", 1, 1}, _] = tokens
    end

    test "handles nested braces in interpolation" do
      {:ok, tokens} = Lexer.tokenize(~S("value: ${record.field}"))

      assert [{:interpolated_string, parts, 1, 1}, _] = tokens
      assert [
        {:string, "value: "},
        {:expr, [
          {:identifier, "record", _, _},
          {:dot, ".", _, _},
          {:identifier, "field", _, _}
        ]}
      ] = parts
    end
  end

  describe "combined v0.2.x features" do
    test "complex expression with new features" do
      input = "CONST mask = 0xFF AND value ?? 0b1010"
      {:ok, tokens} = Lexer.tokenize(input)

      assert [
        {:const, "CONST", 1, 1},
        {:identifier, "mask", 1, 7},
        {:assign, "=", 1, 12},
        {:hex_integer, 255, 1, 14},
        {:and, "AND", 1, 19},
        {:identifier, "value", 1, 23},
        {:double_question, "??", 1, 29},
        {:binary_integer, 10, 1, 32},
        {:eof, nil, _, _}
      ] = tokens
    end

    test "IPv6 in policy condition" do
      input = "source_ip == ::1"
      {:ok, tokens} = Lexer.tokenize(input)

      assert [
        {:identifier, "source_ip", 1, 1},
        {:eq, "==", 1, 11},
        {:ipv6_address, "::1", 1, 14},
        {:eof, nil, _, _}
      ] = tokens
    end

    test "optional chaining tokenization" do
      {:ok, tokens} = Lexer.tokenize("record?.field?.nested")

      assert [
        {:identifier, "record", 1, 1},
        {:question_dot, "?.", 1, 7},
        {:identifier, "field", 1, 9},
        {:question_dot, "?.", 1, 14},
        {:identifier, "nested", 1, 16},
        {:eof, nil, _, _}
      ] = tokens
    end

    test "null coalescing with optional chaining" do
      {:ok, tokens} = Lexer.tokenize("record?.value ?? 0")

      assert [
        {:identifier, "record", 1, 1},
        {:question_dot, "?.", 1, 7},
        {:identifier, "value", 1, 9},
        {:double_question, "??", 1, 15},
        {:integer, 0, 1, 18},
        {:eof, nil, _, _}
      ] = tokens
    end
  end
end
