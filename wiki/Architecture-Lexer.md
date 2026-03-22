# Architecture: Lexer

The tokenizer component of the Phronesis frontend.

---

## Overview

The lexer transforms source code into a stream of tokens. It's implemented as a hand-written scanner for maximum control and clarity.

---

## Token Types

```elixir
# Keywords
:policy, :const, :import, :as, :then, :if, :else, :priority,
:and, :or, :not, :accept, :reject, :report, :execute

# Literals
:integer, :float, :string, :boolean, :ip_address, :datetime

# Identifiers
:identifier

# Operators
:plus, :minus, :star, :slash, :percent,
:eq, :neq, :lt, :gt, :lte, :gte,
:in

# Punctuation
:lparen, :rparen, :lbracket, :rbracket, :lbrace, :rbrace,
:colon, :comma, :dot

# Special
:eof, :newline
```

---

## Token Structure

```elixir
defmodule Phronesis.Token do
  @type t :: %__MODULE__{
    type: atom(),
    value: any(),
    line: pos_integer(),
    column: pos_integer()
  }

  defstruct [:type, :value, :line, :column]
end
```

Example tokens:

```elixir
[
  %Token{type: :policy, value: "POLICY", line: 1, column: 1},
  %Token{type: :identifier, value: "my_policy", line: 1, column: 8},
  %Token{type: :colon, value: ":", line: 1, column: 17},
  %Token{type: :identifier, value: "route", line: 2, column: 3},
  %Token{type: :dot, value: ".", line: 2, column: 8},
  %Token{type: :identifier, value: "prefix", line: 2, column: 9},
  ...
]
```

---

## Scanning Algorithm

### Main Loop

```elixir
def tokenize(input) do
  scan(input, [], 1, 1)
end

defp scan("", tokens, _line, _col) do
  {:ok, Enum.reverse([%Token{type: :eof} | tokens])}
end

defp scan(input, tokens, line, col) do
  case next_token(input, line, col) do
    {:ok, token, rest, new_line, new_col} ->
      scan(rest, [token | tokens], new_line, new_col)
    {:error, reason} ->
      {:error, reason}
  end
end
```

### Token Recognition

```elixir
defp next_token(input, line, col) do
  input
  |> skip_whitespace_and_comments(line, col)
  |> recognize_token()
end

defp recognize_token({input, line, col}) do
  cond do
    # Keywords and identifiers
    match?({:ok, _}, scan_keyword_or_identifier(input)) ->
      scan_keyword_or_identifier(input, line, col)

    # Numbers
    match?({:ok, _}, scan_number(input)) ->
      scan_number(input, line, col)

    # Strings
    String.starts_with?(input, "\"") ->
      scan_string(input, line, col)

    # IP addresses
    match?({:ok, _}, scan_ip_address(input)) ->
      scan_ip_address(input, line, col)

    # Operators and punctuation
    true ->
      scan_operator_or_punctuation(input, line, col)
  end
end
```

---

## Keyword Recognition

Keywords are recognized after scanning an identifier:

```elixir
@keywords %{
  "POLICY" => :policy,
  "CONST" => :const,
  "IMPORT" => :import,
  "AS" => :as,
  "THEN" => :then,
  "IF" => :if,
  "ELSE" => :else,
  "PRIORITY" => :priority,
  "AND" => :and,
  "OR" => :or,
  "NOT" => :not,
  "ACCEPT" => :accept,
  "REJECT" => :reject,
  "REPORT" => :report,
  "EXECUTE" => :execute,
  "IN" => :in,
  "true" => :boolean,
  "false" => :boolean,
  "null" => :null
}

defp scan_keyword_or_identifier(input, line, col) do
  {word, rest} = scan_word(input)
  type = Map.get(@keywords, word, :identifier)
  value = if type == :boolean, do: word == "true", else: word

  {:ok, %Token{type: type, value: value, line: line, column: col},
   rest, line, col + String.length(word)}
end
```

---

## Literal Scanning

### Numbers

```elixir
defp scan_number(input, line, col) do
  {digits, rest} = scan_digits(input)

  case rest do
    "." <> after_dot ->
      {decimals, final_rest} = scan_digits(after_dot)
      value = String.to_float("#{digits}.#{decimals}")
      {:ok, %Token{type: :float, value: value, line: line, column: col},
       final_rest, line, col + String.length(digits) + 1 + String.length(decimals)}

    _ ->
      value = String.to_integer(digits)
      {:ok, %Token{type: :integer, value: value, line: line, column: col},
       rest, line, col + String.length(digits)}
  end
end
```

### Strings

```elixir
defp scan_string("\"" <> rest, line, col) do
  case scan_string_content(rest, "", line, col + 1) do
    {:ok, content, rest, end_line, end_col} ->
      {:ok, %Token{type: :string, value: content, line: line, column: col},
       rest, end_line, end_col}
    {:error, reason} ->
      {:error, reason}
  end
end

defp scan_string_content("\"" <> rest, acc, line, col) do
  {:ok, acc, rest, line, col + 1}
end

defp scan_string_content("\\" <> <<char::utf8>> <> rest, acc, line, col) do
  escaped = case char do
    ?n -> "\n"
    ?t -> "\t"
    ?r -> "\r"
    ?\\ -> "\\"
    ?" -> "\""
    _ -> <<char::utf8>>
  end
  scan_string_content(rest, acc <> escaped, line, col + 2)
end

defp scan_string_content(<<char::utf8>> <> rest, acc, line, col) do
  scan_string_content(rest, acc <> <<char::utf8>>, line, col + 1)
end

defp scan_string_content("", _acc, line, col) do
  {:error, {:unterminated_string, line, col}}
end
```

### IP Addresses

```elixir
defp scan_ip_address(input, line, col) do
  # Match IPv4: xxx.xxx.xxx.xxx[/xx]
  case Regex.run(~r/^(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})(\/\d{1,3})?/, input) do
    [full_match | _] ->
      {:ok, %Token{type: :ip_address, value: full_match, line: line, column: col},
       String.slice(input, String.length(full_match)..-1),
       line, col + String.length(full_match)}
    nil ->
      {:error, {:invalid_ip, line, col}}
  end
end
```

### DateTime

```elixir
defp scan_datetime(input, line, col) do
  # Match ISO 8601: YYYY-MM-DDTHH:MM:SSZ
  pattern = ~r/^(\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2})(Z|[+-]\d{2}:\d{2})?/

  case Regex.run(pattern, input) do
    [full_match | _] ->
      {:ok, %Token{type: :datetime, value: full_match, line: line, column: col},
       String.slice(input, String.length(full_match)..-1),
       line, col + String.length(full_match)}
    nil ->
      nil  # Not a datetime, try other patterns
  end
end
```

---

## Whitespace and Comments

```elixir
defp skip_whitespace_and_comments(input, line, col) do
  case input do
    # Newline
    "\n" <> rest ->
      skip_whitespace_and_comments(rest, line + 1, 1)

    # Other whitespace
    <<c::utf8>> <> rest when c in [?\s, ?\t, ?\r] ->
      skip_whitespace_and_comments(rest, line, col + 1)

    # Comment
    "#" <> rest ->
      {_, after_comment} = skip_until_newline(rest)
      skip_whitespace_and_comments(after_comment, line + 1, 1)

    # Not whitespace
    _ ->
      {input, line, col}
  end
end

defp skip_until_newline("\n" <> rest), do: {:newline, rest}
defp skip_until_newline(""), do: {:eof, ""}
defp skip_until_newline(<<_::utf8>> <> rest), do: skip_until_newline(rest)
```

---

## Operators

```elixir
@operators %{
  "==" => :eq,
  "!=" => :neq,
  "<=" => :lte,
  ">=" => :gte,
  "<" => :lt,
  ">" => :gt,
  "+" => :plus,
  "-" => :minus,
  "*" => :star,
  "/" => :slash,
  "%" => :percent,
  "(" => :lparen,
  ")" => :rparen,
  "[" => :lbracket,
  "]" => :rbracket,
  "{" => :lbrace,
  "}" => :rbrace,
  ":" => :colon,
  "," => :comma,
  "." => :dot
}

defp scan_operator_or_punctuation(input, line, col) do
  # Try two-character operators first
  two_char = String.slice(input, 0, 2)

  case Map.get(@operators, two_char) do
    nil ->
      # Try single-character
      one_char = String.first(input)
      case Map.get(@operators, one_char) do
        nil ->
          {:error, {:unexpected_character, one_char, line, col}}
        type ->
          {:ok, %Token{type: type, value: one_char, line: line, column: col},
           String.slice(input, 1..-1), line, col + 1}
      end
    type ->
      {:ok, %Token{type: type, value: two_char, line: line, column: col},
       String.slice(input, 2..-1), line, col + 2}
  end
end
```

---

## Error Handling

```elixir
@type error :: {:error, error_info()}
@type error_info ::
  {:unterminated_string, line :: pos_integer(), col :: pos_integer()}
  | {:unexpected_character, char :: String.t(), line :: pos_integer(), col :: pos_integer()}
  | {:invalid_number, line :: pos_integer(), col :: pos_integer()}
  | {:invalid_ip, line :: pos_integer(), col :: pos_integer()}

defp format_error({:unterminated_string, line, col}) do
  "Unterminated string at line #{line}, column #{col}"
end

defp format_error({:unexpected_character, char, line, col}) do
  "Unexpected character '#{char}' at line #{line}, column #{col}"
end
```

---

## Position Tracking

Every token carries position information:

```elixir
%Token{
  type: :identifier,
  value: "route",
  line: 5,       # 1-indexed line number
  column: 3      # 1-indexed column number
}
```

This enables:
- Precise error messages
- Source maps for debugging
- IDE integration (go to definition)

---

## Performance Optimizations

### Binary Pattern Matching

```elixir
# Efficient binary pattern matching
defp scan_word(<<c::utf8>> <> rest) when c in ?a..?z or c in ?A..?Z or c == ?_ do
  scan_word_continue(rest, <<c::utf8>>)
end

defp scan_word_continue(<<c::utf8>> <> rest, acc)
     when c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ do
  scan_word_continue(rest, acc <> <<c::utf8>>)
end

defp scan_word_continue(rest, acc) do
  {acc, rest}
end
```

### Keyword Lookup

```elixir
# Compile-time map for O(1) keyword lookup
@keywords Map.new([...])
```

---

## Testing

```elixir
defmodule Phronesis.LexerTest do
  use ExUnit.Case

  describe "keywords" do
    test "recognizes POLICY" do
      {:ok, tokens} = Phronesis.Lexer.tokenize("POLICY")
      assert [%{type: :policy}, %{type: :eof}] = tokens
    end
  end

  describe "literals" do
    test "scans integers" do
      {:ok, tokens} = Phronesis.Lexer.tokenize("42")
      assert [%{type: :integer, value: 42}, _] = tokens
    end

    test "scans floats" do
      {:ok, tokens} = Phronesis.Lexer.tokenize("3.14")
      assert [%{type: :float, value: 3.14}, _] = tokens
    end

    test "scans strings" do
      {:ok, tokens} = Phronesis.Lexer.tokenize(~s("hello"))
      assert [%{type: :string, value: "hello"}, _] = tokens
    end

    test "scans IP addresses" do
      {:ok, tokens} = Phronesis.Lexer.tokenize("192.0.2.1")
      assert [%{type: :ip_address, value: "192.0.2.1"}, _] = tokens
    end
  end

  describe "operators" do
    test "scans comparison operators" do
      {:ok, tokens} = Phronesis.Lexer.tokenize("== != < > <= >=")
      types = Enum.map(tokens, & &1.type)
      assert [:eq, :neq, :lt, :gt, :lte, :gte, :eof] = types
    end
  end

  describe "errors" do
    test "reports unterminated string" do
      {:error, {:unterminated_string, 1, 1}} =
        Phronesis.Lexer.tokenize(~s("unclosed))
    end
  end
end
```

---

## See Also

- [Architecture-Parser](Architecture-Parser.md) - Parser details
- [Syntax-Reference](Syntax-Reference.md) - Complete syntax
- [Reference-Grammar](Reference-Grammar.md) - Formal grammar
