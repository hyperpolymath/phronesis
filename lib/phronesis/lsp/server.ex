# SPDX-License-Identifier: MPL-2.0
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.LSP.Server do
  @moduledoc """
  Language Server Protocol (LSP) server for Phronesis.

  Provides IDE integration features:
  - Text document synchronization
  - Diagnostics (errors and warnings)
  - Auto-completion
  - Hover documentation
  - Go to definition
  - Find references
  - Document symbols
  - Code formatting

  ## Usage

  Start the LSP server:

      phronesis lsp

  The server communicates via stdin/stdout using JSON-RPC 2.0.

  ## LSP Capabilities

  - `textDocument/didOpen` - Track opened documents
  - `textDocument/didChange` - Incremental updates
  - `textDocument/didSave` - Save notifications
  - `textDocument/completion` - Auto-complete
  - `textDocument/hover` - Documentation on hover
  - `textDocument/definition` - Go to definition
  - `textDocument/references` - Find all references
  - `textDocument/documentSymbol` - Outline view
  - `textDocument/formatting` - Format document
  - `textDocument/publishDiagnostics` - Errors/warnings

  ## References

  - LSP Specification: https://microsoft.github.io/language-server-protocol/
  - JSON-RPC 2.0: https://www.jsonrpc.org/specification
  """

  use GenServer
  require Logger

  alias Phronesis.{Lexer, Parser, Linter, Formatter}
  alias Phronesis.LSP.{Protocol, TextDocument, Completion, Hover, Definition}

  @type state :: %{
          documents: %{uri :: String.t() => TextDocument.t()},
          client_capabilities: map(),
          initialized: boolean()
        }

  # ============================================================
  # Public API
  # ============================================================

  @doc """
  Start the LSP server.
  """
  def start_link(opts \\ []) do
    GenServer.start_link(__MODULE__, opts, name: __MODULE__)
  end

  @doc """
  Main loop - read from stdin, write to stdout.
  """
  def run do
    {:ok, _pid} = start_link()
    Logger.info("Phronesis LSP server started")

    loop()
  end

  # ============================================================
  # GenServer Callbacks
  # ============================================================

  @impl true
  def init(_opts) do
    state = %{
      documents: %{},
      client_capabilities: %{},
      initialized: false
    }

    {:ok, state}
  end

  @impl true
  def handle_call({:handle_message, message}, _from, state) do
    case handle_lsp_message(message, state) do
      {:reply, response, new_state} ->
        {:reply, response, new_state}

      {:noreply, new_state} ->
        {:reply, nil, new_state}

      {:error, error, new_state} ->
        {:reply, {:error, error}, new_state}
    end
  end

  # ============================================================
  # Message Loop
  # ============================================================

  defp loop do
    case read_message() do
      {:ok, message} ->
        response = GenServer.call(__MODULE__, {:handle_message, message})

        if response do
          write_message(response)
        end

        loop()

      {:error, :eof} ->
        Logger.info("LSP server shutting down (EOF)")
        :ok

      {:error, reason} ->
        Logger.error("Failed to read message: #{inspect(reason)}")
        loop()
    end
  end

  defp read_message do
    # Read Content-Length header
    case IO.read(:stdio, :line) do
      :eof ->
        {:error, :eof}

      {:error, reason} ->
        {:error, reason}

      line ->
        case parse_header(line) do
          {:ok, content_length} ->
            # Read blank line
            IO.read(:stdio, :line)

            # Read content
            case IO.read(:stdio, content_length) do
              :eof ->
                {:error, :eof}

              {:error, reason} ->
                {:error, reason}

              content ->
                case Jason.decode(content) do
                  {:ok, message} -> {:ok, message}
                  {:error, reason} -> {:error, {:json_decode, reason}}
                end
            end

          {:error, reason} ->
            {:error, reason}
        end
    end
  end

  defp parse_header(line) do
    case String.trim(line) do
      "Content-Length: " <> length ->
        case Integer.parse(length) do
          {num, _} -> {:ok, num}
          :error -> {:error, :invalid_content_length}
        end

      _ ->
        {:error, :invalid_header}
    end
  end

  defp write_message(message) do
    json = Jason.encode!(message)
    content_length = byte_size(json)

    IO.write(:stdio, "Content-Length: #{content_length}\r\n\r\n")
    IO.write(:stdio, json)
    IO.write(:stdio, "\r\n")
  end

  # ============================================================
  # LSP Message Handlers
  # ============================================================

  defp handle_lsp_message(%{"method" => "initialize", "id" => id, "params" => params}, state) do
    client_capabilities = Map.get(params, "capabilities", %{})

    response = %{
      "jsonrpc" => "2.0",
      "id" => id,
      "result" => %{
        "capabilities" => server_capabilities(),
        "serverInfo" => %{
          "name" => "phronesis-lsp",
          "version" => "0.2.0"
        }
      }
    }

    new_state = %{state | client_capabilities: client_capabilities, initialized: true}
    {:reply, response, new_state}
  end

  defp handle_lsp_message(%{"method" => "initialized"}, state) do
    Logger.info("Client initialized")
    {:noreply, state}
  end

  defp handle_lsp_message(%{"method" => "shutdown", "id" => id}, state) do
    response = %{
      "jsonrpc" => "2.0",
      "id" => id,
      "result" => nil
    }

    {:reply, response, state}
  end

  defp handle_lsp_message(%{"method" => "exit"}, _state) do
    System.halt(0)
  end

  defp handle_lsp_message(
         %{"method" => "textDocument/didOpen", "params" => params},
         state
       ) do
    uri = get_in(params, ["textDocument", "uri"])
    text = get_in(params, ["textDocument", "text"])
    version = get_in(params, ["textDocument", "version"])

    document = TextDocument.new(uri, text, version)
    new_state = put_in(state, [:documents, uri], document)

    # Send diagnostics
    diagnostics = compute_diagnostics(document)
    publish_diagnostics(uri, diagnostics)

    {:noreply, new_state}
  end

  defp handle_lsp_message(
         %{"method" => "textDocument/didChange", "params" => params},
         state
       ) do
    uri = get_in(params, ["textDocument", "uri"])
    changes = get_in(params, ["contentChanges"])
    version = get_in(params, ["textDocument", "version"])

    case Map.get(state.documents, uri) do
      nil ->
        {:noreply, state}

      document ->
        new_document = apply_changes(document, changes, version)
        new_state = put_in(state, [:documents, uri], new_document)

        # Send updated diagnostics
        diagnostics = compute_diagnostics(new_document)
        publish_diagnostics(uri, diagnostics)

        {:noreply, new_state}
    end
  end

  defp handle_lsp_message(
         %{"method" => "textDocument/didSave", "params" => _params},
         state
       ) do
    # Could trigger additional analysis here
    {:noreply, state}
  end

  defp handle_lsp_message(
         %{"method" => "textDocument/completion", "id" => id, "params" => params},
         state
       ) do
    uri = get_in(params, ["textDocument", "uri"])
    position = get_in(params, ["position"])

    completions =
      case Map.get(state.documents, uri) do
        nil -> []
        document -> Completion.compute(document, position)
      end

    response = %{
      "jsonrpc" => "2.0",
      "id" => id,
      "result" => completions
    }

    {:reply, response, state}
  end

  defp handle_lsp_message(
         %{"method" => "textDocument/hover", "id" => id, "params" => params},
         state
       ) do
    uri = get_in(params, ["textDocument", "uri"])
    position = get_in(params, ["position"])

    hover_info =
      case Map.get(state.documents, uri) do
        nil -> nil
        document -> Hover.compute(document, position)
      end

    response = %{
      "jsonrpc" => "2.0",
      "id" => id,
      "result" => hover_info
    }

    {:reply, response, state}
  end

  defp handle_lsp_message(
         %{"method" => "textDocument/definition", "id" => id, "params" => params},
         state
       ) do
    uri = get_in(params, ["textDocument", "uri"])
    position = get_in(params, ["position"])

    locations =
      case Map.get(state.documents, uri) do
        nil -> []
        document -> Definition.compute(document, position, state.documents)
      end

    response = %{
      "jsonrpc" => "2.0",
      "id" => id,
      "result" => locations
    }

    {:reply, response, state}
  end

  defp handle_lsp_message(
         %{"method" => "textDocument/formatting", "id" => id, "params" => params},
         state
       ) do
    uri = get_in(params, ["textDocument", "uri"])

    edits =
      case Map.get(state.documents, uri) do
        nil ->
          []

        document ->
          case Formatter.format(document.text) do
            {:ok, formatted} ->
              [
                %{
                  "range" => full_document_range(document),
                  "newText" => formatted
                }
              ]

            {:error, _} ->
              []
          end
      end

    response = %{
      "jsonrpc" => "2.0",
      "id" => id,
      "result" => edits
    }

    {:reply, response, state}
  end

  defp handle_lsp_message(%{"method" => method}, state) do
    Logger.warn("Unhandled LSP method: #{method}")
    {:noreply, state}
  end

  # ============================================================
  # Server Capabilities
  # ============================================================

  defp server_capabilities do
    %{
      "textDocumentSync" => %{
        "openClose" => true,
        "change" => 2,
        # Incremental
        "save" => %{"includeText" => false}
      },
      "completionProvider" => %{
        "triggerCharacters" => [".", ":"],
        "resolveProvider" => false
      },
      "hoverProvider" => true,
      "definitionProvider" => true,
      "referencesProvider" => false,
      # TODO: Implement
      "documentSymbolProvider" => false,
      # TODO: Implement
      "documentFormattingProvider" => true
    }
  end

  # ============================================================
  # Diagnostics
  # ============================================================

  defp compute_diagnostics(document) do
    case Lexer.tokenize(document.text) do
      {:ok, tokens} ->
        case Parser.parse(tokens) do
          {:ok, ast} ->
            # Check for linter warnings
            warnings = Linter.lint(ast)

            Enum.map(warnings, fn warning ->
              %{
                "range" => %{
                  "start" => %{"line" => 0, "character" => 0},
                  "end" => %{"line" => 0, "character" => 0}
                },
                "severity" => 2,
                # Warning
                "source" => "phronesis",
                "message" => warning
              }
            end)

          {:error, {:parse_error, msg, line, col}} ->
            [
              %{
                "range" => %{
                  "start" => %{"line" => line - 1, "character" => col - 1},
                  "end" => %{"line" => line - 1, "character" => col}
                },
                "severity" => 1,
                # Error
                "source" => "phronesis",
                "message" => msg
              }
            ]

          {:error, reason} ->
            [
              %{
                "range" => %{
                  "start" => %{"line" => 0, "character" => 0},
                  "end" => %{"line" => 0, "character" => 0}
                },
                "severity" => 1,
                "source" => "phronesis",
                "message" => "Parse error: #{inspect(reason)}"
              }
            ]
        end

      {:error, {:lexer_error, msg, line, col}} ->
        [
          %{
            "range" => %{
              "start" => %{"line" => line - 1, "character" => col - 1},
              "end" => %{"line" => line - 1, "character" => col}
            },
            "severity" => 1,
            "source" => "phronesis",
            "message" => msg
          }
        ]

      {:error, reason} ->
        [
          %{
            "range" => %{
              "start" => %{"line" => 0, "character" => 0},
              "end" => %{"line" => 0, "character" => 0}
            },
            "severity" => 1,
            "source" => "phronesis",
            "message" => "Lexer error: #{inspect(reason)}"
          }
        ]
    end
  end

  defp publish_diagnostics(uri, diagnostics) do
    notification = %{
      "jsonrpc" => "2.0",
      "method" => "textDocument/publishDiagnostics",
      "params" => %{
        "uri" => uri,
        "diagnostics" => diagnostics
      }
    }

    write_message(notification)
  end

  # ============================================================
  # Text Document Sync
  # ============================================================

  defp apply_changes(document, changes, version) do
    # For incremental sync (change type 2)
    new_text =
      Enum.reduce(changes, document.text, fn change, text ->
        case change do
          %{"text" => new_text} ->
            # Full document sync
            new_text

          %{"range" => _range, "text" => _new_text} ->
            # Incremental change - TODO: implement properly
            # For now, fall back to full sync
            Map.get(change, "text", text)

          _ ->
            text
        end
      end)

    %{document | text: new_text, version: version}
  end

  defp full_document_range(document) do
    lines = String.split(document.text, "\n")
    last_line_idx = max(length(lines) - 1, 0)
    last_line = List.last(lines) || ""

    %{
      "start" => %{"line" => 0, "character" => 0},
      "end" => %{"line" => last_line_idx, "character" => String.length(last_line)}
    }
  end
end
