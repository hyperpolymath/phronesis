# SPDX-License-Identifier: PMPL-1.0-or-later
# SPDX-FileCopyrightText: 2025 Phronesis Contributors

defmodule Phronesis.DocGenerator do
  @moduledoc """
  Documentation generator for Phronesis policies.

  Extracts documentation from policy files and generates user-friendly
  documentation in multiple formats (HTML, Markdown, PDF).

  ## Features

  - Extract policy documentation from comments
  - Generate API documentation for constants and policies
  - Create module documentation
  - Generate policy catalogs
  - Cross-reference policies and constants
  - Example extraction
  - Generate indices and search functionality

  ## Usage

      # Generate docs for a single file
      {:ok, docs} = DocGenerator.generate_file("policy.phr")

      # Generate docs for entire project
      {:ok, docs} = DocGenerator.generate_project("./policies")

      # Export to HTML
      DocGenerator.export_html(docs, "output/")

      # Export to Markdown
      DocGenerator.export_markdown(docs, "docs/")
  """

  alias Phronesis.{Lexer, Parser}

  defstruct [
    :project_name,
    :version,
    :files,
    :constants,
    :policies,
    :modules,
    :examples,
    :index
  ]

  @type doc_entry :: %{
          name: String.t(),
          description: String.t(),
          signature: String.t(),
          examples: [String.t()],
          metadata: map(),
          file: String.t(),
          line: integer()
        }

  @type t :: %__MODULE__{
          project_name: String.t(),
          version: String.t(),
          files: [String.t()],
          constants: [doc_entry()],
          policies: [doc_entry()],
          modules: %{String.t() => [doc_entry()]},
          examples: [doc_entry()],
          index: %{String.t() => doc_entry()}
        }

  ## Generation

  @doc """
  Generate documentation for a single file.
  """
  def generate_file(file_path) do
    with {:ok, source} <- File.read(file_path),
         {:ok, tokens} <- Lexer.tokenize(source),
         {:ok, ast} <- Parser.parse(tokens) do
      docs = extract_documentation(ast, source, file_path)
      {:ok, docs}
    else
      {:error, reason} -> {:error, reason}
    end
  end

  @doc """
  Generate documentation for an entire project.
  """
  def generate_project(directory, opts \\ []) do
    # Check if directory exists
    if not File.dir?(directory) do
      {:error, :enoent}
    else
      do_generate_project(directory, opts)
    end
  end

  defp do_generate_project(directory, opts) do

    project_name = Keyword.get(opts, :name, Path.basename(directory))
    version = Keyword.get(opts, :version, "0.1.0")

    files =
      Path.wildcard(Path.join(directory, "**/*.phr"))
      |> Enum.sort()

    all_docs =
      Enum.reduce(files, [], fn file, acc ->
        case generate_file(file) do
          {:ok, docs} -> acc ++ [docs]
          {:error, _} -> acc
        end
      end)

    project_docs = %__MODULE__{
      project_name: project_name,
      version: version,
      files: files,
      constants: Enum.flat_map(all_docs, & &1.constants),
      policies: Enum.flat_map(all_docs, & &1.policies),
      modules: merge_modules(all_docs),
      examples: Enum.flat_map(all_docs, & &1.examples),
      index: build_index(all_docs)
    }

    {:ok, project_docs}
  end

  ## Documentation Extraction

  defp extract_documentation(ast, source, file_path) do
    lines = String.split(source, "\n")
    base_name = Path.basename(file_path, ".phr")

    %__MODULE__{
      project_name: base_name,
      version: "0.1.0",
      files: [file_path],
      constants: extract_constants(ast, lines, file_path),
      policies: extract_policies(ast, lines, file_path),
      modules: extract_modules(ast, lines),
      examples: extract_examples(source, file_path),
      index: %{}
    }
  end

  defp extract_constants(ast, lines, file_path) do
    ast
    |> Enum.filter(&match?({:const, _, _}, &1))
    |> Enum.map(fn {:const, name, value} ->
      # Try to find line number from the value if it's a structure
      line = extract_line_from_value(value) || 1
      doc_comment = extract_comment(lines, line)

      %{
        name: to_string(name),
        description: doc_comment,
        signature: "CONST #{name} = #{format_value(value)}",
        value: value,
        examples: [],
        metadata: %{},
        file: file_path,
        line: line
      }
    end)
  end

  defp extract_line_from_value({:literal, _type, _value, meta}) when is_map(meta), do: meta[:line]
  defp extract_line_from_value({:literal, _type, _value}), do: nil
  defp extract_line_from_value(_), do: nil

  defp format_value({:literal, _, value}), do: inspect(value)
  defp format_value({:literal, _, value, _meta}), do: inspect(value)
  defp format_value(value), do: inspect(value)

  defp extract_policies(ast, lines, file_path) do
    ast
    |> Enum.filter(&match?({:policy, _, _, _, _}, &1))
    |> Enum.map(fn {:policy, name, condition, action, meta} ->
      line = meta[:line] || 1
      doc_comment = extract_comment(lines, line)

      %{
        name: to_string(name),
        description: doc_comment,
        signature: format_policy_signature(name, condition, action, meta),
        condition: condition,
        action: action,
        examples: extract_policy_examples(doc_comment),
        metadata: meta,
        file: file_path,
        line: line
      }
    end)
  end

  defp extract_modules(ast, _lines) do
    ast
    |> Enum.filter(&match?({:import, _, _}, &1))
    |> Enum.map(fn {:import, module, _meta} -> module end)
    |> Enum.uniq()
    |> Enum.into(%{}, fn module -> {module, []} end)
  end

  defp extract_examples(source, file_path) do
    # Extract code blocks from comments marked as examples
    lines = String.split(source, "\n")

    lines
    |> Enum.with_index(1)
    |> Enum.reduce({[], false, []}, fn {line, line_num}, {examples, in_example, current} ->
      cond do
        String.contains?(line, "# Example:") or String.contains?(line, "# EXAMPLE:") ->
          {examples, true, []}

        in_example and String.starts_with?(line, "#") ->
          code = String.trim_leading(line, "# ")
          {examples, true, current ++ [code]}

        in_example and not String.starts_with?(line, "#") ->
          example = %{
            code: Enum.join(current, "\n"),
            file: file_path,
            line: line_num - length(current)
          }
          {examples ++ [example], false, []}

        true ->
          {examples, false, current}
      end
    end)
    |> elem(0)
  end

  defp extract_comment(lines, target_line) do
    # Look backwards from target line to find doc comments
    comments =
      (target_line - 1)..1
      |> Enum.reduce_while([], fn line_idx, acc ->
        line = Enum.at(lines, line_idx - 1, "")

        cond do
          String.starts_with?(String.trim(line), "#") and not String.contains?(line, "SPDX") ->
            comment = String.trim_leading(line, "#") |> String.trim()
            {:cont, [comment | acc]}

          String.trim(line) == "" ->
            {:cont, acc}

          true ->
            {:halt, acc}
        end
      end)

    Enum.join(comments, " ")
  end

  defp extract_policy_examples(doc_comment) do
    # Extract example usage from doc comments
    if String.contains?(doc_comment, "Example:") do
      doc_comment
      |> String.split("Example:")
      |> List.last()
      |> String.trim()
      |> List.wrap()
    else
      []
    end
  end

  defp format_policy_signature(name, _condition, _action, meta) do
    priority = meta[:priority] || "N/A"
    expires = meta[:expires] || "never"
    created_by = meta[:created_by] || "unknown"

    """
    POLICY #{name}:
      PRIORITY: #{priority}
      EXPIRES: #{expires}
      CREATED_BY: #{created_by}
    """
    |> String.trim()
  end

  ## Index Building

  defp build_index(all_docs) do
    all_docs
    |> Enum.flat_map(fn docs ->
      (docs.constants || []) ++ (docs.policies || [])
    end)
    |> Enum.into(%{}, fn entry -> {entry.name, entry} end)
  end

  defp merge_modules(all_docs) do
    all_docs
    |> Enum.flat_map(fn docs -> Map.to_list(docs.modules || %{}) end)
    |> Enum.group_by(&elem(&1, 0), &elem(&1, 1))
    |> Enum.into(%{}, fn {module, values} -> {module, List.flatten(values)} end)
  end

  ## HTML Export

  @doc """
  Export documentation as HTML.
  """
  def export_html(docs, output_dir) do
    File.mkdir_p!(output_dir)

    # Generate index page
    index_html = generate_index_html(docs)
    File.write!(Path.join(output_dir, "index.html"), index_html)

    # Generate constants page
    constants_html = generate_constants_html(docs)
    File.write!(Path.join(output_dir, "constants.html"), constants_html)

    # Generate policies page
    policies_html = generate_policies_html(docs)
    File.write!(Path.join(output_dir, "policies.html"), policies_html)

    # Generate CSS
    css = generate_css()
    File.write!(Path.join(output_dir, "styles.css"), css)

    {:ok, output_dir}
  end

  defp generate_index_html(docs) do
    """
    <!DOCTYPE html>
    <html>
    <head>
      <title>#{docs.project_name} Documentation</title>
      <link rel="stylesheet" href="styles.css">
    </head>
    <body>
      <nav>
        <h1>#{docs.project_name}</h1>
        <p class="version">Version #{docs.version}</p>
        <ul>
          <li><a href="index.html">Overview</a></li>
          <li><a href="constants.html">Constants (#{length(docs.constants)})</a></li>
          <li><a href="policies.html">Policies (#{length(docs.policies)})</a></li>
        </ul>
      </nav>

      <main>
        <h2>Project Overview</h2>
        <div class="stats">
          <div class="stat">
            <span class="label">Files:</span>
            <span class="value">#{length(docs.files)}</span>
          </div>
          <div class="stat">
            <span class="label">Constants:</span>
            <span class="value">#{length(docs.constants)}</span>
          </div>
          <div class="stat">
            <span class="label">Policies:</span>
            <span class="value">#{length(docs.policies)}</span>
          </div>
          <div class="stat">
            <span class="label">Modules:</span>
            <span class="value">#{map_size(docs.modules)}</span>
          </div>
        </div>

        <h3>Files</h3>
        <ul class="file-list">
          #{Enum.map_join(docs.files, "\n", &"<li><code>#{Path.basename(&1)}</code></li>")}
        </ul>

        #{if length(docs.examples) > 0 do
          """
          <h3>Examples</h3>
          #{Enum.map_join(docs.examples, "\n", &example_html/1)}
          """
        else
          ""
        end}
      </main>
    </body>
    </html>
    """
  end

  defp generate_constants_html(docs) do
    """
    <!DOCTYPE html>
    <html>
    <head>
      <title>Constants - #{docs.project_name}</title>
      <link rel="stylesheet" href="styles.css">
    </head>
    <body>
      <nav>
        <h1>#{docs.project_name}</h1>
        <ul>
          <li><a href="index.html">Overview</a></li>
          <li><a href="constants.html" class="active">Constants</a></li>
          <li><a href="policies.html">Policies</a></li>
        </ul>
      </nav>

      <main>
        <h2>Constants</h2>
        #{Enum.map_join(docs.constants, "\n\n", &constant_html/1)}
      </main>
    </body>
    </html>
    """
  end

  defp generate_policies_html(docs) do
    """
    <!DOCTYPE html>
    <html>
    <head>
      <title>Policies - #{docs.project_name}</title>
      <link rel="stylesheet" href="styles.css">
    </head>
    <body>
      <nav>
        <h1>#{docs.project_name}</h1>
        <ul>
          <li><a href="index.html">Overview</a></li>
          <li><a href="constants.html">Constants</a></li>
          <li><a href="policies.html" class="active">Policies</a></li>
        </ul>
      </nav>

      <main>
        <h2>Policies</h2>
        #{Enum.map_join(docs.policies, "\n\n", &policy_html/1)}
      </main>
    </body>
    </html>
    """
  end

  defp constant_html(const) do
    """
    <div class="doc-entry" id="#{const.name}">
      <h3>#{const.name}</h3>
      <div class="signature">
        <code>#{escape_html(const.signature)}</code>
      </div>
      #{if const.description != "" do
        "<p class=\"description\">#{escape_html(const.description)}</p>"
      else
        ""
      end}
      <div class="metadata">
        <span class="file">#{Path.basename(const.file)}:#{const.line}</span>
      </div>
    </div>
    """
  end

  defp policy_html(policy) do
    """
    <div class="doc-entry" id="#{policy.name}">
      <h3>#{policy.name}</h3>
      <div class="signature">
        <pre><code>#{escape_html(policy.signature)}</code></pre>
      </div>
      #{if policy.description != "" do
        "<p class=\"description\">#{escape_html(policy.description)}</p>"
      else
        ""
      end}
      #{if length(policy.examples) > 0 do
        """
        <div class="examples">
          <h4>Examples</h4>
          #{Enum.map_join(policy.examples, "\n", fn ex -> "<pre><code>#{escape_html(ex)}</code></pre>" end)}
        </div>
        """
      else
        ""
      end}
      <div class="metadata">
        <span class="file">#{Path.basename(policy.file)}:#{policy.line}</span>
        <span class="priority">Priority: #{policy.metadata[:priority] || "N/A"}</span>
      </div>
    </div>
    """
  end

  defp example_html(example) do
    """
    <div class="example">
      <pre><code>#{escape_html(example.code)}</code></pre>
      <div class="example-source">#{Path.basename(example.file)}:#{example.line}</div>
    </div>
    """
  end

  defp generate_css do
    """
    body {
      font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif;
      margin: 0;
      padding: 0;
      background: #1e1e1e;
      color: #d4d4d4;
      display: flex;
    }

    nav {
      width: 250px;
      background: #252526;
      padding: 20px;
      min-height: 100vh;
      border-right: 1px solid #3e3e42;
    }

    nav h1 {
      color: #4ec9b0;
      margin: 0 0 5px 0;
      font-size: 24px;
    }

    nav .version {
      color: #858585;
      margin: 0 0 20px 0;
    }

    nav ul {
      list-style: none;
      padding: 0;
    }

    nav li {
      margin: 10px 0;
    }

    nav a {
      color: #9cdcfe;
      text-decoration: none;
    }

    nav a:hover, nav a.active {
      color: #4ec9b0;
    }

    main {
      flex: 1;
      padding: 40px;
      max-width: 1200px;
    }

    h2, h3, h4 {
      color: #4ec9b0;
    }

    .stats {
      display: flex;
      gap: 30px;
      margin: 20px 0;
      background: #2d2d30;
      padding: 20px;
      border-radius: 5px;
    }

    .stat .label {
      color: #9cdcfe;
      margin-right: 10px;
    }

    .stat .value {
      color: #ce9178;
      font-weight: bold;
      font-size: 20px;
    }

    .doc-entry {
      background: #2d2d30;
      padding: 20px;
      margin: 20px 0;
      border-left: 3px solid #4ec9b0;
      border-radius: 3px;
    }

    .doc-entry h3 {
      margin-top: 0;
    }

    .signature {
      background: #1e1e1e;
      padding: 15px;
      border-radius: 3px;
      margin: 10px 0;
    }

    .signature code, .signature pre {
      color: #ce9178;
      font-family: 'Consolas', 'Courier New', monospace;
    }

    .description {
      color: #d4d4d4;
      line-height: 1.6;
    }

    .metadata {
      color: #858585;
      font-size: 14px;
      margin-top: 15px;
      display: flex;
      gap: 20px;
    }

    .file-list {
      list-style: none;
      padding: 0;
    }

    .file-list li {
      background: #2d2d30;
      padding: 10px;
      margin: 5px 0;
      border-radius: 3px;
    }

    .file-list code {
      color: #ce9178;
    }

    .examples {
      margin: 15px 0;
    }

    .examples h4 {
      margin-bottom: 10px;
    }

    .examples pre {
      background: #1e1e1e;
      padding: 15px;
      border-radius: 3px;
      overflow-x: auto;
    }

    .example {
      background: #2d2d30;
      padding: 15px;
      margin: 10px 0;
      border-radius: 3px;
    }

    .example-source {
      color: #858585;
      font-size: 12px;
      margin-top: 10px;
    }

    code {
      font-family: 'Consolas', 'Courier New', monospace;
    }

    pre {
      margin: 0;
      white-space: pre-wrap;
    }
    """
  end

  ## Markdown Export

  @doc """
  Export documentation as Markdown.
  """
  def export_markdown(docs, output_dir) do
    File.mkdir_p!(output_dir)

    # Generate index
    index_md = generate_index_markdown(docs)
    File.write!(Path.join(output_dir, "README.md"), index_md)

    # Generate constants doc
    if length(docs.constants) > 0 do
      constants_md = generate_constants_markdown(docs)
      File.write!(Path.join(output_dir, "CONSTANTS.md"), constants_md)
    end

    # Generate policies doc
    if length(docs.policies) > 0 do
      policies_md = generate_policies_markdown(docs)
      File.write!(Path.join(output_dir, "POLICIES.md"), policies_md)
    end

    {:ok, output_dir}
  end

  defp generate_index_markdown(docs) do
    """
    # #{docs.project_name} Documentation

    **Version:** #{docs.version}

    ## Overview

    - **Files:** #{length(docs.files)}
    - **Constants:** #{length(docs.constants)}
    - **Policies:** #{length(docs.policies)}
    - **Modules:** #{map_size(docs.modules)}

    ## Contents

    - [Constants](CONSTANTS.md) - #{length(docs.constants)} constant definitions
    - [Policies](POLICIES.md) - #{length(docs.policies)} policy definitions

    ## Files

    #{Enum.map_join(docs.files, "\n", fn file -> "- `#{Path.basename(file)}`" end)}
    """
  end

  defp generate_constants_markdown(docs) do
    """
    # Constants

    #{Enum.map_join(docs.constants, "\n\n---\n\n", &constant_markdown/1)}
    """
  end

  defp generate_policies_markdown(docs) do
    """
    # Policies

    #{Enum.map_join(docs.policies, "\n\n---\n\n", &policy_markdown/1)}
    """
  end

  defp constant_markdown(const) do
    """
    ## #{const.name}

    ```phronesis
    #{const.signature}
    ```

    #{if const.description != "", do: const.description, else: "*No description*"}

    **Source:** `#{Path.basename(const.file)}:#{const.line}`
    """
  end

  defp policy_markdown(policy) do
    """
    ## #{policy.name}

    ```phronesis
    #{policy.signature}
    ```

    #{if policy.description != "", do: policy.description, else: "*No description*"}

    #{if length(policy.examples) > 0 do
      """
      ### Examples

      #{Enum.map_join(policy.examples, "\n\n", fn ex -> "```phronesis\n#{ex}\n```" end)}
      """
    else
      ""
    end}

    **Source:** `#{Path.basename(policy.file)}:#{policy.line}`
    **Priority:** #{policy.metadata[:priority] || "N/A"}
    """
  end

  ## Helpers

  defp escape_html(text) do
    text
    |> String.replace("&", "&amp;")
    |> String.replace("<", "&lt;")
    |> String.replace(">", "&gt;")
    |> String.replace("\"", "&quot;")
    |> String.replace("'", "&#39;")
  end
end
