defmodule Muro.LexerTest do
  use ExUnit.Case, async: true

  alias Muro.{Lexer, MakeupLexer, Parser}

  test "a book covers the source and keeps parser tokens" do
    src = File.read!("examples/half_ok.muro")
    tokens = Lexer.tokenize(src)

    assert cover(src, tokens) == src
    assert {:ok, _} = Parser.parse(src)
    assert [:keyword] = kinds(src, tokens, "def") |> Enum.uniq()
    assert [:tag] = kinds(src, tokens, "run") |> Enum.uniq()
    assert [:tag] = kinds(src, tokens, "spec") |> Enum.uniq()
    assert [:tag] = kinds(src, tokens, "evidence") |> Enum.uniq()
    assert :builtin in Enum.map(tokens, &elem(&1, 0))
    assert :comment in Enum.map(tokens, &elem(&1, 0))
  end

  test "a fragment that is not a book still yields spans" do
    src = "(+ n : Nat) →"
    assert {:error, _} = Parser.parse(src)

    tokens = Lexer.tokenize(src)
    assert cover(src, tokens) == src

    assert tokens == [
             {:punctuation, 0, 1},
             {:operator, 1, 2},
             {:whitespace, 2, 3},
             {:name, 3, 4},
             {:whitespace, 4, 5},
             {:punctuation, 5, 6},
             {:whitespace, 6, 7},
             {:builtin, 7, 10},
             {:punctuation, 10, 11},
             {:whitespace, 11, 12},
             {:operator, 12, byte_size(src)}
           ]
  end

  test "keywords are not prefixes of names" do
    src = "default runtime internal inc matchEmpty"
    tokens = Lexer.tokenize(src)

    assert Enum.map(tokens, fn {kind, a, b} -> {kind, binary_part(src, a, b - a)} end) == [
             {:name, "default"},
             {:whitespace, " "},
             {:name, "runtime"},
             {:whitespace, " "},
             {:tag, "internal"},
             {:whitespace, " "},
             {:name, "inc"},
             {:whitespace, " "},
             {:keyword, "matchEmpty"}
           ]
  end

  test "operators and comments follow the parser" do
    src = "n := 0 -- a comment\n-> => :: == ~"
    tokens = Lexer.tokenize(src)

    assert Enum.map(tokens, fn {kind, a, b} -> {kind, binary_part(src, a, b - a)} end) == [
             {:name, "n"},
             {:whitespace, " "},
             {:operator, ":="},
             {:whitespace, " "},
             {:number, "0"},
             {:whitespace, " "},
             {:comment, "-- a comment"},
             {:whitespace, "\n"},
             {:operator, "->"},
             {:whitespace, " "},
             {:operator, "=>"},
             {:whitespace, " "},
             {:operator, "::"},
             {:whitespace, " "},
             {:operator, "=="},
             {:whitespace, " "},
             {:operator, "~"}
           ]
  end

  test "unicode binders and an unknown codepoint are covered" do
    src = "λ (n : Nat) → @@"
    tokens = Lexer.tokenize(src)
    assert cover(src, tokens) == src
    lam = byte_size("λ")
    assert {:keyword, 0, ^lam} = hd(tokens)

    {kind, start, stop} = List.last(tokens)
    assert kind == :text
    assert binary_part(src, start, stop - start) == "@"
  end

  test "an apostrophe stays inside a name" do
    src = "n'"
    assert Lexer.tokenize(src) == [{:name, 0, 2}]
  end

  test "nil is one builtin" do
    assert Lexer.tokenize("[]") == [{:builtin, 0, 2}]
  end

  test "makeup tags are the slices of the source" do
    src = "def plus : run Nat := 0"
    tagged = MakeupLexer.lex(src)

    assert Enum.map_join(tagged, fn {_tag, _meta, text} -> text end) == src

    assert Enum.map(tagged, fn {tag, _meta, text} -> {tag, IO.iodata_to_binary(text)} end) == [
             {:keyword, "def"},
             {:whitespace, " "},
             {:name, "plus"},
             {:whitespace, " "},
             {:punctuation, ":"},
             {:whitespace, " "},
             {:keyword_type, "run"},
             {:whitespace, " "},
             {:name_builtin, "Nat"},
             {:whitespace, " "},
             {:operator, ":="},
             {:whitespace, " "},
             {:number_integer, "0"}
           ]
  end

  test "muro is registered with Makeup" do
    assert {:ok, {Muro.MakeupLexer, []}} = Makeup.Registry.fetch_lexer_by_name("muro")
    assert {:ok, {Muro.MakeupLexer, []}} = Makeup.Registry.fetch_lexer_by_extension("muro")

    html = Makeup.highlight_inner_html("def plus : run", lexer: "muro")
    assert html =~ ~s(<span class="k">def</span>)
    assert html =~ ~s(<span class="kt">run</span>)
    assert html =~ ~s(<span class="n">plus</span>)
  end

  defp cover(src, tokens) do
    Enum.map_join(tokens, fn {_kind, start, stop} -> binary_part(src, start, stop - start) end)
  end

  defp kinds(src, tokens, text) do
    for {kind, start, stop} <- tokens, binary_part(src, start, stop - start) == text, do: kind
  end
end
