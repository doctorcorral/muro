defmodule Muro.Parser do
  @moduledoc """
  Tiny .muro parser. Agda-looking: Π, λ, match, explicit types. Not Python-like.
  """

  def parse(src) when is_binary(src) do
    case parse_book(skip(src)) do
      {:ok, book, rest} ->
        rest = skip(rest)

        if rest == "" do
          {:ok, book}
        else
          {:error, "trailing input: #{String.slice(rest, 0, 40)}"}
        end

      other ->
        other
    end
  end

  defp parse_book(s), do: parse_book(s, [])

  defp parse_book(s, acc) do
    s = skip(s)

    if s == "" do
      {:ok, Enum.reverse(acc), ""}
    else
      case parse_def(s) do
        {:ok, d, rest} -> parse_book(rest, [d | acc])
        err -> err
      end
    end
  end

  defp parse_def(s) do
    with {:ok, rest} <- kw(s, "def"),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, mode, rest} <- parse_mode(skip(rest)),
         {:ok, ty, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), ":="),
         {:ok, body, rest} <- parse_term(skip(rest), 0) do
      {:ok, %{name: name, mode: mode, type: ty, body: body}, rest}
    end
  end

  defp parse_mode(<<"live", rest::binary>>), do: {:ok, :live, rest}
  defp parse_mode(<<"dead", rest::binary>>), do: {:ok, :dead, rest}
  defp parse_mode(_), do: {:error, "expected live or dead"}

  # Pratt-ish: apps are juxtaposition, arrows bind looser via Π/λ.
  defp parse_term(s, min_bp) do
    with {:ok, left, rest} <- parse_atom(skip(s)) do
      parse_infix(rest, left, min_bp)
    end
  end

  defp parse_infix(s, left, min_bp) do
    s0 = skip(s)

    cond do
      starts_atom?(s0) and min_bp <= 20 ->
        with {:ok, arg, rest} <- parse_atom(s0) do
          parse_infix(rest, {:app, left, arg}, min_bp)
        end

      true ->
        {:ok, left, s}
    end
  end

  defp starts_atom?(s) do
    case s do
      <<c, _::binary>> when c in ?a..?z or c in ?A..?Z or c == ?( or c == ?{ -> true
      <<"Type", _::binary>> -> true
      _ -> false
    end
  end

  defp parse_atom(s) do
    s = skip(s)

    cond do
      has_prefix?(s, "Type") -> {:ok, :typ, after_kw(s, "Type")}
      has_prefix?(s, "Nat") -> {:ok, :nat, after_kw(s, "Nat")}
      has_prefix?(s, "Unit") -> {:ok, :unit, after_kw(s, "Unit")}
      has_prefix?(s, "Empty") -> {:ok, :empty, after_kw(s, "Empty")}
      has_prefix?(s, "refl") -> {:ok, :rfl, after_kw(s, "refl")}
      has_prefix?(s, "tt") -> {:ok, :one, after_kw(s, "tt")}
      has_prefix?(s, "0") -> {:ok, :ze, after_kw(s, "0")}
      has_prefix?(s, "suc") -> parse_suc(s)
      has_prefix?(s, "Π") or has_prefix?(s, "Pi") -> parse_pi(s)
      has_prefix?(s, "λ") or has_prefix?(s, "lam") -> parse_lam(s)
      has_prefix?(s, "matchEmpty") -> parse_memp(s)
      has_prefix?(s, "match") -> parse_mnat(s)
      has_prefix?(s, "rewrite") -> parse_rwt(s)
      first_char(s) == ?{ -> parse_idt(s)
      first_char(s) == ?( ->
        with {:ok, rest} <- tok(s, "("),
             {:ok, t, rest} <- parse_term(skip(rest), 0),
             {:ok, rest} <- tok(skip(rest), ")") do
          {:ok, t, rest}
        end

      true ->
        case ident(s) do
          {:ok, name, rest} -> {:ok, {:var_or_def, name}, rest}
          _ -> {:error, "expected term at #{String.slice(s, 0, 30)}"}
        end
    end
    |> resolve_name()
  end

  defp resolve_name({:ok, {:var_or_def, name}, rest}) do
    # defs vs vars are distinguished at to_db / check time: unknown names
    # become {:def, name} if not bound. Parser emits {:var, name}; Check
    # treats free names as defs when converting.
    {:ok, {:var, name}, rest}
  end

  defp resolve_name(other), do: other

  defp parse_suc(s) do
    with {:ok, rest} <- kw(s, "suc"),
         {:ok, rest} <- tok(skip(rest), "("),
         {:ok, t, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), ")") do
      {:ok, {:su, t}, rest}
    end
  end

  defp parse_binder(s) do
    with {:ok, rest} <- tok(skip(s), "("),
         {:ok, q, rest} <- parse_qty(skip(rest)),
         {:ok, x, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, a, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), ")") do
      {:ok, {q, x, a}, rest}
    end
  end

  defp parse_qty(<<"+", rest::binary>>), do: {:ok, :reuse, rest}
  defp parse_qty(<<"-", rest::binary>>), do: {:ok, :erased, rest}
  defp parse_qty(s), do: {:ok, :affine, s}

  defp parse_pi(s) do
    rest = s |> skip() |> eat_kw(["Π", "Pi"])

    with {:ok, {q, x, a}, rest} <- parse_binder(rest),
         {:ok, rest} <- either_tok(skip(rest), ["→", "->"]),
         {:ok, b, rest} <- parse_term(skip(rest), 0) do
      {:ok, {:pi, q, a, x, b}, rest}
    end
  end

  defp parse_lam(s) do
    rest = s |> skip() |> eat_kw(["λ", "lam"])

    with {:ok, {q, x, a}, rest} <- parse_binder(rest),
         {:ok, rest} <- either_tok(skip(rest), ["→", "->"]),
         {:ok, t, rest} <- parse_term(skip(rest), 0) do
      {:ok, {:lam, q, a, x, t}, rest}
    end
  end

  defp parse_mnat(s) do
    with {:ok, rest} <- kw(s, "match"),
         {:ok, e, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- kw(skip(rest), "motive"),
         {:ok, rest} <- tok(skip(rest), "("),
         {:ok, rest} <- eat_lam(skip(rest)),
         {:ok, x, rest} <- ident(skip(rest)),
         {:ok, rest} <- either_tok(skip(rest), ["→", "->"]),
         {:ok, p, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), ")"),
         {:ok, rest} <- tok(skip(rest), "|"),
         {:ok, rest} <- kw(skip(rest), "0"),
         {:ok, rest} <- tok(skip(rest), "=>"),
         {:ok, z, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), "|"),
         {:ok, rest} <- kw(skip(rest), "suc"),
         {:ok, y, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), "=>"),
         {:ok, sc, rest} <- parse_term(skip(rest), 0) do
      {:ok, {:mnat, e, x, p, z, y, sc}, rest}
    end
  end

  defp parse_memp(s) do
    with {:ok, rest} <- kw(s, "matchEmpty"),
         {:ok, e, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- kw(skip(rest), "motive"),
         {:ok, rest} <- tok(skip(rest), "("),
         {:ok, rest} <- eat_lam(skip(rest)),
         {:ok, x, rest} <- ident(skip(rest)),
         {:ok, rest} <- either_tok(skip(rest), ["→", "->"]),
         {:ok, p, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), ")") do
      {:ok, {:memp, e, x, p}, rest}
    end
  end

  defp parse_rwt(s) do
    with {:ok, rest} <- kw(s, "rewrite"),
         {:ok, eq, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- kw(skip(rest), "motive"),
         {:ok, rest} <- tok(skip(rest), "("),
         {:ok, rest} <- eat_lam(skip(rest)),
         {:ok, x, rest} <- ident(skip(rest)),
         {:ok, rest} <- either_tok(skip(rest), ["→", "->"]),
         {:ok, p, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), ")"),
         {:ok, rest} <- kw(skip(rest), "in"),
         {:ok, t, rest} <- parse_term(skip(rest), 0) do
      {:ok, {:rwt, eq, x, p, t}, rest}
    end
  end

  defp parse_idt(s) do
    with {:ok, rest} <- tok(s, "{"),
         {:ok, a, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- either_tok(skip(rest), ["≡", "=="]),
         {:ok, b, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, ty, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), "}") do
      {:ok, {:idt, ty, a, b}, rest}
    end
  end

  defp eat_lam(s) do
    cond do
      has_prefix?(s, "λ") -> {:ok, after_kw(s, "λ")}
      has_prefix?(s, "lam") -> {:ok, after_kw(s, "lam")}
      true -> {:ok, s}
    end
  end

  defp eat_kw(s, [k | ks]) do
    if has_prefix?(s, k), do: after_kw(s, k), else: eat_kw(s, ks)
  end

  defp eat_kw(s, []), do: s

  # -- tokens ----------------------------------------------------------------

  defp skip(<<" ", r::binary>>), do: skip(r)
  defp skip(<<"\n", r::binary>>), do: skip(r)
  defp skip(<<"\t", r::binary>>), do: skip(r)
  defp skip(<<"\r", r::binary>>), do: skip(r)
  defp skip(<<"--", r::binary>>), do: skip(skip_line(r))
  defp skip(s), do: s

  defp skip_line(<<"\n", r::binary>>), do: r
  defp skip_line(<<_, r::binary>>), do: skip_line(r)
  defp skip_line(""), do: ""

  defp has_prefix?(s, kw), do: String.starts_with?(s, kw)

  defp after_kw(s, kw), do: String.slice(s, String.length(kw)..-1//1)

  defp kw(s, w) do
    s = skip(s)

    if has_prefix?(s, w) do
      rest = after_kw(s, w)

      if rest == "" or not ident_char?(String.first(rest)) do
        {:ok, rest}
      else
        {:error, "expected #{w}"}
      end
    else
      {:error, "expected #{w}"}
    end
  end

  defp tok(s, t) do
    s = skip(s)

    if has_prefix?(s, t), do: {:ok, after_kw(s, t)}, else: {:error, "expected #{t}"}
  end

  defp ident(s) do
    s = skip(s)

    case s do
      <<c, _::binary>> when c in ?a..?z or c in ?A..?Z or c == ?_ ->
        {n, rest} = take_ident(s, "")
        {:ok, n, rest}

      _ ->
        {:error, "expected identifier"}
    end
  end

  defp take_ident(<<c, r::binary>>, acc) when c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ do
    take_ident(r, acc <> <<c>>)
  end

  defp take_ident(s, acc), do: {acc, s}

  defp ident_char?(nil), do: false
  defp ident_char?(<<c>>), do: c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_
  defp ident_char?(s) when is_binary(s), do: ident_char?(String.first(s))

  defp first_char(<<c, _::binary>>), do: c
  defp first_char(_), do: nil

  defp either_tok(s, [t | ts]) do
    case tok(s, t) do
      {:ok, rest} -> {:ok, rest}
      _ -> either_tok(s, ts)
    end
  end

  defp either_tok(_, []), do: {:error, "expected token"}
end
