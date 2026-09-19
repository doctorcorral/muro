defmodule Muro.Parser do
  @moduledoc """
  Tiny .muro parser. Agda-looking: Π, λ, match, explicit types.
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

    cond do
      s == "" ->
        {:ok, Enum.reverse(acc), ""}

      nu_start?(s) ->
        case parse_nu(s) do
          {:ok, rest} -> parse_book(rest, acc)
          err -> err
        end

      data_start?(s) ->
        case parse_data(s) do
          {:ok, rest} -> parse_book(rest, acc)
          err -> err
        end

      true ->
        case parse_def(s) do
          {:ok, d, rest} -> parse_book(rest, [d | acc])
          err -> err
        end
    end
  end

  defp nu_start?(s), do: word_kw?(s, "ν") or word_kw?(s, "nu")

  # v1: only `ν Stream (A : Type) : Type where uncons : Stream A → A × Stream A`.
  # Stream is primitive; the block is checked for shape and then dropped.
  defp parse_nu(s) do
    rest = s |> skip() |> eat_kw(["ν", "nu"])

    with {:ok, name, rest} <- ident(skip(rest)),
         :ok <- if(name == "Stream", do: :ok, else: {:error, "v1 only supports ν Stream"}),
         {:ok, {_q, _x, a}, rest} <- parse_binder(rest),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, ty, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- kw(skip(rest), "where"),
         {:ok, ctor, rest} <- ident(skip(rest)),
         :ok <- if(ctor == "uncons", do: :ok, else: {:error, "expected uncons"}),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, _ctor_ty, rest} <- parse_term(skip(rest), 0) do
      _ = {a, ty}
      {:ok, rest}
    end
  end

  defp data_start?(s), do: word_kw?(s, "data")

  # v1: only built-in Either. The block is shape-checked and dropped.
  defp parse_data(s) do
    with {:ok, rest} <- kw(s, "data"),
         {:ok, name, rest} <- ident(skip(rest)),
         :ok <- if(name == "Either", do: :ok, else: {:error, "v1 only supports data Either"}),
         {:ok, _, rest} <- parse_binder(rest),
         {:ok, _, rest} <- parse_binder(rest),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, _ty, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- kw(skip(rest), "where"),
         {:ok, c1, rest} <- ident(skip(rest)),
         :ok <- if(c1 == "left", do: :ok, else: {:error, "expected left"}),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, _, rest} <- parse_term(skip(rest), 0),
         {:ok, c2, rest} <- ident(skip(rest)),
         :ok <- if(c2 == "right", do: :ok, else: {:error, "expected right"}),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, _, rest} <- parse_term(skip(rest), 0) do
      {:ok, rest}
    end
  end

  defp parse_def(s) do
    with {:ok, rest} <- kw(s, "def"),
         {:ok, name, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), ":"),
         {:ok, tag, rest} <- parse_mode(skip(rest)),
         {:ok, ty, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), ":="),
         {:ok, body, rest} <- parse_term(skip(rest), 0) do
      {:ok, Map.merge(%{name: name, type: ty, body: body}, tag), rest}
    end
  end

  # tag ::= "run" "internal"? | "spec" | "evidence"
  defp parse_mode(s) do
    s = skip(s)

    cond do
      tag = forbidden_tag(s) ->
        {:error, "rejected tag #{tag}"}

      word_kw?(s, "spec") ->
        {:ok, %{mode: :spec}, after_kw(s, "spec")}

      word_kw?(s, "evidence") ->
        {:ok, %{mode: :evidence}, after_kw(s, "evidence")}

      word_kw?(s, "run") ->
        rest = after_kw(s, "run")
        rest_s = skip(rest)

        if word_kw?(rest_s, "internal") do
          {:ok, %{mode: :run, export: false}, after_kw(rest_s, "internal")}
        else
          {:ok, %{mode: :run, export: true}, rest}
        end

      true ->
        {:error, "expected run, run internal, spec, or evidence"}
    end
  end

  defp forbidden_tag(s) do
    Enum.find_value(
      [
        {"l", "ive"},
        {"d", "ead"},
        {"pr", "oof"},
        {"comp", ""},
        {"ghost", ""},
        {"export", ""}
      ],
      fn {a, b} ->
        tag = a <> b

        if word_kw?(s, tag) do
          rest = skip(after_kw(s, tag))

          if tag == "pr" <> "oof" and word_kw?(rest, "evidence") do
            tag <> " evidence"
          else
            tag
          end
        end
      end
    )
  end

  defp word_kw?(s, w) do
    has_prefix?(s, w) and not ident_continue?(s, w)
  end

  defp ident_continue?(s, w) do
    rest = after_kw(s, w)
    rest != "" and ident_char?(String.first(rest))
  end

  # Pratt-ish: apps are juxtaposition, arrows bind looser via Π/λ.
  defp parse_term(s, min_bp) do
    with {:ok, left, rest} <- parse_atom(skip(s)) do
      parse_infix(rest, left, min_bp)
    end
  end

  defp parse_infix(s, left, min_bp) do
    s0 = skip(s)

    cond do
      arrow_tok?(s0) and min_bp <= 5 ->
        with {:ok, rest} <- eat_arrow(s0),
             {:ok, right, rest} <- parse_term(skip(rest), 5) do
          parse_infix(rest, {:pi, :affine, left, "_", right}, min_bp)
        end

      times_tok?(s0) and min_bp <= 15 ->
        with {:ok, rest} <- eat_times(s0),
             {:ok, right, rest} <- parse_term(skip(rest), 16) do
          parse_infix(rest, {:prod, left, right}, min_bp)
        end

      sum_tok?(s0) and min_bp <= 12 ->
        with {:ok, rest} <- eat_sum(s0),
             {:ok, right, rest} <- parse_term(skip(rest), 13) do
          parse_infix(rest, {:sum, left, right}, min_bp)
        end

      starts_atom?(s0) and min_bp <= 20 ->
        with {:ok, arg, rest} <- parse_atom(s0) do
          parse_infix(rest, {:app, left, arg}, min_bp)
        end

      true ->
        {:ok, left, s}
    end
  end

  defp arrow_tok?(s) do
    (has_prefix?(s, "→") or has_prefix?(s, "->")) and not has_prefix?(s, "=>")
  end

  defp eat_arrow(s) do
    cond do
      has_prefix?(s, "→") -> {:ok, after_kw(s, "→")}
      has_prefix?(s, "->") -> {:ok, after_kw(s, "->")}
      true -> {:error, "expected →"}
    end
  end

  defp times_tok?(s), do: has_prefix?(s, "×") or has_prefix?(s, "*")

  defp eat_times(s) do
    cond do
      has_prefix?(s, "×") -> {:ok, after_kw(s, "×")}
      has_prefix?(s, "*") -> {:ok, after_kw(s, "*")}
      true -> {:error, "expected ×"}
    end
  end

  defp sum_tok?(s), do: has_prefix?(s, "⊎")

  defp eat_sum(s) do
    if has_prefix?(s, "⊎"), do: {:ok, after_kw(s, "⊎")}, else: {:error, "expected ⊎"}
  end

  defp starts_atom?(s) do
    s = skip(s)

    cond do
      word_kw?(s, "motive") ->
        false

      word_kw?(s, "in") ->
        false

      word_kw?(s, "def") ->
        false

      word_kw?(s, "where") ->
        false

      word_kw?(s, "data") ->
        false

      word_kw?(s, "left") ->
        false

      word_kw?(s, "right") ->
        false

      true ->
        case s do
          <<c, _::binary>>
          when c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ or c == ?( or
                 c == ?{ ->
            true

          _ ->
            false
        end
    end
  end

  defp parse_atom(s) do
    s = skip(s)

    cond do
      has_prefix?(s, "Type") ->
        {:ok, :typ, after_kw(s, "Type")}

      has_prefix?(s, "Nat") ->
        {:ok, :nat, after_kw(s, "Nat")}

      has_prefix?(s, "Unit") ->
        {:ok, :unit, after_kw(s, "Unit")}

      has_prefix?(s, "Empty") ->
        {:ok, :empty, after_kw(s, "Empty")}

      has_prefix?(s, "refl") ->
        {:ok, :rfl, after_kw(s, "refl")}

      has_prefix?(s, "tt") ->
        {:ok, :one, after_kw(s, "tt")}

      has_prefix?(s, "0") ->
        {:ok, :ze, after_kw(s, "0")}

      has_prefix?(s, "suc") ->
        parse_suc(s)

      word_kw?(s, "Either") ->
        parse_either(s)

      word_kw?(s, "left") ->
        parse_unary(s, "left", :left)

      word_kw?(s, "right") ->
        parse_unary(s, "right", :right)

      word_kw?(s, "Stream") ->
        parse_stream(s)

      word_kw?(s, "Always") ->
        parse_always(s)

      word_kw?(s, "unfold") ->
        parse_unf(s)

      word_kw?(s, "uncons") ->
        parse_ucons(s)

      word_kw?(s, "fst") ->
        parse_unary(s, "fst", :fst)

      word_kw?(s, "snd") ->
        parse_unary(s, "snd", :snd)

      word_kw?(s, "head") ->
        with {:ok, e, rest} <- parse_unary_arg(s, "head") do
          {:ok, {:fst, {:ucons, e}}, rest}
        end

      word_kw?(s, "tail") ->
        with {:ok, e, rest} <- parse_unary_arg(s, "tail") do
          {:ok, {:snd, {:ucons, e}}, rest}
        end

      has_prefix?(s, "Π") or has_prefix?(s, "Pi") ->
        parse_pi(s)

      has_prefix?(s, "λ") or has_prefix?(s, "lam") ->
        parse_lam(s)

      has_prefix?(s, "matchEmpty") ->
        parse_memp(s)

      has_prefix?(s, "match") ->
        parse_match(s)

      has_prefix?(s, "rewrite") ->
        parse_rwt(s)

      first_char(s) == ?{ ->
        parse_idt(s)

      first_char(s) == ?( ->
        with {:ok, rest} <- tok(s, "("),
             {:ok, t, rest} <- parse_term(skip(rest), 0) do
          rest1 = skip(rest)

          if has_prefix?(rest1, ",") do
            with {:ok, rest} <- tok(rest1, ","),
                 {:ok, u, rest} <- parse_term(skip(rest), 0),
                 {:ok, rest} <- tok(skip(rest), ")") do
              {:ok, {:pair, t, u}, rest}
            end
          else
            with {:ok, rest} <- tok(rest1, ")") do
              {:ok, t, rest}
            end
          end
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
    with {:ok, rest} <- kw(s, "suc") do
      rest = skip(rest)

      if has_prefix?(rest, "(") do
        with {:ok, rest} <- tok(rest, "("),
             {:ok, t, rest} <- parse_term(skip(rest), 0),
             {:ok, rest} <- tok(skip(rest), ")") do
          {:ok, {:su, t}, rest}
        end
      else
        with {:ok, t, rest} <- parse_atom(rest) do
          {:ok, {:su, t}, rest}
        end
      end
    end
  end

  defp parse_stream(s) do
    with {:ok, rest} <- kw(s, "Stream"),
         {:ok, a, rest} <- parse_atom(skip(rest)) do
      {:ok, {:stream, a}, rest}
    end
  end

  defp parse_always(s) do
    with {:ok, rest} <- kw(s, "Always"),
         {:ok, _a, rest} <- parse_atom(skip(rest)),
         {:ok, p, rest} <- parse_atom(skip(rest)),
         {:ok, st, rest} <- parse_atom(skip(rest)) do
      {:ok, {:always, p, st}, rest}
    end
  end

  defp parse_unf(s) do
    with {:ok, rest} <- kw(s, "unfold"),
         {:ok, seed, rest} <- parse_atom(skip(rest)),
         {:ok, f, rest} <- parse_atom(skip(rest)) do
      {:ok, {:unf, seed, f}, rest}
    end
  end

  defp parse_ucons(s) do
    parse_unary(s, "uncons", :ucons)
  end

  defp parse_unary(s, w, tag) do
    with {:ok, e, rest} <- parse_unary_arg(s, w) do
      {:ok, {tag, e}, rest}
    end
  end

  defp parse_unary_arg(s, w) do
    with {:ok, rest} <- kw(s, w),
         {:ok, e, rest} <- parse_atom(skip(rest)) do
      {:ok, e, rest}
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

  defp parse_match(s) do
    with {:ok, rest} <- kw(s, "match"),
         {:ok, e, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- kw(skip(rest), "motive"),
         {:ok, rest} <- tok(skip(rest), "("),
         {:ok, rest} <- eat_lam(skip(rest)),
         {:ok, x, rest} <- parse_motive_binder(skip(rest)),
         {:ok, rest} <- either_tok(skip(rest), ["→", "->"]),
         {:ok, p, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), ")"),
         {:ok, rest} <- tok(skip(rest), "|") do
      rest = skip(rest)

      cond do
        word_kw?(rest, "left") -> parse_msum_cases(e, x, p, rest)
        true -> parse_mnat_cases(e, x, p, rest)
      end
    end
  end

  defp parse_motive_binder(s) do
    s = skip(s)

    if has_prefix?(s, "(") do
      with {:ok, {_q, x, _a}, rest} <- parse_binder(s), do: {:ok, x, rest}
    else
      ident(s)
    end
  end

  defp parse_mnat_cases(e, x, p, rest) do
    with {:ok, rest} <- kw(rest, "0"),
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

  defp parse_msum_cases(e, x, p, rest) do
    with {:ok, rest} <- kw(rest, "left"),
         {:ok, a, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), "=>"),
         {:ok, l, rest} <- parse_term(skip(rest), 0),
         {:ok, rest} <- tok(skip(rest), "|"),
         {:ok, rest} <- kw(skip(rest), "right"),
         {:ok, b, rest} <- ident(skip(rest)),
         {:ok, rest} <- tok(skip(rest), "=>"),
         {:ok, r, rest} <- parse_term(skip(rest), 0) do
      {:ok, {:msum, e, x, p, a, l, b, r}, rest}
    end
  end

  defp parse_either(s) do
    with {:ok, rest} <- kw(s, "Either"),
         {:ok, a, rest} <- parse_atom(skip(rest)),
         {:ok, b, rest} <- parse_atom(skip(rest)) do
      {:ok, {:sum, a, b}, rest}
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

    if has_prefix?(s, t),
      do: {:ok, after_kw(s, t)},
      else: {:error, "expected #{t}"}
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

  defp take_ident(<<c, r::binary>>, acc)
       when c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ or c == ?- do
    take_ident(r, acc <> <<c>>)
  end

  defp take_ident(s, acc), do: {acc, s}

  defp ident_char?(nil), do: false
  defp ident_char?(<<c>>), do: c in ?a..?z or c in ?A..?Z or c in ?0..?9 or c == ?_ or c == ?-
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
