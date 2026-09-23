defmodule Muro.Check do
  @moduledoc """
  Bidirectional checker. Each clause is tagged with its Agda ⊢ constructor
  from `Muro.Check` (`⇒-var-run`, `⇐-refl`, …). There is no promotion.
  """

  alias Muro.{Ast, Subst}

  # Default fuel. Fuel bounds reduction (whnf, conversion, isData, index
  # matching) and the substitution of a forced match argument; everything
  # else is structural recursion on the term, as in Agda's Muro.Check.
  # Running out is reported as an error, never as a silently unreduced term.
  @fuel 2000
  @out_of_fuel "out of fuel (the checker gave up reducing; raise the fuel)"

  @doc "The default fuel of `check_sig/2` and `check_def/3`."
  def default_fuel, do: @fuel

  # -- lookup ----------------------------------------------------------------

  defp lookup_def(book, name) do
    case Enum.find(book, &(Map.get(&1, :kind, :def) != :data and &1.name == name)) do
      nil -> {:error, "unknown definition #{name}"}
      d -> {:ok, d}
    end
  end

  defp lookup_data(book, name) do
    case Enum.find(book, &(Map.get(&1, :kind) == :data and &1.name == name)) do
      nil -> {:error, "unknown data type #{name}"}
      d -> {:ok, d}
    end
  end

  defp lookup_ctor(book, name) do
    Enum.find_value(book, fn
      %{kind: :data, name: dname, ctors: cs} = d ->
        case Enum.find_index(cs, &(&1.name == name)) do
          nil -> nil
          i -> {d, dname, i, Enum.at(cs, i)}
        end

      _ ->
        nil
    end)
    |> case do
      nil -> {:error, "unknown constructor #{name}"}
      found -> {:ok, found}
    end
  end

  defp data_name?(book, name), do: match?({:ok, _}, lookup_data(book, name))
  defp ctor_name?(book, name), do: match?({:ok, _}, lookup_ctor(book, name))

  # -- context: newest at index 0 -------------------------------------------

  defp ext(gamma, q, a) do
    [{q, Subst.wk(a)} | Enum.map(gamma, fn {q1, a1} -> {q1, Subst.wk(a1)} end)]
  end

  defp qty_of(gamma, x), do: elem(Enum.at(gamma, x), 0)
  defp typ_of(gamma, x), do: elem(Enum.at(gamma, x), 1)

  # -- rec state -------------------------------------------------------------

  defp empty_rec, do: %{self: nil, smaller: [], rec_ok: [], next_ok: false, guarded: false}
  defp def_rec(name), do: %{self: name, smaller: [], rec_ok: [], next_ok: true, guarded: false}

  defp ext_rec(rs, new_small, new_ok) do
    %{
      rs
      | smaller: [new_small | rs.smaller],
        rec_ok: [new_ok | rs.rec_ok],
        next_ok: false
    }
  end

  defp keep_next(old, new), do: %{new | next_ok: old.next_ok}

  defp bind_rec(rs, q) do
    new = ext_rec(rs, false, rs.next_ok)
    if q == :erased, do: keep_next(rs, new), else: new
  end

  defp at(list, i), do: Enum.at(list, i) == true

  defp scrut_ok(rs, {:var, x}), do: at(rs.rec_ok, x) or at(rs.smaller, x)
  defp scrut_ok(_, _), do: false

  defp smaller_var?(rs, {:var, x}), do: at(rs.smaller, x)
  defp smaller_var?(_, _), do: false

  # -- uses ------------------------------------------------------------------

  defp u0s(n), do: List.duplicate(:u0, n)
  defp one_hot(n, x, u), do: List.replace_at(u0s(n), x, u)

  defp add_use(:u0, u), do: {:ok, u}
  defp add_use(u, :u0), do: {:ok, u}
  defp add_use(:u1, :u1), do: {:error, "affine variable used twice"}
  defp add_use(:uw, _), do: {:ok, :uw}
  defp add_use(_, :uw), do: {:ok, :uw}

  defp add_uses(us, vs) do
    Enum.zip(us, vs)
    |> Enum.reduce_while({:ok, []}, fn {u, v}, {:ok, acc} ->
      case add_use(u, v) do
        {:ok, w} -> {:cont, {:ok, acc ++ [w]}}
        err -> {:halt, err}
      end
    end)
  end

  defp max_use(:uw, _), do: :uw
  defp max_use(_, :uw), do: :uw
  defp max_use(:u1, _), do: :u1
  defp max_use(_, :u1), do: :u1
  defp max_use(_, _), do: :u0

  defp max_uses(us, vs), do: Enum.zip_with(us, vs, &max_use/2)

  defp combine(m, u, v) when m in [:run, :evidence], do: add_uses(u, v)
  defp combine(:spec, u, _), do: {:ok, List.duplicate(:u0, length(u))}

  defp combine_alt(m, u, v) when m in [:run, :evidence], do: max_uses(u, v)
  defp combine_alt(:spec, u, _), do: List.duplicate(:u0, length(u))

  defp check_bound(m, :erased, u) when m in [:run, :evidence] and u in [:u1, :uw],
    do: {:error, "erased variable used computationally"}

  defp check_bound(m, :affine, :uw) when m in [:run, :evidence],
    do: {:error, "affine variable used as reusable"}

  defp check_bound(_, _, _), do: :ok

  # Using a definition of `from` while checking in `to`.
  # spec ↛ evidence, evidence ↛ run, spec ↛ run.
  defp allowed_def?(from, to) do
    cond do
      from == to -> true
      from == :run -> true
      from == :evidence and to == :spec -> true
      true -> false
    end
  end

  defp infer_var_tax(k, book, gamma, n, x, mode) do
    case qty_of(gamma, x) do
      :erased ->
        {:error, "no promotion: erased variable in #{mode} mode"}

      q ->
        ty = typ_of(gamma, x)
        u = if q == :reuse, do: :uw, else: :u1

        if mode == :run do
          case run_ty(k, book, ty) do
            {:ok, true} -> {:ok, {ty, one_hot(n, x, u)}}
            {:ok, false} -> {:error, "no promotion: variable has a spec type"}
            err -> err
          end
        else
          {:ok, {ty, one_hot(n, x, u)}}
        end
    end
  end

  defp nctx(gamma), do: length(gamma)

  # -- apps / rec ------------------------------------------------------------

  defp apps(t), do: apps(t, [])
  defp apps({:app, f, a}, acc), do: apps(f, [a | acc])
  defp apps(f, acc), do: {f, acc}

  defp ctor_head_book?(book, t) do
    case elem(apps(t), 0) do
      :ze -> true
      {:su, _} -> true
      :one -> true
      {:def, n} -> ctor_name?(book, n)
      _ -> false
    end
  end

  defp nth_qty({:pi, q, _, _}, 0), do: {:ok, q}
  defp nth_qty({:pi, _, _, b}, i), do: nth_qty(b, i - 1)
  defp nth_qty(_, _), do: {:error, "recursive-call spine longer than Π telescope"}

  # Descent is required for run and evidence, not for spec.
  defp check_rec(_book, :spec, _rs, _t), do: :ok

  defp check_rec(book, mode, rs, t) when mode in [:run, :evidence] do
    case apps(t) do
      {{:def, name}, args} when rs.self == name ->
        if rs.guarded do
          :ok
        else
          descend(book, mode, rs, name, args, 0)
        end

      _ ->
        :ok
    end
  end

  defp descend(book, mode, rs, name, args, j),
    do: descend(book, mode, rs, name, args, j, false)

  defp descend(book, _mode, _rs, name, [], j, seen_comp) do
    with {:ok, d} <- lookup_def(book, name) do
      case nth_qty(d.type, j) do
        {:ok, _} ->
          :ok

        {:error, _} ->
          if seen_comp,
            do: {:error, "recursive call does not descend on a smaller argument"},
            else: :ok
      end
    end
  end

  defp descend(book, mode, rs, name, [a | as], j, seen_comp) do
    with {:ok, d} <- lookup_def(book, name),
         {:ok, q} <- nth_qty(d.type, j) do
      cond do
        q == :erased ->
          descend(book, mode, rs, name, as, j + 1, seen_comp)

        smaller_var?(rs, a) ->
          :ok

        true ->
          descend(book, mode, rs, name, as, j + 1, true)
      end
    end
  end

  # -- whnf ------------------------------------------------------------------

  # Weak-head normalisation, fuelled. `{:ok, t}` is a weak-head normal form
  # (or a stuck term); `{:error, msg}` is out of fuel.
  defp whnf(0, _book, _t), do: {:error, @out_of_fuel}

  defp whnf(k, book, {:app, f, a}) do
    case whnf(k - 1, book, f) do
      {:ok, {:lam, _, _, t}} -> whnf(k - 1, book, Subst.inst(t, a))
      {:ok, f1} -> {:ok, {:app, f1, a}}
      err -> err
    end
  end

  defp whnf(k, book, {:mnat, e, p, z, s}) do
    case whnf(k - 1, book, e) do
      {:ok, :ze} -> whnf(k - 1, book, z)
      {:ok, {:su, u}} -> whnf(k - 1, book, Subst.inst(s, u))
      {:ok, e1} -> {:ok, {:mnat, e1, p, z, s}}
      err -> err
    end
  end

  defp whnf(k, book, {:mdata, e, p, bs}) do
    with {:ok, e1} <- whnf(k - 1, book, e) do
      case ctor_spine(book, e1) do
        {:ok, {_dname, ci, args}} ->
          case Enum.at(bs, ci) do
            {_n, _ar, b} -> whnf(k - 1, book, Subst.inst_n(b, args))
            nil -> {:ok, {:mdata, e1, p, bs}}
          end

        :error ->
          {:ok, {:mdata, e1, p, bs}}
      end
    end
  end

  defp whnf(k, book, {:munit, e, p, u}) do
    case whnf(k - 1, book, e) do
      {:ok, :one} -> whnf(k - 1, book, u)
      {:ok, e1} -> {:ok, {:munit, e1, p, u}}
      err -> err
    end
  end

  defp whnf(k, book, {:memp, e, p}) do
    with {:ok, e1} <- whnf(k - 1, book, e), do: {:ok, {:memp, e1, p}}
  end

  defp whnf(k, book, {:def, name}) do
    case lookup_def(book, name) do
      {:ok, d} -> whnf(k - 1, book, d.body)
      _ -> {:ok, {:def, name}}
    end
  end

  defp whnf(k, book, {:ann, e, _}), do: whnf(k - 1, book, e)

  defp whnf(k, book, {:fst, e}) do
    case whnf(k - 1, book, e) do
      {:ok, {:pair, a, _}} -> whnf(k - 1, book, a)
      {:ok, e1} -> {:ok, {:fst, e1}}
      err -> err
    end
  end

  defp whnf(k, book, {:snd, e}) do
    case whnf(k - 1, book, e) do
      {:ok, {:pair, _, b}} -> whnf(k - 1, book, b)
      {:ok, e1} -> {:ok, {:snd, e1}}
      err -> err
    end
  end

  defp whnf(k, book, {:ucons, e}) do
    case whnf(k - 1, book, e) do
      {:ok, {:unf, s, f}} ->
        case whnf(k - 1, book, {:app, f, s}) do
          {:ok, {:pair, h, t}} -> {:ok, {:pair, h, {:unf, t, f}}}
          {:ok, _} -> {:ok, {:ucons, {:unf, s, f}}}
          err -> err
        end

      {:ok, e1} ->
        {:ok, {:ucons, e1}}

      err ->
        err
    end
  end

  defp whnf(_, _, t), do: {:ok, t}

  # Fuelled, as Agda's isData: fuel also bounds the descent into data
  # parameters (a spec definition may be recursive: X : Type := D X).
  defp is_data(0, _book, _t), do: {:error, @out_of_fuel}

  defp is_data(k, book, t) do
    with {:ok, t1} <- whnf(k, book, t) do
      {h, as} = apps(t1)
      k = k - 1

      case h do
        :nat ->
          {:ok, as == []}

        :unit ->
          {:ok, as == []}

        :empty ->
          {:ok, as == []}

        :i64 ->
          {:ok, as == []}

        :f32ty ->
          {:ok, as == []}

        {:tensor, _, _} ->
          {:ok, as == []}

        {:def, n} ->
          case lookup_data(book, n) do
            {:ok, d} -> all_data(k, book, Enum.take(as, length(d.params)))
            _ -> {:ok, false}
          end

        _ ->
          {:ok, false}
      end
    end
  end

  defp all_data(_k, _book, []), do: {:ok, true}

  defp all_data(k, book, [a | as]) do
    case is_data(k, book, a) do
      {:ok, true} -> all_data(k, book, as)
      other -> other
    end
  end

  # `:ok` when `a` is a Data type, `{:error, msg}` when it is not or the
  # fuel ran out.
  defp guard_data(k, book, a, msg) do
    case is_data(k, book, a) do
      {:ok, true} -> :ok
      {:ok, false} -> {:error, msg}
      err -> err
    end
  end

  # Shape of a run type after one whnf, read syntactically as Agda's
  # runTy: a variable, a leaf type, a Π whose codomain is one, a product
  # of two, ν F with F one (the bound variable counts as a run type), a
  # data type or an application of one.
  defp run_ty(k, book, t) do
    with {:ok, t1} <- whnf(k, book, t), do: {:ok, run_ty_n(book, t1)}
  end

  defp run_ty_n(_book, {:var, _}), do: true
  defp run_ty_n(_book, :nat), do: true
  defp run_ty_n(_book, :unit), do: true
  defp run_ty_n(_book, :empty), do: true
  defp run_ty_n(_book, :i64), do: true
  defp run_ty_n(_book, :f32ty), do: true
  defp run_ty_n(_book, {:tensor, _, _}), do: true
  defp run_ty_n(book, {:pi, _, _, b}), do: run_ty_n(book, b)
  defp run_ty_n(book, {:nu, f}), do: run_ty_n(book, f)
  defp run_ty_n(book, {:prod, a, b}), do: run_ty_n(book, a) and run_ty_n(book, b)
  defp run_ty_n(book, {:app, f, _}), do: run_ty_n(book, f)
  defp run_ty_n(book, {:def, n}), do: data_name?(book, n)
  defp run_ty_n(_book, _), do: false

  # -- conversion ------------------------------------------------------------

  defp syn_eq(a, b), do: a == b

  defp conv(0, _, _, _), do: {:error, @out_of_fuel}

  defp conv(k, book, u, v) do
    if syn_eq(u, v) do
      :ok
    else
      stuck_cong(k, book, u, v)
    end
  end

  defp stuck_cong(k, book, u, v) do
    case {apps(u), apps(v)} do
      {{{:def, i}, [a | as]}, {{:def, j}, [b | bs]}} ->
        if i == j and not ctor_head_book?(book, a) and not ctor_head_book?(book, b) do
          with :ok <- conv(k - 1, book, a, b), do: conv_args(k - 1, book, as, bs)
        else
          conv_whnf(k - 1, book, u, v)
        end

      _ ->
        conv_whnf(k - 1, book, u, v)
    end
  end

  defp conv_whnf(k, book, u, v) do
    with {:ok, u1} <- whnf(k, book, u),
         {:ok, v1} <- whnf(k, book, v),
         do: conv_n(k, book, u1, v1)
  end

  defp conv_args(_k, _book, [], []), do: :ok
  defp conv_args(_k, _book, _, []), do: {:error, "conv: spine length mismatch"}
  defp conv_args(_k, _book, [], _), do: {:error, "conv: spine length mismatch"}

  defp conv_args(k, book, [a | as], [b | bs]) do
    with :ok <- conv(k, book, a, b), do: conv_args(k, book, as, bs)
  end

  defp conv_n(_k, _book, a, b) when a == b, do: :ok
  defp conv_n(k, book, {:su, a}, {:su, b}), do: conv(k, book, a, b)
  defp conv_n(_k, _book, {:var, i}, {:var, j}) when i == j, do: :ok

  defp conv_n(k, book, {:pi, q, a, b}, {:pi, q, a1, b1}) do
    with :ok <- conv(k, book, a, a1), do: conv(k, book, b, b1)
  end

  defp conv_n(k, book, {:lam, q, a, t}, {:lam, q, a1, t1}) do
    with :ok <- conv(k, book, a, a1), do: conv(k, book, t, t1)
  end

  defp conv_n(k, book, {:app, f, a}, {:app, g, b}) do
    with :ok <- conv(k, book, f, g), do: conv(k, book, a, b)
  end

  defp conv_n(k, book, {:idt, a, x, y}, {:idt, a1, x1, y1}) do
    with :ok <- conv(k, book, a, a1),
         :ok <- conv(k, book, x, x1),
         do: conv(k, book, y, y1)
  end

  defp conv_n(k, book, {:mnat, e, p, z, s}, {:mnat, e1, p1, z1, s1}) do
    with :ok <- conv(k, book, e, e1),
         :ok <- conv(k, book, p, p1),
         :ok <- conv(k, book, z, z1),
         do: conv(k, book, s, s1)
  end

  defp conv_n(k, book, {:memp, e, p}, {:memp, e1, p1}) do
    with :ok <- conv(k, book, e, e1), do: conv(k, book, p, p1)
  end

  defp conv_n(k, book, {:munit, e, p, u}, {:munit, e1, p1, u1}) do
    with :ok <- conv(k, book, e, e1),
         :ok <- conv(k, book, p, p1),
         do: conv(k, book, u, u1)
  end

  defp conv_n(k, book, {:rwt, e, p, t}, {:rwt, e1, p1, t1}) do
    with :ok <- conv(k, book, e, e1),
         :ok <- conv(k, book, p, p1),
         do: conv(k, book, t, t1)
  end

  defp conv_n(k, book, {:ann, e, a}, {:ann, e1, a1}) do
    with :ok <- conv(k, book, e, e1), do: conv(k, book, a, a1)
  end

  defp conv_n(k, book, {:prod, a, b}, {:prod, a1, b1}) do
    with :ok <- conv(k, book, a, a1), do: conv(k, book, b, b1)
  end

  defp conv_n(k, book, {:pair, a, b}, {:pair, a1, b1}) do
    with :ok <- conv(k, book, a, a1), do: conv(k, book, b, b1)
  end

  defp conv_n(k, book, {:fst, t}, {:fst, t1}), do: conv(k, book, t, t1)
  defp conv_n(k, book, {:snd, t}, {:snd, t1}), do: conv(k, book, t, t1)
  defp conv_n(k, book, {:nu, f}, {:nu, f1}), do: conv(k, book, f, f1)

  defp conv_n(k, book, {:unf, s, f}, {:unf, s1, f1}) do
    with :ok <- conv(k, book, s, s1), do: conv(k, book, f, f1)
  end

  defp conv_n(k, book, {:ucons, s}, {:ucons, s1}), do: conv(k, book, s, s1)

  defp conv_n(k, book, {:tensor, d, s}, {:tensor, d1, s1}) do
    with :ok <- conv(k, book, d, d1), do: conv(k, book, s, s1)
  end

  defp conv_n(k, book, {:addi, x, y}, {:addi, x1, y1}) do
    with :ok <- conv(k, book, x, x1), do: conv(k, book, y, y1)
  end

  defp conv_n(k, book, {:muli, x, y}, {:muli, x1, y1}) do
    with :ok <- conv(k, book, x, x1), do: conv(k, book, y, y1)
  end

  defp conv_n(k, book, {:addt, t, u}, {:addt, t1, u1}) do
    with :ok <- conv(k, book, t, t1), do: conv(k, book, u, u1)
  end

  defp conv_n(k, book, {:toi64, t}, {:toi64, t1}), do: conv(k, book, t, t1)

  defp conv_n(k, book, {:packi, x, y}, {:packi, x1, y1}) do
    with :ok <- conv(k, book, x, x1), do: conv(k, book, y, y1)
  end

  defp conv_n(k, book, {:mdata, e, p, bs}, {:mdata, e1, p1, bs1}) do
    with :ok <- conv(k, book, e, e1),
         :ok <- conv(k, book, p, p1) do
      conv_mdata_bs(k, book, bs, bs1)
    end
  end

  defp conv_n(_k, _book, u, v),
    do: {:error, "cannot convert #{inspect(u)} ≁ #{inspect(v)}"}

  defp conv_mdata_bs(_k, _book, [], []), do: :ok

  defp conv_mdata_bs(k, book, [{n, ar, b} | bs], [{n, ar, b1} | bs1]) do
    with :ok <- conv(k, book, b, b1), do: conv_mdata_bs(k, book, bs, bs1)
  end

  defp conv_mdata_bs(_, _, _, _), do: {:error, "match branches do not convert"}

  defp view_pi(k, book, t) do
    case whnf(k, book, t) do
      {:ok, {:pi, q, a, b}} -> {:ok, {q, a, b}}
      {:ok, t1} -> {:error, "expected Π, got #{inspect(t1)}"}
      err -> err
    end
  end

  defp view_id(k, book, t) do
    case whnf(k, book, t) do
      {:ok, {:idt, a, x, y}} -> {:ok, {a, x, y}}
      {:ok, t1} -> {:error, "expected Id, got #{inspect(t1)}"}
      err -> err
    end
  end

  defp nx_dtype_ok(k, book, t) do
    case whnf(k, book, t) do
      {:ok, :i64} -> :ok
      {:ok, :f32ty} -> :ok
      {:ok, _} -> {:error, "Tensor dtype must be I64 or F32"}
      err -> err
    end
  end

  defp float_id_ok(k, book, a) do
    forbidden = {:error, "kernel identity is not defined on F32"}

    case whnf(k, book, a) do
      {:ok, :f32ty} ->
        forbidden

      {:ok, {:tensor, d, _}} ->
        case whnf(k, book, d) do
          {:ok, :f32ty} -> forbidden
          {:ok, _} -> :ok
          err -> err
        end

      {:ok, _} ->
        :ok

      err ->
        err
    end
  end

  # packI shape: toI64 (suc (suc 0))
  defp i64two, do: {:toi64, {:su, {:su, :ze}}}

  defp view_prod(k, book, t) do
    case whnf(k, book, t) do
      {:ok, {:prod, a, b}} -> {:ok, {a, b}}
      {:ok, t1} -> {:error, "expected ×, got #{inspect(t1)}"}
      err -> err
    end
  end

  defp view_nu(k, book, t) do
    case whnf(k, book, t) do
      {:ok, {:nu, f}} -> {:ok, f}
      {:ok, t1} -> {:error, "expected ν, got #{inspect(t1)}"}
      err -> err
    end
  end

  # ⇒-bisim / ⇐-unf: σ ~ τ = ν R. {head σ ≡ head τ} × R
  defp payload_ty(k, book, f) do
    case view_prod(k, book, Subst.inst(f, :unit)) do
      {:ok, {a, _}} -> {:ok, a}
      err -> err
    end
  end

  defp expand_bisim(k, book, rs, gamma, s, t) do
    with {:ok, {ts, _}} <- infer(k, book, rs, gamma, :spec, s),
         {:ok, f} <- view_nu(k, book, ts),
         {:ok, a} <- payload_ty(k, book, f),
         {:ok, {tt, _}} <- infer(k, book, rs, gamma, :spec, t),
         :ok <- conv(k, book, ts, tt) do
      id = {:idt, a, {:fst, {:ucons, s}}, {:fst, {:ucons, t}}}
      {:ok, {:nu, {:prod, Subst.wk(id), {:var, 0}}}}
    end
  end

  defp as_nu(k, book, rs, gamma, t) do
    case whnf(k, book, t) do
      {:ok, {:nu, f}} ->
        {:ok, f}

      {:ok, {:bisim, s, u}} ->
        with {:ok, {:nu, f}} <- expand_bisim(k, book, rs, gamma, s, u), do: {:ok, f}

      {:ok, t1} ->
        {:error, "expected ν, got #{inspect(t1)}"}

      err ->
        err
    end
  end

  defp view_data(k, book, t) do
    with {:ok, t1} <- whnf(k, book, t) do
      {h, args} = apps(t1)

      case h do
        {:def, n} ->
          case lookup_data(book, n) do
            {:ok, d} ->
              np = length(d.params)
              ni = length(Map.get(d, :indices, []))

              if length(args) == np + ni do
                {:ok, {d, n, Enum.take(args, np), Enum.drop(args, np)}}
              else
                {:error, "data applied to the wrong number of arguments"}
              end

            _ ->
              {:error, "expected data type, got #{inspect(h)}"}
          end

        _ ->
          {:error, "expected data type, got #{inspect(h)}"}
      end
    end
  end

  defp ctor_spine(book, t) do
    {h, args} = apps(t)

    case h do
      {:def, n} ->
        case lookup_ctor(book, n) do
          {:ok, {_d, dname, ci, _c}} -> {:ok, {dname, ci, args}}
          _ -> :error
        end

      _ ->
        :error
    end
  end

  defp is_d_type?(book, dname, t) do
    case elem(apps(t), 0) do
      {:def, n} -> n == dname and data_name?(book, n)
      _ -> false
    end
  end

  # ⇒-unf productivity: self may not occur in the pair's head.
  defp has_self?(self, {:def, name}) when self == name, do: true
  defp has_self?(self, {:app, f, a}), do: has_self?(self, f) or has_self?(self, a)
  defp has_self?(self, {:su, t}), do: has_self?(self, t)
  defp has_self?(self, {:pair, a, b}), do: has_self?(self, a) or has_self?(self, b)
  defp has_self?(self, {:fst, t}), do: has_self?(self, t)
  defp has_self?(self, {:snd, t}), do: has_self?(self, t)
  defp has_self?(self, {:unf, s, f}), do: has_self?(self, s) or has_self?(self, f)
  defp has_self?(self, {:ucons, s}), do: has_self?(self, s)
  defp has_self?(self, {:tensor, d, s}), do: has_self?(self, d) or has_self?(self, s)
  defp has_self?(self, {:addi, x, y}), do: has_self?(self, x) or has_self?(self, y)
  defp has_self?(self, {:muli, x, y}), do: has_self?(self, x) or has_self?(self, y)
  defp has_self?(self, {:addt, t, u}), do: has_self?(self, t) or has_self?(self, u)
  defp has_self?(self, {:toi64, t}), do: has_self?(self, t)
  defp has_self?(self, {:packi, x, y}), do: has_self?(self, x) or has_self?(self, y)
  defp has_self?(self, {:lam, _, a, t}), do: has_self?(self, a) or has_self?(self, t)
  defp has_self?(self, {:pi, _, a, b}), do: has_self?(self, a) or has_self?(self, b)
  defp has_self?(self, {:prod, a, b}), do: has_self?(self, a) or has_self?(self, b)
  defp has_self?(self, {:nu, f}), do: has_self?(self, f)
  defp has_self?(self, {:bisim, s, t}), do: has_self?(self, s) or has_self?(self, t)

  defp has_self?(self, {:mdata, e, p, bs}) do
    has_self?(self, e) or has_self?(self, p) or
      Enum.any?(bs, fn {_, _, b} -> has_self?(self, b) end)
  end

  defp has_self?(_, _), do: false

  defp occurs?(x, {:var, y}), do: x == y
  defp occurs?(x, {:pi, _, a, b}), do: occurs?(x, a) or occurs?(x + 1, b)
  defp occurs?(x, {:lam, _, a, t}), do: occurs?(x, a) or occurs?(x + 1, t)
  defp occurs?(x, {:app, f, a}), do: occurs?(x, f) or occurs?(x, a)
  defp occurs?(x, {:su, t}), do: occurs?(x, t)
  defp occurs?(x, {:prod, a, b}), do: occurs?(x, a) or occurs?(x, b)
  defp occurs?(x, {:pair, a, b}), do: occurs?(x, a) or occurs?(x, b)
  defp occurs?(x, {:fst, t}), do: occurs?(x, t)
  defp occurs?(x, {:snd, t}), do: occurs?(x, t)
  defp occurs?(x, {:nu, f}), do: occurs?(x + 1, f)
  defp occurs?(x, {:bisim, s, t}), do: occurs?(x, s) or occurs?(x, t)

  defp occurs?(x, {:mdata, e, p, bs}) do
    occurs?(x, e) or occurs?(x + 1, p) or
      Enum.any?(bs, fn {_, ar, b} -> occurs?(x + ar, b) end)
  end

  defp occurs?(x, {:unf, s, f}), do: occurs?(x, s) or occurs?(x, f)
  defp occurs?(x, {:ucons, s}), do: occurs?(x, s)
  defp occurs?(x, {:idt, a, b, c}), do: occurs?(x, a) or occurs?(x, b) or occurs?(x, c)
  defp occurs?(x, {:tensor, d, s}), do: occurs?(x, d) or occurs?(x, s)
  defp occurs?(x, {:addi, a, b}), do: occurs?(x, a) or occurs?(x, b)
  defp occurs?(x, {:muli, a, b}), do: occurs?(x, a) or occurs?(x, b)
  defp occurs?(x, {:addt, t, u}), do: occurs?(x, t) or occurs?(x, u)
  defp occurs?(x, {:toi64, t}), do: occurs?(x, t)
  defp occurs?(x, {:packi, a, b}), do: occurs?(x, a) or occurs?(x, b)
  defp occurs?(_, _), do: false

  defp spos?(_x, {:var, _}), do: true
  defp spos?(x, {:prod, a, b}), do: spos?(x, a) and spos?(x, b)
  defp spos?(x, {:pi, _, a, b}), do: not occurs?(x, a) and spos?(x + 1, b)
  defp spos?(x, {:nu, f}), do: not occurs?(x + 1, f)
  defp spos?(x, t), do: not occurs?(x, t)

  defp strict_pos?(f), do: spos?(0, f)

  defp check_unfold(_k, _book, :spec, _rs, _f), do: :ok

  defp check_unfold(k, book, _m, rs, f) do
    with {:ok, f1} <- whnf(k, book, f), do: go_unfold(f1, rs.self)
  end

  defp go_unfold({:lam, _, _, t}, self), do: go_unfold(t, self)

  defp go_unfold({:pair, h, _}, self) do
    if has_self?(self, h),
      do: {:error, "unguarded recursive call"},
      else: :ok
  end

  defp go_unfold(_, _), do: {:error, "unfold body must be a pair"}

  defp check_nu(:spec, _ty, _body), do: :ok

  defp check_nu(_mode, ty, body) do
    go_nu(ty, body)
  end

  defp go_nu({:pi, _, _, b}, {:lam, _, _, t}), do: go_nu(b, t)
  defp go_nu({:nu, _}, {:unf, _, _}), do: :ok
  defp go_nu({:bisim, _, _}, {:unf, _, _}), do: :ok
  defp go_nu({:nu, _}, _), do: {:error, "ν value must be an unfold"}
  defp go_nu({:bisim, _, _}, _), do: {:error, "ν value must be an unfold"}
  defp go_nu(_, _), do: :ok

  # -- infer / check ---------------------------------------------------------

  defp infer(k, book, rs, gamma, mode, t) do
    n = nctx(gamma)

    case {mode, t} do
      # ⇒-var-run / ⇒-var-evid / ⇒-var-spec
      {:run, {:var, x}} ->
        infer_var_tax(k, book, gamma, n, x, :run)

      {:evidence, {:var, x}} ->
        infer_var_tax(k, book, gamma, n, x, :evidence)

      {:spec, {:var, x}} ->
        {:ok, {typ_of(gamma, x), u0s(n)}}

      # ⇒-ze
      {_, :ze} ->
        {:ok, {:nat, u0s(n)}}

      # ⇒-su
      {m, {:su, t1}} ->
        with {:ok, u} <- check(k, book, rs, gamma, m, t1, :nat),
             do: {:ok, {:nat, u}}

      # ⇒-tt
      {_, :one} ->
        {:ok, {:unit, u0s(n)}}

      {m, :nat} when m in [:run, :evidence] ->
        {:error, "no promotion: Nat is an erased term"}

      {m, :unit} when m in [:run, :evidence] ->
        {:error, "no promotion: Unit is an erased term"}

      {m, :empty} when m in [:run, :evidence] ->
        {:error, "no promotion: Empty is an erased term"}

      {m, :typ} when m in [:run, :evidence] ->
        {:error, "no promotion: Type is an erased term"}

      # ⇒-nat / ⇒-unit / ⇒-empty  (spec only)
      {:spec, :nat} ->
        {:ok, {:typ, u0s(n)}}

      {:spec, :unit} ->
        {:ok, {:typ, u0s(n)}}

      {:spec, :empty} ->
        {:ok, {:typ, u0s(n)}}

      # ⇒-mData
      {m, {:mdata, e, p, bs}} ->
        with {:ok, {et, eu}} <- infer(k, book, rs, gamma, m, e),
             {:ok, {d, dname, params, idxs}} <- view_data(k, book, et),
             :ok <- match_arity(bs, d.ctors),
             :ok <- check_motive(k, book, rs, gamma, d, dname, params, p),
             mot_fun = first_mot_lam(d, dname, params, p),
             {:ok, bu} <-
               check_branches(
                 k,
                 book,
                 rs,
                 gamma,
                 m,
                 dname,
                 params,
                 idxs,
                 mot_fun,
                 d.ctors,
                 bs
               ),
             {:ok, uses} <- combine(m, eu, bu) do
          {:ok, {Subst.apps_from(mot_fun, idxs ++ [e]), uses}}
        end

      {:spec, :typ} ->
        {:error, "Type has no type (no Type : Type)"}

      # ⇒-pi
      {m, {:pi, _, _, _}} when m in [:run, :evidence] ->
        {:error, "no promotion: Π is an erased term"}

      # The codomain must be small (: Type). With check_ty instead,
      # Π (x : A) → Type : Type and Type is a retract of a small type.
      {:spec, {:pi, q, a, b}} ->
        with :ok <- check_ty(k, book, rs, gamma, a),
             {:ok, _} <-
               check(k, book, ext_rec(rs, false, false), ext(gamma, q, a), :spec, b, :typ),
             do: {:ok, {:typ, u0s(n)}}

      # ⇒-lam
      {m, {:lam, q, a, t1}} ->
        with :ok <- check_ty(k, book, rs, gamma, a),
             :ok <-
               if(q == :reuse,
                 do: guard_data(k, book, a, "+ requires a Data type"),
                 else: :ok
               ),
             {:ok, {b, [u0 | us]}} <-
               infer(k, book, bind_rec(rs, q), ext(gamma, q, a), m, t1),
             :ok <- check_bound(m, q, u0) do
          {:ok, {{:pi, q, a, b}, us}}
        end

      # ⇒-app-aff / ⇒-app-era / ⇒-app-reuse
      {m, {:app, f, a}} ->
        with {:ok, {ft, fu}} <- infer(k, book, rs, gamma, m, f),
             {:ok, {q, a_ty, b}} <- view_pi(k, book, ft),
             {:ok, uses} <- infer_arg(k, book, rs, gamma, m, q, a_ty, fu, a, f),
             :ok <- check_rec(book, m, rs, {:app, f, a}) do
          {:ok, {Subst.inst(b, a), uses}}
        end

      {m, {:idt, _, _, _}} when m in [:run, :evidence] ->
        {:error, "no promotion: identity type is an erased term"}

      # ⇒-idt
      {:spec, {:idt, a, x, y}} ->
        with :ok <- check_ty(k, book, rs, gamma, a),
             :ok <- float_id_ok(k, book, a),
             {:ok, _} <- check(k, book, rs, gamma, :spec, x, a),
             {:ok, _} <- check(k, book, rs, gamma, :spec, y, a),
             do: {:ok, {:typ, u0s(n)}}

      {_, :rfl} ->
        {:error, "refl requires an expected identity type"}

      # ⇒-rwt
      {m, {:rwt, eq, p, t1}} ->
        with {:ok, {et, _}} <- infer(k, book, rs, gamma, :evidence, eq),
             {:ok, {a, lft, r}} <- view_id(k, book, et),
             :ok <- check_ty(k, book, ext_rec(rs, false, false), ext(gamma, :affine, a), p),
             {:ok, tu} <- check(k, book, rs, gamma, m, t1, Subst.inst(p, r)) do
          {:ok, {Subst.inst(p, lft), tu}}
        end

      # ⇒-mNat
      {m, {:mnat, e, p, z, s}} ->
        with {:ok, eu} <- check(k, book, rs, gamma, m, e, :nat),
             :ok <- check_ty(k, book, ext_rec(rs, false, false), ext(gamma, :affine, :nat), p),
             {:ok, zu} <- check(k, book, rs, gamma, m, z, Subst.inst(p, :ze)),
             ok? = scrut_ok(rs, e),
             {:ok, [u0 | sus]} <-
               check(
                 k,
                 book,
                 ext_rec(rs, ok?, ok?),
                 ext(gamma, :affine, :nat),
                 m,
                 s,
                 Subst.mot_suc(p)
               ),
             :ok <- check_bound(m, :affine, u0),
             {:ok, uses} <- combine(m, eu, combine_alt(m, zu, sus)) do
          {:ok, {Subst.inst(p, e), uses}}
        end

      # ⇒-mEmp
      {m, {:memp, e, p}} ->
        with {:ok, eu} <- check(k, book, rs, gamma, m, e, :empty),
             :ok <- check_ty(k, book, ext_rec(rs, false, false), ext(gamma, :affine, :empty), p) do
          {:ok, {Subst.inst(p, e), eu}}
        end

      # ⇒-mUnit
      {m, {:munit, e, p, u}} ->
        with {:ok, eu} <- check(k, book, rs, gamma, m, e, :unit),
             :ok <- check_ty(k, book, ext_rec(rs, false, false), ext(gamma, :affine, :unit), p),
             {:ok, uu} <- check(k, book, rs, gamma, m, u, Subst.inst(p, :one)),
             {:ok, uses} <- combine(m, eu, uu) do
          {:ok, {Subst.inst(p, e), uses}}
        end

      # ⇒-def / ⇒-dty
      {m, {:def, name}} ->
        case lookup_def(book, name) do
          {:ok, d} ->
            cond do
              not allowed_def?(d.mode, m) ->
                {:error, "no promotion: #{d.mode} definition #{name} in #{m} mode"}

              m == :run ->
                case run_ty(k, book, d.type) do
                  {:ok, true} -> {:ok, {d.type, u0s(n)}}
                  {:ok, false} -> {:error, "no promotion: definition #{name} has a spec type"}
                  err -> err
                end

              true ->
                {:ok, {d.type, u0s(n)}}
            end

          {:error, _} ->
            case lookup_data(book, name) do
              {:ok, d} when m == :spec ->
                {:ok, {dty_type(d.params, Map.get(d, :indices, [])), u0s(n)}}

              {:ok, _} ->
                {:error, "no promotion: a data former is an erased term"}

              {:error, _} ->
                case lookup_ctor(book, name) do
                  {:ok, _} ->
                    {:error, "constructor requires an expected data type"}

                  err ->
                    err
                end
            end
        end

      # ⇒-ann
      {m, {:ann, e, a}} ->
        with :ok <- check_ty(k, book, rs, gamma, a),
             {:ok, u} <- check(k, book, rs, gamma, m, e, a),
             do: {:ok, {a, u}}

      # ⇒-prod
      {m, {:prod, _, _}} when m in [:run, :evidence] ->
        {:error, "no promotion: × is an erased term"}

      # components small
      {:spec, {:prod, a, b}} ->
        with {:ok, _} <- check(k, book, rs, gamma, :spec, a, :typ),
             {:ok, _} <- check(k, book, rs, gamma, :spec, b, :typ),
             do: {:ok, {:typ, u0s(n)}}

      # ⇒-nu
      {m, {:nu, _}} when m in [:run, :evidence] ->
        {:error, "no promotion: ν is an erased term"}

      # body small
      {:spec, {:nu, f}} ->
        with {:ok, _} <-
               check(
                 k,
                 book,
                 ext_rec(rs, false, false),
                 ext(gamma, :affine, :typ),
                 :spec,
                 f,
                 :typ
               ),
             :ok <-
               if(strict_pos?(f),
                 do: :ok,
                 else: {:error, "ν body is not strictly positive"}
               ),
             do: {:ok, {:typ, u0s(n)}}

      {m, {:bisim, _, _}} when m in [:run, :evidence] ->
        {:error, "no promotion: ~ is an erased term"}

      {:spec, {:bisim, s, t}} ->
        with {:ok, _} <- expand_bisim(k, book, rs, gamma, s, t),
             do: {:ok, {:typ, u0s(n)}}

      # ⇒-pair
      {m, {:pair, a, b}} ->
        with {:ok, {ta, au}} <- infer(k, book, rs, gamma, m, a),
             {:ok, {tb, bu}} <- infer(k, book, rs, gamma, m, b),
             {:ok, uses} <- combine(m, au, bu) do
          {:ok, {{:prod, ta, tb}, uses}}
        end

      # ⇒-fst
      {m, {:fst, t1}} ->
        with {:ok, {tt, u}} <- infer(k, book, rs, gamma, m, t1),
             {:ok, {a, _}} <- view_prod(k, book, tt) do
          {:ok, {a, u}}
        end

      # ⇒-snd
      {m, {:snd, t1}} ->
        with {:ok, {tt, u}} <- infer(k, book, rs, gamma, m, t1),
             {:ok, {_, b}} <- view_prod(k, book, tt) do
          {:ok, {b, u}}
        end

      # ⇒-unf
      {m, {:unf, seed, f}} ->
        with {:ok, {s_ty, seed_u}} <- infer(k, book, rs, gamma, m, seed),
             {:ok, {ft, fu}} <- infer(k, book, rs, gamma, m, f),
             {:ok, {_q, s1, body}} <- view_pi(k, book, ft),
             :ok <- conv(k, book, s1, s_ty),
             {:ok, {a, s2}} <- view_prod(k, book, Subst.inst(body, seed)),
             :ok <- conv(k, book, s2, s_ty),
             :ok <- check_unfold(k, book, m, rs, f),
             {:ok, uses} <- combine(m, seed_u, fu) do
          {:ok, {{:nu, {:prod, Subst.wk(a), {:var, 0}}}, uses}}
        end

      # ⇒-ucons
      {m, {:ucons, s}} ->
        with {:ok, {tt, u}} <- infer(k, book, rs, gamma, m, s),
             {:ok, f} <- view_nu(k, book, tt) do
          {:ok, {Subst.inst(f, tt), u}}
        end

      # ⇒-i64 / ⇒-f32ty / ⇒-tensor
      {m, :i64} when m in [:run, :evidence] ->
        {:error, "no promotion: I64 is an erased term"}

      {m, :f32ty} when m in [:run, :evidence] ->
        {:error, "no promotion: F32 is an erased term"}

      {m, {:tensor, _, _}} when m in [:run, :evidence] ->
        {:error, "no promotion: Tensor is an erased term"}

      {:spec, :i64} ->
        {:ok, {:typ, u0s(n)}}

      {:spec, :f32ty} ->
        {:ok, {:typ, u0s(n)}}

      {:spec, {:tensor, d, s}} ->
        with :ok <- check_ty(k, book, rs, gamma, d),
             :ok <- nx_dtype_ok(k, book, d),
             {:ok, _} <- check(k, book, rs, gamma, :spec, s, :i64) do
          {:ok, {:typ, u0s(n)}}
        end

      # ⇒-addi / ⇒-muli
      {m, {:addi, x, y}} ->
        with {:ok, xu} <- check(k, book, rs, gamma, m, x, :i64),
             {:ok, yu} <- check(k, book, rs, gamma, m, y, :i64),
             {:ok, uses} <- combine(m, xu, yu) do
          {:ok, {:i64, uses}}
        end

      {m, {:muli, x, y}} ->
        with {:ok, xu} <- check(k, book, rs, gamma, m, x, :i64),
             {:ok, yu} <- check(k, book, rs, gamma, m, y, :i64),
             {:ok, uses} <- combine(m, xu, yu) do
          {:ok, {:i64, uses}}
        end

      # ⇒-addt
      {m, {:addt, t, u}} ->
        with {:ok, {tt, tu}} <- infer(k, book, rs, gamma, m, t),
             {:ok, tt1} <- whnf(k, book, tt) do
          case tt1 do
            {:tensor, d, s} ->
              with {:ok, uu} <- check(k, book, rs, gamma, m, u, {:tensor, d, s}),
                   {:ok, uses} <- combine(m, tu, uu) do
                {:ok, {{:tensor, d, s}, uses}}
              end

            t1 ->
              {:error, "addt expected a Tensor, got #{inspect(t1)}"}
          end
        end

      # ⇒-toi64
      {m, {:toi64, n1}} ->
        with {:ok, u} <- check(k, book, rs, gamma, m, n1, :nat),
             do: {:ok, {:i64, u}}

      # ⇒-packi
      {m, {:packi, x, y}} ->
        with {:ok, xu} <- check(k, book, rs, gamma, m, x, :i64),
             {:ok, yu} <- check(k, book, rs, gamma, m, y, :i64),
             {:ok, uses} <- combine(m, xu, yu) do
          {:ok, {{:tensor, :i64, i64two()}, uses}}
        end

      {_, t1} ->
        {:error, "cannot infer #{inspect(t1)}"}
    end
  end

  # An application f a in evidence mode whose head is an evidence
  # definition instantiates a theorem: the argument is still checked in
  # the mode of the application, but its uses are not computational and
  # are discarded (Agda: Env.appUses / evidCall).
  defp evid_call?(book, :evidence, f) do
    case elem(apps(f), 0) do
      {:def, name} ->
        case lookup_def(book, name) do
          {:ok, %{mode: :evidence}} -> true
          _ -> false
        end

      _ ->
        false
    end
  end

  defp evid_call?(_book, _m, _f), do: false

  defp app_uses(book, m, f, fu, au) do
    if evid_call?(book, m, f), do: {:ok, fu}, else: combine(m, fu, au)
  end

  defp infer_arg(k, book, rs, gamma, m, :erased, a, fu, arg, _f) do
    with {:ok, _} <- check(k, book, rs, gamma, :spec, arg, a) do
      if m in [:run, :evidence], do: {:ok, fu}, else: {:ok, u0s(nctx(gamma))}
    end
  end

  defp infer_arg(k, book, rs, gamma, m, :affine, a, fu, arg, f) do
    with {:ok, au} <- check(k, book, rs, gamma, m, arg, a),
         do: app_uses(book, m, f, fu, au)
  end

  defp infer_arg(k, book, rs, gamma, m, :reuse, a, fu, arg, f) do
    with :ok <- guard_data(k, book, a, "+ argument is not Data"),
         {:ok, au} <- check(k, book, rs, gamma, m, arg, a),
         do: app_uses(book, m, f, fu, au)
  end

  # A type is Type, a kind Π (x : A) → K, or a small type (⇒ Type).
  # Kinds are not small: Π (x : A) → Type is wf but has no type.
  # Syntax-directed, as ⊢ wf: a kind is recognised by its shape, anything
  # else must infer a type convertible to Type. (Reducing first would
  # accept terms that merely reduce to Type or to a kind, such as
  # (λ (x : Nat) → Type) 0, which have no derivation.)
  defp check_ty(k, book, rs, gamma, a) do
    case a do
      # type-Type
      :typ ->
        :ok

      # type-pi
      {:pi, q, a1, b} ->
        with :ok <- check_ty(k, book, rs, gamma, a1),
             do: check_ty(k, book, ext_rec(rs, false, false), ext(gamma, q, a1), b)

      # type-el
      a1 ->
        with {:ok, {t, _}} <- infer(k, book, rs, gamma, :spec, a1),
             do: conv(k, book, t, :typ)
    end
  end

  defp check(k, book, rs, gamma, mode, e, a) do
    case e do
      # ⇐-lam
      {:lam, q, a_ann, t} ->
        case view_pi(k, book, a) do
          {:ok, {q1, a1, b}} ->
            with :ok <- if(q == q1, do: :ok, else: {:error, "λ/Π quantity mismatch"}),
                 :ok <- check_ty(k, book, rs, gamma, a_ann),
                 :ok <- conv(k, book, a_ann, a1),
                 :ok <-
                   if(q == :reuse,
                     do: guard_data(k, book, a1, "+ requires a Data type"),
                     else: :ok
                   ),
                 {:ok, [u0 | us]} <-
                   check(
                     k,
                     book,
                     bind_rec(rs, q),
                     ext(gamma, q, a1),
                     mode,
                     t,
                     b
                   ),
                 :ok <- check_bound(mode, q, u0) do
              {:ok, us}
            end

          {:error, _} ->
            infer_conv(k, book, rs, gamma, mode, e, a)
        end

      # ⇐-refl
      :rfl ->
        with {:ok, {sort, x, y}} <- view_id(k, book, a),
             :ok <- float_id_ok(k, book, sort),
             :ok <- conv(k, book, x, y),
             do: {:ok, u0s(nctx(gamma))}

      # ⇐-pair
      {:pair, x, y} ->
        with {:ok, {a1, b1}} <- view_prod(k, book, a),
             {:ok, au} <- check(k, book, rs, gamma, mode, x, a1),
             {:ok, bu} <- check(k, book, rs, gamma, mode, y, b1),
             do: combine(mode, au, bu)

      # ⇐-unf
      {:unf, seed, {:lam, q, a_ann, t}} ->
        with {:ok, fu_ty} <- as_nu(k, book, rs, gamma, a),
             {:ok, {s_ty, seed_u}} <- infer(k, book, rs, gamma, mode, seed),
             :ok <- conv(k, book, a_ann, s_ty),
             {:ok, [u0 | us]} <-
               check(
                 k,
                 book,
                 ext_rec(rs, false, rs.next_ok),
                 ext(gamma, q, s_ty),
                 mode,
                 t,
                 Subst.wk(Subst.inst(fu_ty, s_ty))
               ),
             :ok <- check_bound(mode, q, u0),
             :ok <- check_unfold(k, book, mode, rs, {:lam, q, a_ann, t}),
             do: combine(mode, seed_u, us)

      {:unf, seed, f} ->
        with {:ok, fu_ty} <- as_nu(k, book, rs, gamma, a),
             {:ok, {s_ty, seed_u}} <- infer(k, book, rs, gamma, mode, seed),
             {:ok, fu} <-
               check(
                 k,
                 book,
                 rs,
                 gamma,
                 mode,
                 f,
                 {:pi, :affine, s_ty, Subst.wk(Subst.inst(fu_ty, s_ty))}
               ),
             :ok <- check_unfold(k, book, mode, rs, f),
             do: combine(mode, seed_u, fu)

      # ⇐-ctor / ⇐-conv
      _ ->
        case {view_data(k, book, a), ctor_spine(book, e)} do
          {{:ok, {_d, dname, params, idxs}}, {:ok, {dname2, _ci, _args}}}
          when dname == dname2 ->
            expected = Subst.apps_from({:def, dname}, params ++ idxs)
            check_ctor_app(k, book, rs, gamma, mode, dname, params, e, expected)

          _ ->
            infer_conv(k, book, rs, gamma, mode, e, a)
        end
    end
  end

  # ⇐-conv: infer, then convert to the expected type.
  defp infer_conv(k, book, rs, gamma, mode, e, a) do
    with {:ok, {b, u}} <- infer(k, book, rs, gamma, mode, e),
         :ok <- conv(k, book, b, a),
         do: {:ok, u}
  end

  # -- signature -------------------------------------------------------------

  defp tag(name, result) do
    case result do
      {:error, e} -> {:error, "#{name}: #{e}"}
      other -> other
    end
  end

  @doc """
  Check one definition of a de Bruijn book. `fuel` bounds reduction; running
  out is an error (`out of fuel …`), not a verdict.
  """
  def check_def(book, d, fuel \\ @fuel)

  def check_def(book, %{kind: :data} = d, fuel), do: check_data(book, d, fuel)

  def check_def(book, %{name: name, mode: mode, type: ty, body: body}, k) do
    with :ok <- tag("#{name} type", check_ty(k, book, empty_rec(), [], ty)),
         {:ok, _} <-
           tag("#{name} body", check(k, book, def_rec(name), [], mode, body, ty)),
         :ok <- tag("#{name} productivity", check_nu(mode, ty, body)) do
      :ok
    end
  end

  @doc """
  Check a named book. Options: `fuel: n` (default `default_fuel/0`).
  """
  def check_sig(named_book, opts \\ []) do
    fuel = Keyword.get(opts, :fuel, @fuel)

    with {:ok, book} <- Ast.book_to_db(named_book) do
      Enum.reduce_while(book, :ok, fn d, :ok ->
        case check_def(book, d, fuel) do
          :ok -> {:cont, :ok}
          err -> {:halt, err}
        end
      end)
    end
  end

  defp match_arity(bs, ctors) do
    if length(bs) == length(ctors) do
      :ok
    else
      {:error, "match branch count does not match constructors"}
    end
  end

  defp dty_type(params, indices) do
    idx_pis =
      Enum.reduce(Enum.reverse(indices), :typ, fn {q, _x, a}, acc ->
        {:pi, q, a, acc}
      end)

    Enum.reduce(Enum.reverse(params), idx_pis, fn {q, _x, _a}, acc ->
      {:pi, q, :typ, acc}
    end)
  end

  defp inst_params(_k, _book, t, []), do: {:ok, t}

  defp inst_params(k, book, t, [p | ps]) do
    case whnf(k, book, t) do
      {:ok, {:pi, _, _, b}} -> inst_params(k, book, Subst.inst(b, p), ps)
      {:ok, _} -> {:error, "constructor type has too few parameter binders"}
      err -> err
    end
  end

  # ⇐-ctor: a constructor spine against the data type dname at params. The
  # spine is walked from the head (Agda: inferCtorSpine): the constructor's
  # type instantiated at the parameters, then one Π per argument; an erased
  # field is checked in spec and contributes no uses.
  defp infer_ctor_spine(k, book, _rs, gamma, _m, dname, params, {:def, cname}) do
    case lookup_ctor(book, cname) do
      {:ok, {_d, dn, _ci, c}} when dn == dname ->
        with {:ok, rest} <- inst_params(k, book, c.type, params),
             do: {:ok, {rest, u0s(nctx(gamma))}}

      {:ok, _} ->
        {:error, "constructor of another data type"}

      err ->
        err
    end
  end

  defp infer_ctor_spine(k, book, rs, gamma, m, dname, params, {:app, f, a}) do
    with {:ok, {ty, fu}} <- infer_ctor_spine(k, book, rs, gamma, m, dname, params, f),
         {:ok, ty1} <- whnf(k, book, ty) do
      case ty1 do
        {:pi, q, a_ty, b} ->
          with {:ok, au} <- check(k, book, rs, gamma, field_mode(q, m), a, a_ty),
               {:ok, uses} <- combine_arg(q, m, au, fu),
               do: {:ok, {Subst.inst(b, a), uses}}

        _ ->
          {:error, "too many constructor arguments"}
      end
    end
  end

  defp infer_ctor_spine(_k, _book, _rs, _gamma, _m, _dname, _params, _e),
    do: {:error, "not a constructor spine"}

  defp field_mode(:erased, _m), do: :spec
  defp field_mode(_q, m), do: m

  defp combine_arg(:erased, :spec, _au, fu), do: {:ok, u0s(length(fu))}
  defp combine_arg(:erased, _m, _au, fu), do: {:ok, fu}
  defp combine_arg(_q, m, au, fu), do: combine(m, au, fu)

  # After the arguments, the residual telescope must be exhausted and be
  # the expected data type.
  defp check_ctor_app(k, book, rs, gamma, m, dname, params, e, expected) do
    with {:ok, {r, u}} <- infer_ctor_spine(k, book, rs, gamma, m, dname, params, e),
         {:ok, r1} <- whnf(k, book, r) do
      case r1 do
        {:pi, _, _, _} -> {:error, "too few constructor arguments"}
        _ -> with :ok <- conv(k, book, r1, expected), do: {:ok, u}
      end
    end
  end

  defp check_branches(_k, _book, _rs, gamma, _m, _dname, _params, _idxs, _mot, [], []) do
    {:ok, u0s(nctx(gamma))}
  end

  defp check_branches(k, book, rs, gamma, m, dname, params, idxs, mot, [c | cs], bs) do
    with {:ok, rest} <- inst_params(k, book, c.type, params) do
      np = nparams_of(book, dname)

      case analyze_forces(k, book, np, idxs, rest) do
        {:error, e} ->
          {:error, e}

        # a clash: the constructor cannot produce the expected indices,
        # its branch is skipped
        {:ok, :clash} ->
          case bs do
            [] -> {:error, "missing branch for #{c.name}"}
            [_ | bs1] -> check_branches(k, book, rs, gamma, m, dname, params, idxs, mot, cs, bs1)
          end

        {:ok, forces} ->
          case bs do
            [] ->
              {:error, "missing branch for #{c.name}"}

            [{bname, _ar, body} | bs1] ->
              if bname != c.name do
                {:error, "expected constructor #{c.name}, got #{bname}"}
              else
                wrapped = wrap_tel(rest, body)

                with {:ok, u} <-
                       check_br(
                         k,
                         book,
                         rs,
                         gamma,
                         m,
                         dname,
                         c.name,
                         rest,
                         wrapped,
                         mot,
                         [],
                         forces
                       ),
                     {:ok, v} <-
                       check_branches(k, book, rs, gamma, m, dname, params, idxs, mot, cs, bs1) do
                  {:ok, combine_alt(m, u, v)}
                end
              end
          end
      end
    end
  end

  defp check_branches(_, _, _, _, _, _, _, _, _, [], [_ | _]),
    do: {:error, "match branch count does not match constructors"}

  defp wrap_tel({:pi, q, a, b}, body), do: {:lam, q, a, wrap_tel(b, body)}
  defp wrap_tel(_, body), do: body

  defp nparams_of(book, dname) do
    case lookup_data(book, dname) do
      {:ok, d} -> length(d.params)
      _ -> 0
    end
  end

  # A branch of match against the constructor's telescope ty: one λ per
  # remaining Π (a forced argument is instantiated instead of bound), then
  # the body against the motive at the constructor applied to the arguments.
  defp check_br(k, book, rs, gamma, m, dname, cname, ty, br, mot, args, forces) do
    with {:ok, ty1} <- whnf(k, book, ty) do
      check_br_n(k, book, rs, gamma, m, dname, cname, ty1, br, mot, args, forces)
    end
  end

  defp check_br_n(k, book, rs, gamma, m, dname, cname, ty1, br, mot, args, forces) do
    case ty1 do
      {:pi, q, a, b} ->
        case {forces, br} do
          {[u | fs], {:lam, q1, a1, t}} when not is_nil(u) ->
            with :ok <- if(q == q1, do: :ok, else: {:error, "λ/Π quantity mismatch"}),
                 :ok <- check_ty(k, book, rs, gamma, a1),
                 :ok <- conv(k, book, a1, a) do
              force_br(
                k,
                book,
                rs,
                gamma,
                m,
                dname,
                cname,
                Subst.inst(b, u),
                Subst.inst(t, u),
                mot,
                args ++ [u],
                fs
              )
            end

          {[nil | fs], {:lam, q1, a1, t}} ->
            rec? = is_d_type?(book, dname, a)
            rs1 = ext_rec(rs, rec?, rec?)
            rs2 = if q == :erased, do: keep_next(rs, rs1), else: rs1
            args1 = Enum.map(args, &Subst.wk/1) ++ [{:var, 0}]

            with :ok <- if(q == q1, do: :ok, else: {:error, "λ/Π quantity mismatch"}),
                 :ok <- check_ty(k, book, rs, gamma, a1),
                 :ok <- conv(k, book, a1, a),
                 {:ok, [u0 | us]} <-
                   check_br(
                     k,
                     book,
                     rs2,
                     ext(gamma, q, a),
                     m,
                     dname,
                     cname,
                     b,
                     t,
                     Subst.wk(mot),
                     args1,
                     wk_forces(fs)
                   ),
                 :ok <- check_bound(m, q, u0) do
              {:ok, us}
            end

          {[_ | _], _} ->
            {:error, "match branch expected a λ for a constructor argument"}

          {[], _} ->
            {:error, "constructor telescope / force list mismatch"}
        end

      _ ->
        np = nparams_of(book, dname)
        {_, targs} = apps(ty1)
        idxs = Enum.drop(targs, np)
        ctor_tm = Subst.apps_from({:def, cname}, args)
        check(k, book, rs, gamma, m, br, Subst.apps_from(mot, idxs ++ [ctor_tm]))
    end
  end

  # A forced argument is substituted into the branch; the result is not a
  # subterm, so the step spends a unit of fuel (Agda: forceBr).
  defp force_br(0, _book, _rs, _gamma, _m, _dname, _cname, _ty, _br, _mot, _args, _forces),
    do: {:error, @out_of_fuel}

  defp force_br(k, book, rs, gamma, m, dname, cname, ty, br, mot, args, forces),
    do: check_br(k - 1, book, rs, gamma, m, dname, cname, ty, br, mot, args, forces)

  defp wk_forces(fs) do
    Enum.map(fs, fn
      nil -> nil
      t -> Subst.wk(t)
    end)
  end

  defp first_mot_lam(d, dname, params, p) do
    case Map.get(d, :indices, []) do
      [] -> {:lam, :affine, Subst.apps_from({:def, dname}, params), p}
      [{q, _, t} | _] -> {:lam, q, t, p}
    end
  end

  defp check_motive(k, book, rs, gamma, d, dname, params, p) do
    case Map.get(d, :indices, []) do
      [] ->
        dty = Subst.apps_from({:def, dname}, params)
        check_ty(k, book, ext_rec(rs, false, false), ext(gamma, :affine, dty), p)

      [{q, _, t} | rest] ->
        gamma1 = ext(gamma, q, t)
        args = Enum.map(params, &Subst.wk/1) ++ [{:var, 0}]
        tail = motive_tail(dname, args, rest)

        with {:ok, _} <- check(k, book, ext_rec(rs, false, false), gamma1, :spec, p, tail),
             do: :ok
    end
  end

  defp motive_tail(dname, args, []),
    do: {:pi, :affine, Subst.apps_from({:def, dname}, args), :typ}

  defp motive_tail(dname, args, [{q, _, t} | rest]) do
    {:pi, q, t, motive_tail(dname, Enum.map(args, &Subst.wk/1) ++ [{:var, 0}], rest)}
  end

  # Index clash / forcing. `{:ok, :clash}`: the constructor cannot produce
  # the expected indices (its branch is skipped); `{:ok, forces}`: one entry
  # per binder of tel, a forced term or nil.
  defp analyze_forces(k, book, np, expected, tel) do
    d = count_pis(tel)

    case walk_forces(k, book, np, expected, tel, 0) do
      {:ok, :clash} -> {:ok, :clash}
      {:ok, pairs} -> {:ok, forces_for(d, pairs)}
      err -> err
    end
  end

  defp walk_forces(k, book, np, expected, {:pi, _, _, b}, d),
    do: walk_forces(k, book, np, expected, b, d + 1)

  defp walk_forces(k, book, np, expected, t, d) do
    with {:ok, t1} <- whnf(k, book, t) do
      {_h, args} = apps(t1)
      match_idxs(k, book, d, expected, Enum.drop(args, np))
    end
  end

  defp count_pis({:pi, _, _, b}), do: 1 + count_pis(b)
  defp count_pis(_), do: 0

  defp match_idxs(_k, _book, _d, [], []), do: {:ok, []}

  defp match_idxs(k, book, d, [e | es], [t | ts]) do
    case match_idx(k, book, d, e, t) do
      {:ok, :clash} ->
        {:ok, :clash}

      {:ok, fs} ->
        case match_idxs(k, book, d, es, ts) do
          {:ok, :clash} -> {:ok, :clash}
          {:ok, gs} -> {:ok, fs ++ gs}
          err -> err
        end

      err ->
        err
    end
  end

  defp match_idxs(_, _, _, _, _), do: {:error, "index telescope length mismatch"}

  # No metavariables: suc is inverted, a rigid mismatch is a clash, a
  # variable is forced. Each inversion reduces both sides, so it spends a
  # unit of fuel (Agda: matchIdx).
  defp match_idx(0, _book, _d, _e, _t), do: {:error, @out_of_fuel}

  defp match_idx(k, book, d, e, t) do
    with {:ok, e1} <- whnf(k - 1, book, e),
         {:ok, t1} <- whnf(k - 1, book, t) do
      case {e1, t1} do
        {{:su, e2}, {:su, t2}} -> match_idx(k - 1, book, d, e2, t2)
        {:ze, :ze} -> {:ok, []}
        {{:su, _}, :ze} -> {:ok, :clash}
        {:ze, {:su, _}} -> {:ok, :clash}
        {e2, {:var, j}} when j < d -> {:ok, [{d - 1 - j, e2}]}
        {_, _} -> {:ok, []}
      end
    end
  end

  defp forces_for(0, _), do: []

  defp forces_for(n, pairs) do
    [lookup_force(pairs, 0) | forces_for(n - 1, shift_forces(pairs))]
  end

  defp lookup_force([], _), do: nil
  defp lookup_force([{j, u} | rest], i), do: if(j == i, do: u, else: lookup_force(rest, i))

  defp shift_forces([]), do: []
  defp shift_forces([{0, _} | rest]), do: shift_forces(rest)
  defp shift_forces([{j, u} | rest]), do: [{j - 1, u} | shift_forces(rest)]

  defp occurs_d?(i, {:def, n}), do: n == i
  defp occurs_d?(i, {:app, f, a}), do: occurs_d?(i, f) or occurs_d?(i, a)
  defp occurs_d?(i, {:pi, _, a, b}), do: occurs_d?(i, a) or occurs_d?(i, b)
  defp occurs_d?(i, {:lam, _, a, t}), do: occurs_d?(i, a) or occurs_d?(i, t)
  defp occurs_d?(i, {:prod, a, b}), do: occurs_d?(i, a) or occurs_d?(i, b)
  defp occurs_d?(i, {:pair, a, b}), do: occurs_d?(i, a) or occurs_d?(i, b)
  defp occurs_d?(i, {:idt, a, b, c}), do: occurs_d?(i, a) or occurs_d?(i, b) or occurs_d?(i, c)
  defp occurs_d?(i, {:su, t}), do: occurs_d?(i, t)
  defp occurs_d?(i, {:fst, t}), do: occurs_d?(i, t)
  defp occurs_d?(i, {:snd, t}), do: occurs_d?(i, t)
  defp occurs_d?(i, {:nu, f}), do: occurs_d?(i, f)
  defp occurs_d?(i, {:unf, s, f}), do: occurs_d?(i, s) or occurs_d?(i, f)
  defp occurs_d?(i, {:ucons, s}), do: occurs_d?(i, s)
  defp occurs_d?(i, {:ann, e, a}), do: occurs_d?(i, e) or occurs_d?(i, a)
  defp occurs_d?(i, {:tensor, d, s}), do: occurs_d?(i, d) or occurs_d?(i, s)
  defp occurs_d?(i, {:addi, a, b}), do: occurs_d?(i, a) or occurs_d?(i, b)
  defp occurs_d?(i, {:muli, a, b}), do: occurs_d?(i, a) or occurs_d?(i, b)
  defp occurs_d?(i, {:addt, t, u}), do: occurs_d?(i, t) or occurs_d?(i, u)
  defp occurs_d?(i, {:toi64, t}), do: occurs_d?(i, t)
  defp occurs_d?(i, {:packi, a, b}), do: occurs_d?(i, a) or occurs_d?(i, b)

  defp occurs_d?(i, {:mdata, e, p, bs}),
    do: occurs_d?(i, e) or occurs_d?(i, p) or Enum.any?(bs, fn {_, _, b} -> occurs_d?(i, b) end)

  defp occurs_d?(_, _), do: false

  defp pos_arg?(book, dname, a), do: is_d_type?(book, dname, a) or not occurs_d?(dname, a)

  defp check_tel_pos(book, dname, np, ni, {:pi, _, a, b}) do
    if pos_arg?(book, dname, a) do
      check_tel_pos(book, dname, np, ni, b)
    else
      {:error, "constructor is not strictly positive"}
    end
  end

  defp check_tel_pos(book, dname, np, ni, t) do
    {_h, args} = apps(t)

    cond do
      not is_d_type?(book, dname, t) ->
        {:error, "constructor does not target the data type"}

      length(args) != np + ni ->
        {:error, "constructor target has the wrong number of arguments"}

      true ->
        :ok
    end
  end

  # Constructor fields must be small types. Parameters are (A : Type) and
  # are skipped; a field of type Type would make the data type a large
  # inductive in Type, and match with motive Type would retract Type into it.
  defp check_ctor_fields(k, book, rs, gamma, np, {:pi, q, a, b}) when np > 0,
    do: check_ctor_fields(k, book, ext_rec(rs, false, false), ext(gamma, q, a), np - 1, b)

  defp check_ctor_fields(_k, _book, _rs, _gamma, np, _t) when np > 0,
    do: {:error, "constructor type has too few parameter binders"}

  defp check_ctor_fields(k, book, rs, gamma, 0, {:pi, q, a, b}) do
    with {:ok, _} <- check(k, book, rs, gamma, :spec, a, :typ),
         do: check_ctor_fields(k, book, ext_rec(rs, false, false), ext(gamma, q, a), 0, b)
  end

  defp check_ctor_fields(_k, _book, _rs, _gamma, 0, _t), do: :ok

  defp check_ctor_rest(book, dname, np, ni, t), do: skip_params(book, dname, np, ni, np, t)

  defp skip_params(book, dname, np, ni, 0, t), do: check_tel_pos(book, dname, np, ni, t)

  defp skip_params(book, dname, np, ni, k, {:pi, _, _, b}) when k > 0,
    do: skip_params(book, dname, np, ni, k - 1, b)

  defp skip_params(_, _, _, _, k, _) when k > 0,
    do: {:error, "constructor type has too few parameter binders"}

  defp check_data(book, %{name: name, params: params, ctors: ctors} = d, k) do
    np = length(params)
    ni = length(Map.get(d, :indices, []))

    Enum.reduce_while(ctors, :ok, fn c, :ok ->
      result =
        with :ok <- tag("#{c.name} type", check_ty(k, book, empty_rec(), [], c.type)),
             :ok <- tag("#{c.name} type", check_ctor_fields(k, book, empty_rec(), [], np, c.type)) do
          check_ctor_rest(book, name, np, ni, c.type)
        end

      case tag(name, result) do
        :ok -> {:cont, :ok}
        err -> {:halt, err}
      end
    end)
  end
end
