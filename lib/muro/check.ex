defmodule Muro.Check do
  @moduledoc """
  Bidirectional checker. Each clause is tagged with its Agda ⊢ constructor
  from `Muro.Check` (`⇒-var-run`, `⇐-refl`, …). There is no promotion.
  """

  alias Muro.{Ast, Subst}

  @fuel 2000

  # -- lookup ----------------------------------------------------------------

  defp lookup_def(book, name) do
    case Enum.find(book, &(&1.name == name)) do
      nil -> {:error, "unknown definition #{name}"}
      d -> {:ok, d}
    end
  end

  # -- context: newest at index 0 -------------------------------------------

  defp ext(gamma, q, a) do
    [{q, Subst.wk(a)} | Enum.map(gamma, fn {q1, a1} -> {q1, Subst.wk(a1)} end)]
  end

  defp qty_of(gamma, x), do: elem(Enum.at(gamma, x), 0)
  defp typ_of(gamma, x), do: elem(Enum.at(gamma, x), 1)

  # -- rec state -------------------------------------------------------------

  defp empty_rec, do: %{self: nil, smaller: [], rec_ok: [], next_ok: false}
  defp def_rec(name), do: %{self: name, smaller: [], rec_ok: [], next_ok: true}

  defp ext_rec(rs, new_small, new_ok) do
    %{
      rs
      | smaller: [new_small | rs.smaller],
        rec_ok: [new_ok | rs.rec_ok],
        next_ok: false
    }
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

  defp combine(:run, u, v), do: add_uses(u, v)
  defp combine(:proof, u, _), do: {:ok, List.duplicate(:u0, length(u))}

  defp combine_alt(:run, u, v), do: max_uses(u, v)
  defp combine_alt(:proof, u, _), do: List.duplicate(:u0, length(u))

  defp check_bound(:run, :erased, u) when u in [:u1, :uw],
    do: {:error, "erased variable used in a run term"}

  defp check_bound(:run, :affine, :uw),
    do: {:error, "affine variable used as reusable"}

  defp check_bound(_, _, _), do: :ok

  defp nctx(gamma), do: length(gamma)

  # -- apps / rec ------------------------------------------------------------

  defp apps(t), do: apps(t, [])
  defp apps({:app, f, a}, acc), do: apps(f, [a | acc])
  defp apps(f, acc), do: {f, acc}

  defp ctor_head?(:ze), do: true
  defp ctor_head?({:su, _}), do: true
  defp ctor_head?(:one), do: true
  defp ctor_head?(_), do: false

  defp nth_qty({:pi, q, _, _}, 0), do: {:ok, q}
  defp nth_qty({:pi, _, _, b}, i), do: nth_qty(b, i - 1)
  defp nth_qty(_, _), do: {:error, "recursive-call spine longer than Π telescope"}

  # checkRec
  defp check_rec(book, mode, rs, t) do
    case apps(t) do
      {{:def, name}, args} when rs.self == name ->
        descend(book, mode, rs, name, args, 0)

      _ ->
        :ok
    end
  end

  defp descend(_book, _mode, _rs, _name, [], _j),
    do: {:error, "recursive call does not descend on a smaller argument"}

  defp descend(book, mode, rs, name, [a | as], j) do
    if smaller_var?(rs, a) do
      if mode == :run do
        with {:ok, d} <- lookup_def(book, name),
             {:ok, q} <- nth_qty(d.type, j) do
          if q == :erased, do: descend(book, mode, rs, name, as, j + 1), else: :ok
        end
      else
        :ok
      end
    else
      descend(book, mode, rs, name, as, j + 1)
    end
  end

  # -- whnf ------------------------------------------------------------------

  defp whnf(0, _book, t), do: t

  defp whnf(k, book, {:app, f, a}) do
    case whnf(k - 1, book, f) do
      {:lam, _, _, t} -> whnf(k - 1, book, Subst.inst(t, a))
      f1 -> {:app, f1, a}
    end
  end

  defp whnf(k, book, {:mnat, e, p, z, s}) do
    case whnf(k - 1, book, e) do
      :ze -> whnf(k - 1, book, z)
      {:su, u} -> whnf(k - 1, book, Subst.inst(s, u))
      e1 -> {:mnat, e1, p, z, s}
    end
  end

  defp whnf(k, book, {:munit, e, p, u}) do
    case whnf(k - 1, book, e) do
      :one -> whnf(k - 1, book, u)
      e1 -> {:munit, e1, p, u}
    end
  end

  defp whnf(k, book, {:memp, e, p}), do: {:memp, whnf(k - 1, book, e), p}

  defp whnf(k, book, {:def, name}) do
    case lookup_def(book, name) do
      {:ok, d} -> whnf(k - 1, book, d.body)
      _ -> {:def, name}
    end
  end

  defp whnf(k, book, {:ann, e, _}), do: whnf(k - 1, book, e)
  defp whnf(_, _, t), do: t

  defp is_data?(k, book, t) do
    case whnf(k, book, t) do
      :nat -> true
      :unit -> true
      :empty -> true
      _ -> false
    end
  end

  defp run_ty?(k, book, t) do
    case whnf(k, book, t) do
      :nat -> true
      :unit -> true
      :empty -> true
      {:pi, _, _, b} -> run_ty?(k, book, b)
      _ -> false
    end
  end

  # -- conversion ------------------------------------------------------------

  defp syn_eq(a, b), do: a == b

  defp conv(0, _, _, _), do: {:error, "conv: out of fuel"}

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
        if i == j and not ctor_head?(a) and not ctor_head?(b) do
          with :ok <- conv(k - 1, book, a, b), do: conv_args(k - 1, book, as, bs)
        else
          conv_n(k - 1, book, whnf(k - 1, book, u), whnf(k - 1, book, v))
        end

      _ ->
        conv_n(k - 1, book, whnf(k - 1, book, u), whnf(k - 1, book, v))
    end
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

  defp conv_n(_k, _book, u, v),
    do: {:error, "cannot convert #{inspect(u)} ≁ #{inspect(v)}"}

  defp view_pi(k, book, t) do
    case whnf(k, book, t) do
      {:pi, q, a, b} -> {:ok, {q, a, b}}
      t1 -> {:error, "expected Π, got #{inspect(t1)}"}
    end
  end

  defp view_id(k, book, t) do
    case whnf(k, book, t) do
      {:idt, a, x, y} -> {:ok, {a, x, y}}
      t1 -> {:error, "expected Id, got #{inspect(t1)}"}
    end
  end

  # -- infer / check ---------------------------------------------------------

  defp infer(k, book, rs, gamma, mode, t) do
    n = nctx(gamma)

    case {mode, t} do
      # ⇒-var-run / ⇒-var-proof
      {:run, {:var, x}} ->
        case qty_of(gamma, x) do
          :erased ->
            {:error, "no promotion: erased variable in run mode"}

          q ->
            ty = typ_of(gamma, x)

            if run_ty?(k, book, ty) do
              u = if q == :reuse, do: :uw, else: :u1
              {:ok, {ty, one_hot(n, x, u)}}
            else
              {:error, "no promotion: variable has a proof type"}
            end
        end

      {:proof, {:var, x}} ->
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

      {:run, :nat} ->
        {:error, "no promotion: Nat is an erased term"}

      {:run, :unit} ->
        {:error, "no promotion: Unit is an erased term"}

      {:run, :empty} ->
        {:error, "no promotion: Empty is an erased term"}

      {:run, :typ} ->
        {:error, "no promotion: Type is an erased term"}

      # ⇒-nat / ⇒-unit / ⇒-empty
      {:proof, :nat} ->
        {:ok, {:typ, u0s(n)}}

      {:proof, :unit} ->
        {:ok, {:typ, u0s(n)}}

      {:proof, :empty} ->
        {:ok, {:typ, u0s(n)}}

      {:proof, :typ} ->
        {:error, "Type has no type (no Type : Type)"}

      # ⇒-pi
      {:run, {:pi, _, _, _}} ->
        {:error, "no promotion: Π is an erased term"}

      {:proof, {:pi, q, a, b}} ->
        with :ok <- check_ty(k, book, rs, gamma, a),
             :ok <- check_ty(k, book, ext_rec(rs, false, false), ext(gamma, q, a), b),
             do: {:ok, {:typ, u0s(n)}}

      # ⇒-lam
      {m, {:lam, q, a, t1}} ->
        with :ok <- check_ty(k, book, rs, gamma, a),
             :ok <-
               if(q == :reuse,
                 do: if(is_data?(k, book, a), do: :ok, else: {:error, "+ requires a Data type"}),
                 else: :ok
               ),
             {:ok, {b, [u0 | us]}} <-
               infer(k, book, ext_rec(rs, false, rs.next_ok), ext(gamma, q, a), m, t1) ,
             :ok <- check_bound(m, q, u0) do
          {:ok, {{:pi, q, a, b}, us}}
        end

      # ⇒-app-aff / ⇒-app-era / ⇒-app-reuse
      {m, {:app, f, a}} ->
        with {:ok, {ft, fu}} <- infer(k, book, rs, gamma, m, f),
             {:ok, {q, a_ty, b}} <- view_pi(k, book, ft),
             {:ok, uses} <- infer_arg(k, book, rs, gamma, m, q, a_ty, fu, a),
             :ok <- check_rec(book, m, rs, {:app, f, a}) do
          {:ok, {Subst.inst(b, a), uses}}
        end

      {:run, {:idt, _, _, _}} ->
        {:error, "no promotion: identity type is an erased term"}

      # ⇒-idt
      {:proof, {:idt, a, x, y}} ->
        with :ok <- check_ty(k, book, rs, gamma, a),
             {:ok, _} <- check(k, book, rs, gamma, :proof, x, a),
             {:ok, _} <- check(k, book, rs, gamma, :proof, y, a),
             do: {:ok, {:typ, u0s(n)}}

      {_, :rfl} ->
        {:error, "refl requires an expected identity type"}

      # ⇒-rwt
      {m, {:rwt, eq, p, t1}} ->
        with {:ok, {et, _}} <- infer(k, book, rs, gamma, :proof, eq),
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
               check(k, book, ext_rec(rs, ok?, ok?), ext(gamma, :affine, :nat), m, s, Subst.mot_suc(p)),
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

      # ⇒-def
      {m, {:def, name}} ->
        with {:ok, d} <- lookup_def(book, name) do
          cond do
            m == :run and d.mode == :proof ->
              {:error, "no promotion: proof definition #{name} in run mode"}

            m == :run and not run_ty?(k, book, d.type) ->
              {:error, "no promotion: definition #{name} has a proof type"}

            true ->
              {:ok, {d.type, u0s(n)}}
          end
        end

      # ⇒-ann
      {m, {:ann, e, a}} ->
        with :ok <- check_ty(k, book, rs, gamma, a),
             {:ok, u} <- check(k, book, rs, gamma, m, e, a),
             do: {:ok, {a, u}}

      {_, t1} ->
        {:error, "cannot infer #{inspect(t1)}"}
    end
  end

  defp infer_arg(k, book, rs, gamma, m, :erased, a, fu, arg) do
    with {:ok, _} <- check(k, book, rs, gamma, :proof, arg, a) do
      if m == :run, do: {:ok, fu}, else: {:ok, u0s(nctx(gamma))}
    end
  end

  defp infer_arg(k, book, rs, gamma, m, :affine, a, fu, arg) do
    with {:ok, au} <- check(k, book, rs, gamma, m, arg, a), do: combine(m, fu, au)
  end

  defp infer_arg(k, book, rs, gamma, m, :reuse, a, fu, arg) do
    if is_data?(k, book, a) do
      with {:ok, au} <- check(k, book, rs, gamma, m, arg, a), do: combine(m, fu, au)
    else
      {:error, "+ argument is not Data"}
    end
  end

  defp check_ty(k, book, rs, gamma, a) do
    case whnf(k, book, a) do
      # type-Type
      :typ ->
        :ok

      # type-el
      a1 ->
        with {:ok, {t, _}} <- infer(k, book, rs, gamma, :proof, a1),
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
                     do:
                       if(is_data?(k, book, a1),
                         do: :ok,
                         else: {:error, "+ requires a Data type"}
                       ),
                     else: :ok
                   ),
                 {:ok, [u0 | us]} <-
                   check(
                     k,
                     book,
                     ext_rec(rs, false, rs.next_ok),
                     ext(gamma, q, a1),
                     mode,
                     t,
                     b
                   ),
                 :ok <- check_bound(mode, q, u0) do
              {:ok, us}
            end

          {:error, _} ->
            with {:ok, {b, u}} <- infer(k, book, rs, gamma, mode, e),
                 :ok <- conv(k, book, b, a),
                 do: {:ok, u}
        end

      # ⇐-refl
      :rfl ->
        with {:ok, {_a, x, y}} <- view_id(k, book, a),
             :ok <- conv(k, book, x, y),
             do: {:ok, u0s(nctx(gamma))}

      # ⇐-conv
      _ ->
        with {:ok, {b, u}} <- infer(k, book, rs, gamma, mode, e),
             :ok <- conv(k, book, b, a),
             do: {:ok, u}
    end
  end

  # -- signature -------------------------------------------------------------

  defp tag(name, result) do
    case result do
      {:error, e} -> {:error, "#{name}: #{e}"}
      other -> other
    end
  end

  def check_def(book, %{name: name, mode: mode, type: ty, body: body}) do
    k = @fuel

    with :ok <- tag("#{name} type", check_ty(k, book, empty_rec(), [], ty)),
         {:ok, _} <-
           tag("#{name} body", check(k, book, def_rec(name), [], mode, body, ty)) do
      :ok
    end
  end

  def check_sig(named_book) do
    with {:ok, book} <- Ast.book_to_db(named_book) do
      Enum.reduce_while(book, :ok, fn d, :ok ->
        case check_def(book, d) do
          :ok -> {:cont, :ok}
          err -> {:halt, err}
        end
      end)
    end
  end
end
