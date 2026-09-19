defmodule Muro.Ast do
  @moduledoc """
  Named FOAS (parser / pretty / emit) and de Bruijn terms (checker).
  """

  @type qty :: :affine | :reuse | :erased
  @type mode :: :run | :spec | :evidence
  @type name :: String.t()

  # Named FOAS. Binders carry the name string.
  @type named ::
          {:var, name}
          | :typ
          | {:pi, qty, named, name, named}
          | {:lam, qty, named, name, named}
          | {:app, named, named}
          | :nat
          | :ze
          | {:su, named}
          | :unit
          | :one
          | :empty
          | {:mdata, named, name, named, [{name, [name], named}]}
          | {:mnat, named, name, named, named, name, named}
          | {:memp, named, name, named}
          | {:munit, named, name, named, named}
          | {:idt, named, named, named}
          | :rfl
          | {:rwt, named, name, named, named}
          | {:def, name}
          | {:ann, named, named}
          | {:prod, named, named}
          | {:pair, named, named}
          | {:fst, named}
          | {:snd, named}
          | {:stream, named}
          | {:always, named, named}
          | {:bisim, named, named}
          | {:nu, name, named}
          | {:unf, named, named}
          | {:ucons, named}

  # de Bruijn. Indices count from the nearest binder (0).
  @type db ::
          {:var, non_neg_integer()}
          | :typ
          | {:pi, qty, db, db}
          | {:lam, qty, db, db}
          | {:app, db, db}
          | :nat
          | :ze
          | {:su, db}
          | :unit
          | :one
          | :empty
          | {:mdata, db, db, [{name, non_neg_integer(), db}]}
          | {:mnat, db, db, db, db}
          | {:memp, db, db}
          | {:munit, db, db, db}
          | {:idt, db, db, db}
          | :rfl
          | {:rwt, db, db, db}
          | {:def, name}
          | {:ann, db, db}
          | {:prod, db, db}
          | {:pair, db, db}
          | {:fst, db}
          | {:snd, db}
          | {:nu, db}
          | {:bisim, db, db}
          | {:unf, db, db}
          | {:ucons, db}

  @type defn :: %{
          name: name,
          mode: mode,
          type: named,
          body: named
        }

  @type book :: [defn]

  def to_db(named, env \\ [])

  def to_db({:var, x}, env) do
    case Enum.find_index(env, &(&1 == x)) do
      nil -> {:ok, {:def, x}}
      i -> {:ok, {:var, i}}
    end
  end

  def to_db(:typ, _), do: {:ok, :typ}
  def to_db(:nat, _), do: {:ok, :nat}
  def to_db(:ze, _), do: {:ok, :ze}
  def to_db(:unit, _), do: {:ok, :unit}
  def to_db(:one, _), do: {:ok, :one}
  def to_db(:empty, _), do: {:ok, :empty}
  def to_db(:rfl, _), do: {:ok, :rfl}
  def to_db({:def, n}, _), do: {:ok, {:def, n}}
  def to_db({:su, t}, env), do: map1(t, env, &{:su, &1})

  def to_db({:mdata, e, x, p, branches}, env) do
    with {:ok, e1} <- to_db(e, env),
         {:ok, p1} <- to_db(p, [x | env]),
         {:ok, bs} <- to_db_branches(branches, env) do
      {:ok, {:mdata, e1, p1, bs}}
    end
  end

  def to_db({:pi, q, a, x, b}, env) do
    with {:ok, a1} <- to_db(a, env),
         {:ok, b1} <- to_db(b, [x | env]),
         do: {:ok, {:pi, q, a1, b1}}
  end

  def to_db({:lam, q, a, x, t}, env) do
    with {:ok, a1} <- to_db(a, env),
         {:ok, t1} <- to_db(t, [x | env]),
         do: {:ok, {:lam, q, a1, t1}}
  end

  def to_db({:app, f, a}, env) do
    with {:ok, f1} <- to_db(f, env),
         {:ok, a1} <- to_db(a, env),
         do: {:ok, {:app, f1, a1}}
  end

  def to_db({:mnat, e, x, p, z, y, s}, env) do
    with {:ok, e1} <- to_db(e, env),
         {:ok, p1} <- to_db(p, [x | env]),
         {:ok, z1} <- to_db(z, env),
         {:ok, s1} <- to_db(s, [y | env]),
         do: {:ok, {:mnat, e1, p1, z1, s1}}
  end

  def to_db({:memp, e, x, p}, env) do
    with {:ok, e1} <- to_db(e, env),
         {:ok, p1} <- to_db(p, [x | env]),
         do: {:ok, {:memp, e1, p1}}
  end

  def to_db({:munit, e, x, p, u}, env) do
    with {:ok, e1} <- to_db(e, env),
         {:ok, p1} <- to_db(p, [x | env]),
         {:ok, u1} <- to_db(u, env),
         do: {:ok, {:munit, e1, p1, u1}}
  end

  def to_db({:idt, a, e1, e2}, env) do
    with {:ok, a1} <- to_db(a, env),
         {:ok, e11} <- to_db(e1, env),
         {:ok, e21} <- to_db(e2, env),
         do: {:ok, {:idt, a1, e11, e21}}
  end

  def to_db({:rwt, eq, x, p, t}, env) do
    with {:ok, eq1} <- to_db(eq, env),
         {:ok, p1} <- to_db(p, [x | env]),
         {:ok, t1} <- to_db(t, env),
         do: {:ok, {:rwt, eq1, p1, t1}}
  end

  def to_db({:ann, e, a}, env) do
    with {:ok, e1} <- to_db(e, env),
         {:ok, a1} <- to_db(a, env),
         do: {:ok, {:ann, e1, a1}}
  end

  def to_db({:prod, a, b}, env) do
    with {:ok, a1} <- to_db(a, env),
         {:ok, b1} <- to_db(b, env),
         do: {:ok, {:prod, a1, b1}}
  end

  def to_db({:pair, a, b}, env) do
    with {:ok, a1} <- to_db(a, env),
         {:ok, b1} <- to_db(b, env),
         do: {:ok, {:pair, a1, b1}}
  end

  def to_db({:fst, t}, env), do: map1(t, env, &{:fst, &1})
  def to_db({:snd, t}, env), do: map1(t, env, &{:snd, &1})

  def to_db({:stream, a}, env) do
    with {:ok, a1} <- to_db(a, env) do
      {:ok, {:nu, {:prod, Muro.Subst.wk(a1), {:var, 0}}}}
    end
  end

  def to_db({:always, p, s}, env) do
    with {:ok, p1} <- to_db(p, env),
         {:ok, s1} <- to_db(s, env) do
      payload = {:app, p1, {:fst, {:ucons, s1}}}
      {:ok, {:nu, {:prod, Muro.Subst.wk(payload), {:var, 0}}}}
    end
  end

  def to_db({:nu, x, f}, env) do
    with {:ok, f1} <- to_db(f, [x | env]), do: {:ok, {:nu, f1}}
  end

  def to_db({:bisim, s, t}, env) do
    with {:ok, s1} <- to_db(s, env),
         {:ok, t1} <- to_db(t, env),
         do: {:ok, {:bisim, s1, t1}}
  end

  def to_db({:ucons, s}, env), do: map1(s, env, &{:ucons, &1})

  def to_db({:unf, s, f}, env) do
    with {:ok, s1} <- to_db(s, env),
         {:ok, f1} <- to_db(f, env),
         do: {:ok, {:unf, s1, f1}}
  end

  def to_db(other, _), do: {:error, "bad named term #{inspect(other)}"}

  defp map1(t, env, f) do
    with {:ok, t1} <- to_db(t, env), do: {:ok, f.(t1)}
  end

  defp to_db_branches(branches, env) do
    Enum.reduce_while(branches, {:ok, []}, fn {cname, binders, body}, {:ok, acc} ->
      env1 = Enum.reverse(binders) ++ env

      case to_db(body, env1) do
        {:ok, b} -> {:cont, {:ok, acc ++ [{cname, length(binders), b}]}}
        err -> {:halt, err}
      end
    end)
  end

  def def_to_db(%{name: n, mode: m, type: ty, body: bo} = d) do
    with {:ok, ty1} <- to_db(ty),
         {:ok, bo1} <- to_db(bo) do
      base = %{name: n, mode: m, type: ty1, body: bo1}

      {:ok,
       if Map.has_key?(d, :export) do
         Map.put(base, :export, d.export)
       else
         base
       end}
    end
  end

  def data_to_db(%{name: n, params: params, ctors: ctors} = d) do
    indices = Map.get(d, :indices, [])

    with {:ok, params1} <- params_to_db(params),
         {:ok, indices1} <- params_to_db(indices),
         {:ok, ctors1} <- ctors_to_db(params, ctors) do
      {:ok, %{kind: :data, name: n, params: params1, indices: indices1, ctors: ctors1}}
    end
  end

  defp params_to_db(params) do
    Enum.reduce_while(params, {:ok, []}, fn {q, x, a}, {:ok, acc} ->
      case to_db(a) do
        {:ok, a1} -> {:cont, {:ok, acc ++ [{q, x, a1}]}}
        err -> {:halt, err}
      end
    end)
  end

  defp ctors_to_db(params, ctors) do
    Enum.reduce_while(ctors, {:ok, []}, fn %{name: cn, type: ty}, {:ok, acc} ->
      wrapped =
        Enum.reduce(Enum.reverse(params), ty, fn {q, x, a}, t ->
          {:pi, q, a, x, t}
        end)

      case to_db(wrapped) do
        {:ok, ty1} -> {:cont, {:ok, acc ++ [%{name: cn, type: ty1}]}}
        err -> {:halt, err}
      end
    end)
  end

  def book_to_db(book) do
    Enum.reduce_while(book, {:ok, []}, fn d, {:ok, acc} ->
      result =
        if Map.get(d, :kind) == :data do
          data_to_db(d)
        else
          def_to_db(d)
        end

      case result do
        {:ok, d1} -> {:cont, {:ok, acc ++ [d1]}}
        err -> {:halt, err}
      end
    end)
  end
end
