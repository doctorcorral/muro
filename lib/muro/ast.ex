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
          | {:mnat, named, name, named, named, name, named}
          | {:memp, named, name, named}
          | {:munit, named, name, named, named}
          | {:idt, named, named, named}
          | :rfl
          | {:rwt, named, name, named, named}
          | {:def, name}
          | {:ann, named, named}

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
          | {:mnat, db, db, db, db}
          | {:memp, db, db}
          | {:munit, db, db, db}
          | {:idt, db, db, db}
          | :rfl
          | {:rwt, db, db, db}
          | {:def, name}
          | {:ann, db, db}

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

  def to_db(other, _), do: {:error, "bad named term #{inspect(other)}"}

  defp map1(t, env, f) do
    with {:ok, t1} <- to_db(t, env), do: {:ok, f.(t1)}
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

  def book_to_db(book) do
    Enum.reduce_while(book, {:ok, []}, fn d, {:ok, acc} ->
      case def_to_db(d) do
        {:ok, d1} -> {:cont, {:ok, acc ++ [d1]}}
        err -> {:halt, err}
      end
    end)
  end
end
