defmodule Muro.Subst do
  @moduledoc """
  Rename / substitute / instantiate de Bruijn terms. Mirrors Muro.Subst.
  """

  def lift(rho) do
    fn
      0 -> 0
      i -> rho.(i - 1) + 1
    end
  end

  def ren(rho, t) do
    case t do
      {:var, i} ->
        {:var, rho.(i)}

      :typ ->
        :typ

      {:pi, q, a, b} ->
        {:pi, q, ren(rho, a), ren(lift(rho), b)}

      {:lam, q, a, u} ->
        {:lam, q, ren(rho, a), ren(lift(rho), u)}

      {:app, f, a} ->
        {:app, ren(rho, f), ren(rho, a)}

      :nat ->
        :nat

      :ze ->
        :ze

      {:su, u} ->
        {:su, ren(rho, u)}

      :unit ->
        :unit

      :one ->
        :one

      :empty ->
        :empty

      {:mnat, e, p, z, s} ->
        {:mnat, ren(rho, e), ren(lift(rho), p), ren(rho, z), ren(lift(rho), s)}

      {:memp, e, p} ->
        {:memp, ren(rho, e), ren(lift(rho), p)}

      {:munit, e, p, u} ->
        {:munit, ren(rho, e), ren(lift(rho), p), ren(rho, u)}

      {:idt, a, x, y} ->
        {:idt, ren(rho, a), ren(rho, x), ren(rho, y)}

      :rfl ->
        :rfl

      {:rwt, e, p, u} ->
        {:rwt, ren(rho, e), ren(lift(rho), p), ren(rho, u)}

      {:def, n} ->
        {:def, n}

      {:ann, e, a} ->
        {:ann, ren(rho, e), ren(rho, a)}
    end
  end

  def wk(t), do: ren(fn i -> i + 1 end, t)

  def closed(t), do: t

  def lifts(sigma) do
    fn
      0 -> {:var, 0}
      i -> wk(sigma.(i - 1))
    end
  end

  def sub(sigma, t) do
    case t do
      {:var, i} ->
        sigma.(i)

      :typ ->
        :typ

      {:pi, q, a, b} ->
        {:pi, q, sub(sigma, a), sub(lifts(sigma), b)}

      {:lam, q, a, u} ->
        {:lam, q, sub(sigma, a), sub(lifts(sigma), u)}

      {:app, f, a} ->
        {:app, sub(sigma, f), sub(sigma, a)}

      :nat ->
        :nat

      :ze ->
        :ze

      {:su, u} ->
        {:su, sub(sigma, u)}

      :unit ->
        :unit

      :one ->
        :one

      :empty ->
        :empty

      {:mnat, e, p, z, s} ->
        {:mnat, sub(sigma, e), sub(lifts(sigma), p), sub(sigma, z), sub(lifts(sigma), s)}

      {:memp, e, p} ->
        {:memp, sub(sigma, e), sub(lifts(sigma), p)}

      {:munit, e, p, u} ->
        {:munit, sub(sigma, e), sub(lifts(sigma), p), sub(sigma, u)}

      {:idt, a, x, y} ->
        {:idt, sub(sigma, a), sub(sigma, x), sub(sigma, y)}

      :rfl ->
        :rfl

      {:rwt, e, p, u} ->
        {:rwt, sub(sigma, e), sub(lifts(sigma), p), sub(sigma, u)}

      {:def, n} ->
        {:def, n}

      {:ann, e, a} ->
        {:ann, sub(sigma, e), sub(sigma, a)}
    end
  end

  def inst(t, u) do
    sub(
      fn
        0 -> u
        i -> {:var, i - 1}
      end,
      t
    )
  end

  def mot_suc(p) do
    sub(
      fn
        0 -> {:su, {:var, 0}}
        i -> {:var, i}
      end,
      p
    )
  end
end
