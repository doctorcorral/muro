defmodule Muro.Example do
  @moduledoc """
  The v1 book: plus, IsEven, half, plus_suc, half_ok.
  Named FOAS, Agda-shaped.
  """

  @affine :affine

  defp v(x), do: {:var, x}
  defp app(f, a), do: {:app, f, a}
  defp app2(f, a, b), do: app(app(f, a), b)
  defp pi(x, a, b), do: {:pi, @affine, a, x, b}
  defp lam(x, a, t), do: {:lam, @affine, a, x, t}
  defp d(name), do: {:def, name}
  defp su(t), do: {:su, t}
  defp idt(l, r), do: {:idt, :nat, l, r}

  defp plus, do: d("plus")
  defp is_even, do: d("IsEven")
  defp half, do: d("half")
  defp plus_suc, do: d("plus_suc")
  defp half_ok, do: d("half_ok")

  defp id_half(x), do: idt(app2(plus(), app(half(), x), app(half(), x)), x)

  def plus_ty, do: pi("n", :nat, pi("m", :nat, :nat))

  def plus_tm do
    lam("n", :nat,
      lam("m", :nat,
        {:mnat, v("n"), "_", :nat, v("m"), "n1", su(app2(plus(), v("n1"), v("m")))}
      )
    )
  end

  def is_even_ty, do: pi("n", :nat, :typ)

  def is_even_tm do
    lam("n", :nat,
      {:mnat, v("n"), "_", :typ, :unit, "n1",
       {:mnat, v("n1"), "_", :typ, :empty, "p", app(is_even(), v("p"))}}
    )
  end

  def half_ty, do: pi("n", :nat, :nat)

  def half_tm do
    lam("n", :nat,
      {:mnat, v("n"), "_", :nat, :ze, "n1",
       {:mnat, v("n1"), "_", :nat, :ze, "p", su(app(half(), v("p")))}}
    )
  end

  def plus_suc_ty do
    pi("n", :nat,
      pi("m", :nat,
        idt(app2(plus(), v("n"), su(v("m"))), su(app2(plus(), v("n"), v("m"))))
      )
    )
  end

  def plus_suc_tm do
    lam("n", :nat,
      lam("m", :nat,
        {:mnat, v("n"), "n1",
         idt(app2(plus(), v("n1"), su(v("m"))), su(app2(plus(), v("n1"), v("m")))),
         :rfl, "n1",
         {:rwt, app2(plus_suc(), v("n1"), v("m")), "z",
          idt(su(v("z")), su(su(app2(plus(), v("n1"), v("m"))))), :rfl}}
      )
    )
  end

  def half_ok_ty do
    pi("n", :nat, pi("e", app(is_even(), v("n")), id_half(v("n"))))
  end

  def half_ok_tm do
    lam("n", :nat,
      lam("e", app(is_even(), v("n")),
        app(even_match(), v("e"))
      )
    )
  end

  defp even_match do
    {:mnat, v("n"), "x", pi("e1", app(is_even(), v("x")), id_half(v("x"))),
     lam("_", app(is_even(), :ze), :rfl), "n1", odd_match()}
  end

  defp odd_match do
    {:mnat, v("n1"), "y", pi("e1", app(is_even(), su(v("y"))), id_half(su(v("y")))),
     lam("e1", app(is_even(), su(:ze)),
       {:memp, v("e1"), "_", id_half(su(:ze))}
     ), "p", even_step()}
  end

  defp even_step do
    lam("e2", app(is_even(), su(su(v("p")))),
      {:rwt, app2(plus_suc(), app(half(), v("p")), app(half(), v("p"))), "z",
       idt(su(v("z")), su(su(v("p")))),
       {:rwt, app2(half_ok(), v("p"), v("e2")), "z",
        idt(su(su(v("z"))), su(su(v("p")))), :rfl}}
    )
  end

  def book do
    [
      %{name: "plus", mode: :run, export: true, type: plus_ty(), body: plus_tm()},
      %{name: "IsEven", mode: :proof, type: is_even_ty(), body: is_even_tm()},
      %{name: "half", mode: :run, export: true, type: half_ty(), body: half_tm()},
      %{name: "plus_suc", mode: :proof, type: plus_suc_ty(), body: plus_suc_tm()},
      %{name: "half_ok", mode: :proof, type: half_ok_ty(), body: half_ok_tm()}
    ]
  end
end
