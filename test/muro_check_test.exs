defmodule Muro.CheckTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, Emit, Example, Parser}

  test "parse, check, and emit half_ok.muro" do
    src = File.read!("examples/half_ok.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.NatFromFile, book)
    assert out =~ ~r/\bdef plus\b/
    assert out =~ ~r/\bdef half\b/
    refute out =~ "half_ok"
    refute out =~ "IsEven"
    refute out =~ "plus_suc"
  end

  test "Muro.Check decides half_ok" do
    assert Check.check_sig(Example.book()) == :ok
  end

  test "run internal helper is defp" do
    assert {:ok, book} = Parser.parse(File.read!("examples/internal_ok.muro"))
    assert Check.check_sig(book) == :ok
    src = Emit.emit_module(Muro.InternalOk, book)
    assert src =~ ~r/\bdefp step\b/
    assert src =~ ~r/\bdef inc\b/
    refute src =~ ~r/\bdef step\b/
  end

  test "emit plus and half as def; omit spec and evidence" do
    src = Emit.emit_module(Muro.NatLive, Example.book())
    assert src =~ ~r/\bdef plus\b/
    assert src =~ ~r/\bdef half\b/
    refute src =~ "def half_ok"
    refute src =~ "def IsEven"
    refute src =~ "plus_suc"
  end

  test "affine duplication fails in evidence and is allowed in spec" do
    arrow = {:pi, :affine, :nat, "_", :nat}

    evid = %{
      name: "dup_evid",
      mode: :evidence,
      type: {:pi, :affine, arrow, "f", :nat},
      body:
        {:lam, :affine, arrow, "f",
         {:app, {:app, {:var, "plus"}, {:app, {:var, "f"}, :ze}}, {:app, {:var, "f"}, :ze}}}
    }

    spec = %{
      name: "dup_spec",
      mode: :spec,
      type: {:pi, :affine, :nat, "n", :typ},
      body:
        {:lam, :affine, :nat, "n",
         {:idt, :nat, {:app, {:app, {:var, "plus"}, {:var, "n"}}, {:var, "n"}}, {:var, "n"}}}
    }

    assert {:error, msg} = Check.check_sig([evid | Example.book()])
    assert msg =~ "affine"

    assert Check.check_sig([spec | Example.book()]) == :ok
  end

  test "spec never becomes evidence or a run" do
    as_run = %{
      name: "bad_run",
      mode: :run,
      export: true,
      type: {:pi, :affine, :nat, "n", :typ},
      body: {:def, "IsEven"}
    }

    as_evid = %{
      name: "bad_evid",
      mode: :evidence,
      type: {:pi, :affine, :nat, "n", :typ},
      body: {:def, "IsEven"}
    }

    assert {:error, r} = Check.check_sig([as_run | Example.book()])
    assert r =~ "promotion"

    assert {:error, e} = Check.check_sig([as_evid | Example.book()])
    assert e =~ "promotion"
  end

  test "evidence never becomes a run" do
    book = [
      %{
        name: "bad",
        mode: :run,
        export: true,
        type: :nat,
        body: {:def, "half_ok"}
      }
    ]

    assert {:error, msg} = Check.check_sig(book ++ Example.book())
    assert msg =~ "promotion"
  end

  test "forbidden tags are rejected" do
    for tag <- ["live", "dead", "proof", "proof evidence", "ghost", "comp", "export"] do
      assert {:error, msg} = Parser.parse("def x : #{tag} Nat := 0")
      assert msg =~ "rejected tag" or msg =~ "expected"
    end
  end

  test "emitted half of eight is four" do
    src = Emit.emit_module(Muro.NatLive, Example.book())
    Code.eval_string(src)
    eight = Enum.reduce(1..8, 0, fn _, n -> {:suc, n} end)
    assert Muro.NatLive.half(eight) == {:suc, {:suc, {:suc, {:suc, 0}}}}
  end
end
