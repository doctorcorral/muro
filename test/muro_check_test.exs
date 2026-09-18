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

  test "a proof never becomes a run" do
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
    assert msg =~ "promotion" or msg =~ "proof"
  end

  test "emit plus and half as def; omit proofs" do
    src = Emit.emit_module(Muro.NatLive, Example.book())
    assert src =~ ~r/\bdef plus\b/
    assert src =~ ~r/\bdef half\b/
    refute src =~ "def half_ok"
    refute src =~ "def IsEven"
    refute src =~ "plus_suc"
  end

  test "run internal helper is defp" do
    assert {:ok, book} = Parser.parse(File.read!("examples/internal_ok.muro"))
    assert Check.check_sig(book) == :ok
    src = Emit.emit_module(Muro.InternalOk, book)
    assert src =~ ~r/\bdefp step\b/
    assert src =~ ~r/\bdef inc\b/
    refute src =~ ~r/\bdef step\b/
  end

  test "emitted half of eight is four" do
    src = Emit.emit_module(Muro.NatLive, Example.book())
    Code.eval_string(src)
    eight = Enum.reduce(1..8, 0, fn _, n -> {:suc, n} end)
    assert Muro.NatLive.half(eight) == {:suc, {:suc, {:suc, {:suc, 0}}}}
  end
end
