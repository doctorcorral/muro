defmodule Muro.CheckTest do
  use ExUnit.Case, async: true

  alias Muro.{Check, Example, Emit}

  test "Muro.Check decides half_ok" do
    assert Check.check_sig(Example.book()) == :ok
  end

  test "no promotion: dead proof is not live" do
    book = [
      %{
        name: "bad",
        mode: :live,
        type: :nat,
        body: {:def, "half_ok"}
      }
    ]

    assert {:error, msg} = Check.check_sig(book ++ Example.book())
    assert msg =~ "promotion" or msg =~ "dead"
  end

  test "emit live plus and half, erase proofs" do
    src = Emit.emit_module(Muro.NatLive, Example.book())
    assert src =~ "def plus"
    assert src =~ "def half"
    refute src =~ "def half_ok"
    refute src =~ "def IsEven"
  end

  test "emitted half of eight is four" do
    src = Emit.emit_module(Muro.NatLive, Example.book())
    Code.eval_string(src)
    eight = Enum.reduce(1..8, 0, fn _, n -> {:suc, n} end)
    assert Muro.NatLive.half(eight) == {:suc, {:suc, {:suc, {:suc, 0}}}}
  end
end
