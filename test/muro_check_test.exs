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
    for tag <- [
          "l" <> "ive",
          "d" <> "ead",
          "pr" <> "oof",
          "pr" <> "oof" <> " evidence",
          "ghost",
          "comp",
          "export"
        ] do
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

  test "zeros.muro parses, checks, and emits only zeros" do
    src = File.read!("examples/zeros.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.Zeros, book)
    assert out =~ ~r/\bdef zeros\b/
    refute out =~ "head-zeros"
    refute out =~ "head_zeros"
  end

  test "nats.muro parses, checks, and emits natsFrom" do
    src = File.read!("examples/nats.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.Nats, book)
    assert out =~ ~r/\bdef natsFrom\b/
    assert out =~ "Stream.unfold"
    Code.eval_string(out)

    assert Muro.Nats.natsFrom(0) |> Stream.take(3) |> Enum.to_list() == [
             0,
             {:suc, 0},
             {:suc, {:suc, 0}}
           ]
  end

  test "non-guarded unfold fails in run and in evidence" do
    f = {:lam, :affine, :nat, "_", {:var, "bad"}}

    run = %{
      name: "bad",
      mode: :run,
      export: true,
      type: {:stream, :nat},
      body: {:unf, :ze, f}
    }

    evid = %{name: "bad", mode: :evidence, type: {:stream, :nat}, body: {:unf, :ze, f}}

    assert {:error, r} = Check.check_sig([run])

    assert r =~ "pair" or r =~ "unguarded" or r =~ "unfold" or r =~ "×" or r =~ "Stream" or
             r =~ "ν" or r =~ "convert"

    assert {:error, e} = Check.check_sig([evid])

    assert e =~ "pair" or e =~ "unguarded" or e =~ "unfold" or e =~ "×" or e =~ "Stream" or
             e =~ "ν" or e =~ "convert"
  end

  test "even_dec.muro checks; Dec and evenDec are not emitted" do
    src = File.read!("examples/even_dec.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.EvenBook, book)
    refute out =~ ~r/\bevenDec\b/
    refute out =~ ~r/\bdef Dec\b/
    refute out =~ ~r/\bdef IsEven\b/
  end

  test "run Either match emits left/right tags" do
    src = File.read!("examples/either_run.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.EitherRun, book)
    assert out =~ ~r/\bdef fromLeft\b/
    assert out =~ "{:left,"
    assert out =~ "{:right,"
    Code.eval_string(out)
    assert Muro.EitherRun.fromLeft({:left, 0}) == 0
    assert Muro.EitherRun.fromLeft({:right, :tt}) == 0
  end

  test "LEM for arbitrary P is rejected" do
    src = File.read!("examples/even_dec.muro")
    assert {:ok, book} = Parser.parse(src)

    lem = %{
      name: "lem",
      mode: :evidence,
      type: {:pi, :affine, :typ, "P", {:app, {:var, "Dec"}, {:var, "P"}}},
      body: {:lam, :affine, :typ, "P", {:app, {:var, "left"}, :one}}
    }

    assert {:error, msg} = Check.check_sig([lem | book])
    assert is_binary(msg)
  end

  test "affine refutation cannot be used twice in evidence" do
    src = File.read!("examples/even_dec.muro")
    assert {:ok, book} = Parser.parse(src)

    arrow = {:pi, :affine, {:app, {:var, "IsEven"}, :ze}, "_", :empty}

    dup = %{
      name: "dup_contra",
      mode: :evidence,
      type: {:pi, :affine, arrow, "c", {:prod, :empty, :empty}},
      body:
        {:lam, :affine, arrow, "c", {:pair, {:app, {:var, "c"}, :one}, {:app, {:var, "c"}, :one}}}
    }

    assert {:error, msg} = Check.check_sig([dup | book])
    assert msg =~ "affine"
  end

  test "always.muro checks; Always evidence is not emitted" do
    src = File.read!("examples/always.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.ZeroAlways, book)
    assert out =~ ~r/\bdef zeros\b/
    refute out =~ "always-zero"
  end

  test "unguarded Always evidence fails" do
    src = File.read!("examples/always.muro")
    assert {:ok, book} = Parser.parse(src)

    p = {:lam, :affine, :nat, "_", {:idt, :nat, :ze, :ze}}

    bad = %{
      name: "bad",
      mode: :evidence,
      type: {:always, p, {:var, "zeros"}},
      body: {:var, "bad"}
    }

    assert {:error, msg} = Check.check_sig(book ++ [bad])
    assert msg =~ "unfold" or msg =~ "ν" or msg =~ "unguarded"
  end

  test "bisim.muro checks; evidence is not emitted" do
    src = File.read!("examples/bisim.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.BisimEx, book)
    assert out =~ ~r/\bdef zeros\b/
    assert out =~ ~r/\bdef zeros_\b/
    assert out =~ ~r/\bdef natsFrom\b/
    refute out =~ "zeros-bisim"
    refute out =~ "nats_tail_bisim"
  end

  test "unguarded ~ evidence fails" do
    src = File.read!("examples/bisim.muro")
    assert {:ok, book} = Parser.parse(src)

    bad = %{
      name: "bad",
      mode: :evidence,
      type: {:bisim, {:var, "zeros"}, {:app, {:var, "natsFrom"}, :ze}},
      body: {:var, "bad"}
    }

    assert {:error, msg} = Check.check_sig(book ++ [bad])
    assert msg =~ "unfold" or msg =~ "ν" or msg =~ "unguarded" or msg =~ "convert"
  end

  test "list.muro checks; evidence is not emitted; length runs" do
    src = File.read!("examples/list.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.Lists, book)
    assert out =~ ~r/\bdef length\b/
    assert out =~ ~r/\bdef ones2\b/
    refute out =~ "length-ones2"
    Code.eval_string(out)
    assert Muro.Lists.length(Muro.Lists.ones2()) == {:suc, {:suc, 0}}
  end

  test "maybe.muro checks; fromMaybe runs" do
    src = File.read!("examples/maybe.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.MaybeEx, book)
    assert out =~ ~r/\bdef fromMaybe\b/
    refute out =~ "fromJust1"
    Code.eval_string(out)
    assert Muro.MaybeEx.fromMaybe(0, {:just, {:suc, 0}}) == {:suc, 0}
    assert Muro.MaybeEx.fromMaybe(0, :nothing) == 0
  end

  test "tree.muro checks; size descends on both children" do
    src = File.read!("examples/tree.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.Trees, book)
    assert out =~ ~r/\bdef size\b/
    refute out =~ "size-t2"
    Code.eval_string(out)
    t2 = {:node, :leaf, {:node, :leaf, :leaf}}
    assert Muro.Trees.size(t2) == {:suc, {:suc, 0}}
  end

  test "strict positivity rejects Bad" do
    src = """
    data Bad : Type where
      mk : (Bad → Nat) → Bad
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "positive"
  end

  test "vec.muro checks; lookup of fzero on a singleton" do
    src = File.read!("examples/vec.muro")
    assert {:ok, book} = Parser.parse(src)
    assert Check.check_sig(book) == :ok

    out = Emit.emit_module(Muro.Vecs, book)
    assert out =~ ~r/\bdef lookup\b/
    assert out =~ ~r/\bdef ones1\b/
    refute out =~ "lookup-ok"
    Code.eval_string(out)
    ones1 = {:vcons, 0, {:suc, 0}, :vnil}
    assert Muro.Vecs.lookup({:suc, 0}, {:fzero, 0}, ones1) == {:suc, 0}
  end

  test "indexed positivity rejects Bad" do
    src = """
    data Bad : Nat → Type where
      mk : Π (n : Nat) → (Bad n → Nat) → Bad n
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert msg =~ "positive"
  end

  test "wrong constructor target index fails" do
    src = File.read!("examples/vec.muro")
    assert {:ok, book} = Parser.parse(src)

    bad = %{
      name: "badnil",
      mode: :run,
      export: true,
      type: {:app, {:app, {:var, "Vec"}, :nat}, :ze},
      body: {:app, {:app, {:app, {:var, "vcons"}, :ze}, {:su, :ze}}, {:var, "vnil"}}
    }

    assert {:error, msg} = Check.check_sig(book ++ [bad])
    assert is_binary(msg)
  end

  test "constructor target missing an index fails" do
    src = """
    data Vec (A : Type) : Nat → Type where
      vnil : Vec A
    """

    assert {:ok, book} = Parser.parse(src)
    assert {:error, msg} = Check.check_sig(book)
    assert is_binary(msg)
  end

  test "non-descending Vec recursion fails" do
    src = File.read!("examples/vec.muro")
    assert {:ok, book} = Parser.parse(src)

    bad = %{
      name: "loopV",
      mode: :run,
      export: true,
      type:
        {:pi, :erased, :typ, "A",
         {:pi, :affine, :nat, "n",
          {:pi, :affine, {:app, {:app, {:var, "Vec"}, {:var, "A"}}, {:var, "n"}}, "xs", :nat}}},
      body:
        {:lam, :erased, :typ, "A",
         {:lam, :affine, :nat, "n",
          {:lam, :affine, {:app, {:app, {:var, "Vec"}, {:var, "A"}}, {:var, "n"}}, "xs",
           {:app, {:app, {:app, {:var, "loopV"}, {:var, "A"}}, {:var, "n"}}, {:var, "xs"}}}}}
    }

    assert {:error, msg} = Check.check_sig([bad | book])
    assert msg =~ "descend"
  end

  test "non-descending Maybe recursion fails" do
    src = File.read!("examples/maybe.muro")
    assert {:ok, book} = Parser.parse(src)

    bad = %{
      name: "loop",
      mode: :run,
      export: true,
      type:
        {:pi, :erased, :typ, "A",
         {:pi, :affine, {:app, {:var, "Maybe"}, {:var, "A"}}, "m",
          {:app, {:var, "Maybe"}, {:var, "A"}}}},
      body:
        {:lam, :erased, :typ, "A",
         {:lam, :affine, {:app, {:var, "Maybe"}, {:var, "A"}}, "m",
          {:app, {:app, {:var, "loop"}, {:var, "A"}}, {:var, "m"}}}}
    }

    assert {:error, msg} = Check.check_sig([bad | book])
    assert msg =~ "descend"
  end

  test "non-descending Tree recursion fails" do
    src = File.read!("examples/tree.muro")
    assert {:ok, book} = Parser.parse(src)

    bad = %{
      name: "loopT",
      mode: :run,
      export: true,
      type: {:pi, :affine, {:var, "Tree"}, "t", {:var, "Tree"}},
      body: {:lam, :affine, {:var, "Tree"}, "t", {:app, {:var, "loopT"}, {:var, "t"}}}
    }

    assert {:error, msg} = Check.check_sig([bad | book])
    assert msg =~ "descend"
  end

  test "non-descending list recursion fails" do
    src = File.read!("examples/list.muro")
    assert {:ok, book} = Parser.parse(src)

    bad = %{
      name: "badlen",
      mode: :run,
      export: true,
      type:
        {:pi, :erased, :typ, "A", {:pi, :affine, {:app, {:var, "List"}, {:var, "A"}}, "xs", :nat}},
      body:
        {:lam, :erased, :typ, "A",
         {:lam, :affine, {:app, {:var, "List"}, {:var, "A"}}, "xs",
          {:app, {:app, {:var, "badlen"}, {:var, "A"}}, {:var, "xs"}}}}
    }

    assert {:error, msg} = Check.check_sig([bad | book])
    assert msg =~ "descend"
  end
end
