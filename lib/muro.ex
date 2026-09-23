defmodule Muro do
  @moduledoc """
  Muro — a spec never becomes evidence. Evidence never becomes a run.

  An explicit affine dependent type theory: Elixir checks it, Agda specifies
  it, only run terms run.
  """

  alias Muro.{Check, Emit, Parser}

  @doc "Parse and check a `.muro` file. Options: `fuel: n` (see `Muro.Check.check_sig/2`)."
  def check_file(path, opts \\ []) do
    path
    |> File.read!()
    |> Parser.parse()
    |> case do
      {:ok, book} -> Check.check_sig(book, opts)
      other -> other
    end
  end

  def emit_file(path, module, opts \\ []) when is_atom(module) do
    with {:ok, book} <- Parser.parse(File.read!(path)),
         :ok <- Check.check_sig(book, opts) do
      {:ok, Emit.emit_module(module, book)}
    end
  end
end
