defmodule Muro do
  @moduledoc """
  Muro — a proof never becomes a run.

  An explicit affine dependent type theory: Elixir checks it, Agda specifies
  it, only run terms run.
  """

  alias Muro.{Check, Emit, Parser}

  def check_file(path) do
    path
    |> File.read!()
    |> Parser.parse()
    |> case do
      {:ok, book} -> Check.check_sig(book)
      other -> other
    end
  end

  def emit_file(path, module) when is_atom(module) do
    with {:ok, book} <- Parser.parse(File.read!(path)),
         :ok <- Check.check_sig(book) do
      {:ok, Emit.emit_module(module, book)}
    end
  end
end
