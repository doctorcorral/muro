defmodule Muro.Application do
  @moduledoc false

  use Application

  @impl true
  def start(_type, _args) do
    Makeup.Registry.register_lexer(Muro.MakeupLexer,
      names: ["muro"],
      extensions: ["muro"]
    )

    Supervisor.start_link([], strategy: :one_for_one, name: Muro.Supervisor)
  end
end
