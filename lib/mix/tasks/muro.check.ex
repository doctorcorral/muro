defmodule Mix.Tasks.Muro.Check do
  use Mix.Task

  @shortdoc "Type-check a .muro file or the built-in half_ok book"

  def run([]) do
    Mix.Task.run("app.start")

    case Muro.Check.check_sig(Muro.Example.book()) do
      :ok -> Mix.shell().info("All terms check. Evidence never becomes a run.")
      {:error, e} -> Mix.raise(e)
    end
  end

  def run([path]) do
    Mix.Task.run("app.start")

    case Muro.check_file(path) do
      :ok -> Mix.shell().info("All terms check. Evidence never becomes a run.")
      {:error, e} -> Mix.raise(e)
    end
  end
end
