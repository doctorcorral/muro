defmodule Muro.MixProject do
  use Mix.Project

  def project do
    [
      app: :muro,
      version: "0.1.0",
      elixir: "~> 1.15",
      start_permanent: Mix.env() == :prod,
      deps: deps(),
      elixirc_paths: elixirc_paths(Mix.env())
    ]
  end

  def application do
    [extra_applications: [:logger]]
  end

  defp elixirc_paths(_), do: ["lib"]

  defp deps do
    [{:nx, "~> 0.9"}]
  end
end
