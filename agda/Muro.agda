------------------------------------------------------------------------
-- Muro — an explicit affine dependent type theory:
-- Elixir checks it, Agda specifies it, only run terms run.
------------------------------------------------------------------------

module Muro where

open import Muro.Base public
open import Muro.Syntax public
open import Muro.Subst public
open import Muro.Check public
import Muro.Judgement
import Muro.Wall
import Muro.Consistency
open import Muro.Example public
open import Muro.ExampleStream public
import Muro.ExampleEither
import Muro.ExampleAlways
import Muro.ExampleBisim
import Muro.ExampleList
import Muro.ExampleVec
import Muro.ExampleNx
