module Machine.Theory where

open import Agda.Primitive
import Lib.Basic as lib

open import Model.Shallow
open import Model.Context
open import Model.Labels
open import Model.Stack

open import Machine.Value
open import Machine.Config
open import Machine.Step

open lib using (ℕ; _+_)
open LCon


