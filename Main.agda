module Main where

{- Lib -}
import Lib.Basic as b
import Lib.Order

{- Model: shallow-embedded syntax -}
import Model.Universe
import Model.Shallow
import Model.Context
import Model.Stack

{- SECD: Dependent SECD Machine -}
import SECD.Syntax
import SECD.Value
import SECD.Config
import SECD.Opsem

import SECD.Theorem.Progress
import SECD.Theorem.Halting
import SECD.Theorem.Fundamental
import SECD.Theorem.Termination

import SECD.Main

{- DAM : Dependent Assembly Machine -} 
import DAM.Labels
import DAM.Syntax
import DAM.Value
import DAM.Config
import DAM.Opsem

import DAM.Theorem.Progress
import DAM.Theorem.Halting
import DAM.Theorem.Fundamental
import DAM.Theorem.Termination

import DAM.Main
