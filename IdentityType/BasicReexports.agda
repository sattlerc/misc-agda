{-# OPTIONS --rewriting --confluence-check --double-check --postfix-projections #-}
module IdentityType.BasicReexports where

open import Basics
open import Families
open import IdentityType.Specification
open import IdentityType.Inversion

-- Helper module.
-- Re-exports common elimination variants and their dual versions with endpoints swapped.
module SymbolsElim {C D : Family} {C-intro : Intro C} (C-elim : Elim C-intro C) (C-elim-D : Elim C-intro D) where
  open Family C public
  open Intro C-intro public
  open Elim' C-elim-D public
  open Transport (elim-to-transport C-elim-D) public
  open ElimInverse C-elim C-elim-D public

module SymbolsElimSelf {C : Family} {C-intro : Intro C} (C-elim : Elim C-intro C) where
  open SymbolsElim C-elim C-elim public
