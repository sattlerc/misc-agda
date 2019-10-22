-- Symmetry of identity types.
-- Assumes elimination of C with respect to itself.
{-# OPTIONS --rewriting --confluence-check --double-check --postfix-projections #-}
module IdentityType.TransportCoherence where

open import Basics
open import Families
open import IdentityType.Specification
open import IdentityType.BasicReexports
open import IdentityType.HigherGroupoidStructure

module TransportCoherence {C D : Family} {C-intro : Intro C} (C-elim : Elim C-intro C) (C-elim-D : Elim C-intro D) (D-intro : Intro D) where
  open SymbolsElim C-elim C-elim-D
  open Family D renaming (Ty to D-Ty; Tm to D-Tm)
  open Intro D-intro renaming (Id to D-Id; r to D-r)
  open HigherGroupoidStructure C-elim

  transport-comp :
    {A : Ty}
    (P : (a : Tm A) → D-Ty)
    {x y z : Tm A}
    {p : Tm (Id x y)}
    {q : Tm (Id y z)}
    {d : D-Tm (P x)}
    → ---------------------
    D-Tm (D-Id (transport P q (transport P p d)) (transport P (compose p q) d))

  transport-comp P {p = p} {q} {d} = J' (λ z q → D-Id (transport P q (transport P p d)) (transport P (compose p q) d)) D-r q
