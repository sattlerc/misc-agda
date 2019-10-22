-- Symmetry of identity types.
-- Assumes elimination of C with respect to itself.
{-# OPTIONS --rewriting --confluence-check --double-check --postfix-projections #-}
module IdentityType.Respect where

open import Basics
open import Families
open import IdentityType.Specification

module Respect {C D : Family} {C-intro : Intro C} (C-elim-D : Elim C-intro D) (D-intro : Intro D) where
  open Family C
  open Intro C-intro
  open Transport (elim-to-transport C-elim-D)
  open Family D renaming (Ty to D-Ty; Tm to D-Tm)
  open Intro D-intro renaming (Id to D-Id; r to D-r)

  respect :
    {A : Ty}
    {B : D-Ty}
    (f : Tm A → D-Tm B)
    {x y : Tm A}
    (p : Tm (Id x y))
    → ---------------------
    D-Tm (D-Id (f x) (f y))

  respect f {x} p = transport (λ y → D-Id (f x) (f y)) p D-r

  respect-β :
    {A : Ty}
    {B : D-Ty}
    (f : Tm A → D-Tm B)
    {a : Tm A}
    → --------------------------
    respect f (r {a = a}) == D-r

  respect-β f = refl
