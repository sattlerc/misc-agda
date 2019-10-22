-- Symmetry of identity types.
-- Assumes elimination of C with respect to itself.
{-# OPTIONS --rewriting --confluence-check --double-check --postfix-projections #-}
module IdentityType.Inversion where

open import Basics
open import Families
open import IdentityType.Specification

module Inverse {C : Family} {C-intro : Intro C} (C-elim : Elim C-intro C) where
  open Family C
  open Intro C-intro
  open Elim' C-elim
  open Transport (elim-to-transport C-elim)

  invert :
    {A : Ty}
    {x y : Tm A}
    (p : Tm (Id x y))
    → ---------------
    Tm (Id y x)

  invert {x = x} {y} p = transport (λ y → Id y x) p r

  invert-β :
    {A : Ty}
    {a : Tm A}
    → ---------------------
    invert (r {a = a}) == r

  invert-β = refl

  invert-invert :
    {A : Ty}
    {x y : Tm A}
    {p : Tm (Id x y)}
    → ---------------------------
    Tm (Id (invert (invert p)) p)

  invert-invert {p = p} = J' (λ y p → Id (invert (invert p)) p) r p

  invert-invert-β :
    {A : Ty}
    {a : Tm A}
    → --------------------------------
    invert-invert {p = r {a = a}} == r

  invert-invert-β = refl

-- Derived elimination operations using inverses.
-- Assumes that C eliminates over itself.
module ElimInverse {C D : Family} {C-intro : Intro C} (C-elim : Elim C-intro C) (C-elim-D : Elim C-intro D) where
  open Family C
  open Family D renaming (Ty to D-Ty; Tm to D-Tm)
  open Intro C-intro
  open Inverse C-elim
  open Elim' C-elim-D
  open Transport (elim-to-transport C-elim-D)

  -- Dual version of J (endpoints swapped).
  J-inv :
    {A : Ty}
    {a : Tm A}
    (P : (x : Tm A) (p : Tm (Id x a)) → D-Ty)
    (d : D-Tm (P a r))
    {x : Tm A}
    (p : Tm (Id x a))
    → ---------------
    D-Tm (P x p)

  J-inv {A} {a} P d {x} p = transport (λ p → P x p) invert-invert (J' (λ x p → P x (invert p)) d (invert p))

  J-inv-β :
    {A : Ty}
    {a : Tm A}
    (P : (x : Tm A) (p : Tm (Id x a)) → D-Ty)
    (d : D-Tm (P a r))
    → ---------------
    J-inv P d r == d

  J-inv-β P d = refl

  transport-inv :
    {A : Ty}
    (P : (a : Tm A) → D-Ty)
    {x y : Tm A}
    (p : Tm (Id x y))
    (d : D-Tm (P y))
    → ---------------------------------------
    D-Tm (P x)

  transport-inv P p d = transport P (invert p) d

  transport-inv-β : 
    {A : Ty}
    (P : (a : Tm A) → D-Ty)
    {a : Tm A}
    (d : D-Tm (P a))
    → ---------------------------------------
    transport P r d == d

  transport-inv-β P d = refl
