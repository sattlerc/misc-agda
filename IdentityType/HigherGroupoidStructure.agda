{-# OPTIONS --rewriting --confluence-check --double-check --postfix-projections #-}
module Frobenius.IdentityType.HigherGroupoidStructure where

open import Frobenius.Basics
open import Frobenius.Families
open import Frobenius.IdentityType.Specification
open import Frobenius.IdentityType.Inversion
open import Frobenius.IdentityType.BasicReexports

-- Higher groupoid structure of identity types.
-- Assumes elimination of C with respect to itself.
-- Re-exports inversion.
module HigherGroupoidStructure {C : Family} {C-intro : Intro C} (C-elim : Elim C-intro C) where
  open SymbolsElimSelf C-elim
  open Inverse C-elim public

  compose :
    {A : Ty}
    {x y z : Tm A}
    (p : Tm (Id x y))
    (q : Tm (Id y z))
    → ---------------
    Tm (Id x z)

  compose {x = x} {y} {z} p q = transport (λ z → Id x z) q p

  compose-β :
    {A : Ty}
    {x y : Tm A}
    (p : Tm (Id x y))
    → ---------------
    compose p r == p

  compose-β p = refl

  compose-neut-l :
    {A : Ty}
    {x y : Tm A}
    {p : Tm (Id x y)}
    → ---------------------
    Tm (Id (compose r p) p)

  compose-neut-l {p = p} = J' (λ y p → Id (compose r p) p) r p

  compose-invert-r :
    {A : Ty}
    {x y : Tm A}
    {p : Tm (Id x y)}
    → ---------------
    Tm (Id (compose p (invert p)) r)

  compose-invert-r {p = p} = J' (λ y p → Id (compose p (invert p)) r) r p

  compose-invert-r-β :
    {A : Ty}
    {a : Tm A}
    → -----------------------------------
    compose-invert-r {p = r {a = a}} == r

  compose-invert-r-β = refl

  compose-invert-l :
    {A : Ty}
    {x y : Tm A}
    {p : Tm (Id x y)}
    → ---------------
    Tm (Id (compose (invert p) p) r)

  compose-invert-l {p = p} = J' (λ y p → Id (compose (invert p) p) r) r p

  compose-invert-l-β :
    {A : Ty}
    {a : Tm A}
    → -----------------------------------
    compose-invert-l {p = r {a = a}} == r

  compose-invert-l-β = refl

  assoc :
    {A : Ty}
    {w x y z : Tm A}
    {o : Tm (Id w x)}
    {p : Tm (Id x y)}
    {q : Tm (Id y z)}
    → ----------------
    Tm (Id (compose (compose o p) q) (compose o (compose p q)))

  assoc {o = o} {p} {q} = J' (λ z q → Id (compose (compose o p) q) (compose o (compose p q))) r q

  assoc-β :
    {A : Ty}
    {w x y z : Tm A}
    {o : Tm (Id w x)}
    {p : Tm (Id x y)}
    → ------------------------
    assoc {o = o} {p} {r} == r

  assoc-β = refl
