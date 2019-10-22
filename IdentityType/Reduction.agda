{-# OPTIONS --rewriting --confluence-check --double-check --postfix-projections #-}
module IdentityType.Reduction where

open import Basics
open import Families
open import IdentityType.Specification
open import IdentityType.Inversion
open import IdentityType.BasicReexports
open import IdentityType.Respect
open import IdentityType.DerivedFixedTarget
open import IdentityType.HigherGroupoidStructure
open import IdentityType.TransportCoherence
open import IdentityType.Contractible
open import IdentityType.Telescope 

-- The Paulin-Mohring eliminator implies the Martin-Loef eliminator.
module ElimMLFrobFromElimFrob
  {C Q D : Family} {C-intro : Intro C}
  (C-elim-frob-Q-D : ElimFrob C-intro Q D) where

  private module PM = ElimFrob C-elim-frob-Q-D
  open ElimMLFrob

  elim : ElimMLFrob C-intro Q D
  elim = λ where
    .J T P d {x} p t → PM.J (T x) (P x) (d x) p t
    .J-β T P d a t → PM.J-β (T a) (P a) (d a) t where
    open ElimMLFrob

-- The Paulin-Mohring eliminator implies the Paulin-Mohring eliminator.
-- I learned this from András Kovács and Rafaël Bocquet.
module ElimFrobFromElim
  {C Q D : Family}
  {C-intro : Intro C} {Q-intro : Intro Q}
  (C-elim : Elim C-intro C) (C-elim-Q : Elim C-intro Q) (C-elim-D : Elim C-intro D)
  (Q-elim : Elim Q-intro Q) (Q-elim-D : Elim Q-intro D) where

  open Family C
  open Family Q renaming (Ty to Q-Ty; Tm to Q-Tm)
  open Family D renaming (Ty to D-Ty; Tm to D-Tm)
  open Intro C-intro
  private module C-Q = SymbolsElim C-elim C-elim-Q
  private module C-D = SymbolsElim C-elim C-elim-D
  private module Q-D = SymbolsElim Q-elim Q-elim-D
  open Singleton C-elim
  open ElimFrob

  private CC = C FamilyOps.• C
  open Family CC renaming (Ty to CC-Ty; Tm to CC-Tm)
  private CC-intro = IntroOps.join C-intro C-intro C-elim
  private CC-elim-C = ElimOpsFixedTarget.join C-elim C-elim C-elim
  private CC-elim = ElimOpsFixedSource.join CC-elim-C CC-elim-C
  open Contractibility CC-elim
  private CC-elim-Q = ElimOpsFixedTarget.join C-elim C-elim-Q C-elim-Q
  private module CC-Q = SymbolsElim CC-elim CC-elim-Q
  private CC-elim-D = ElimOpsFixedTarget.join C-elim C-elim-D C-elim-D
  private module CC-D = SymbolsElim CC-elim CC-elim-D
  open ContractibilityDefs CC-intro
  open TransportContr CC-elim CC-elim-Q Q-elim

  elim : ElimFrob C-intro Q D
  elim .J {A} {a} T P d {x} p t = result where
    -- First, we translate the problem to CC.
    A' : CC-Ty
    A' = (A , (λ x → Id a x))

    z₀ : CC-Tm A'
    z₀ = (a , r)

    z₁ : CC-Tm A'
    z₁ = (x , p)

    T' : (z : CC-Tm A') → Q-Ty
    T' (x , p) = T x p

    P' : (z : CC-Tm A') (t : Q-Tm (T' z)) → D-Ty
    P' (x , p) t = P x p t

    -- Here, it is just a transport over a contractible type.
    c : IsContractible A'
    c = singleton-from-is-contr a

    open IsContractible c
    open HasAllPaths (contractible-has-all-paths c)

    -- Now it is trivial.
    t₀ : Q-Tm (T' z₀)
    t₀ = transport-contr c T' _ t

    d₁ : D-Tm $ P' z₁ (transport-contr c T' z₁ t)
    d₁ = CC-D.transport (λ z → P' z (transport-contr c T' z t)) (all-paths {z₀} {z₁}) (d t₀)

    result : D-Tm (P' z₁ t)
    result = Q-D.transport (P' z₁) (transport-contr-id c T') d₁

  elim .J-β T P d t = refl

-- Telescope version of the reduction.
-- Needs representability of C.
module ElimTeleFrobFromElim
  {C D : Family}
  (C-rep : IsRepresentable C)
  {C-intro : Intro C}
  (C-elim : Elim C-intro C) (C-elim-D : Elim C-intro D) where

  open Telescope C-elim

  elim : ElimFrob C-intro (FamilyOps.star C) D
  elim = ElimFrobFromElim.elim C-elim (C-elim-star C-rep) C-elim-D (star-elim-star C-rep) (star-elim-D C-elim-D)
