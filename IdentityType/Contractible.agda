{-# OPTIONS --rewriting --confluence-check --double-check --postfix-projections #-}
module Frobenius.IdentityType.Contractible where

open import Frobenius.Basics
open import Frobenius.Families
open import Frobenius.IdentityType.Specification
open import Frobenius.IdentityType.Inversion
open import Frobenius.IdentityType.BasicReexports
open import Frobenius.IdentityType.Respect
open import Frobenius.IdentityType.DerivedFixedTarget
open import Frobenius.IdentityType.HigherGroupoidStructure
open import Frobenius.IdentityType.TransportCoherence

module ContractibilityDefs {C : Family} (C-intro : Intro C) where
  open Family C
  open Intro C-intro

  record IsContractible (A : Ty) : Set where
    field
      center : Tm A
      spoke : (a : Tm A) → Tm (Id center a)

  record HasAllPaths (A : Ty) : Set where
    field
      all-paths : {x y : Tm A} → Tm (Id x y)

  record IsProposition (A : Ty) : Set where
    field
      contractible-homs : {x y : Tm A} → IsContractible (Id x y)

module Contractibility {C : Family} {C-intro : Intro C} (C-elim : Elim C-intro C) where
  open SymbolsElimSelf C-elim
  open HigherGroupoidStructure C-elim
  open ContractibilityDefs C-intro 

  module _ {A : Ty} where
    contractible-has-all-paths : (contr : IsContractible A) → HasAllPaths A
    contractible-has-all-paths contr .HasAllPaths.all-paths {x} {y} = compose (invert (spoke x)) (spoke y) where
      open IsContractible contr

    all-paths-is-proposition : (paths : HasAllPaths A) → IsProposition A
    all-paths-is-proposition paths .IsProposition.contractible-homs {x} {y} = λ where
      .center → compose (all-paths {x} {y}) (invert $ all-paths {y} {y})
      .spoke p → J' (λ y p → Id (compose (all-paths {x} {y}) (invert $ all-paths {y} {y})) p) (compose-invert-r {p = all-paths {x} {x}}) p where
      open IsContractible
      open HasAllPaths paths

    contractible-is-proposition : (contr : IsContractible A) → IsProposition A
    contractible-is-proposition contr = all-paths-is-proposition $ contractible-has-all-paths contr

module TransportContr {C D : Family} {C-intro : Intro C} (C-elim : Elim C-intro C) (C-elim-D : Elim C-intro D) {D-intro : Intro D} (D-elim : Elim D-intro D) where
  open Family D renaming (Ty to D-Ty; Tm to D-Tm)
  open Intro D-intro renaming (Id to D-Id; r to D-r)
  open SymbolsElim C-elim C-elim-D
  open ContractibilityDefs C-intro
  open Contractibility C-elim
  open Respect C-elim-D D-intro
  open TransportCoherence C-elim C-elim-D D-intro
  private module CG = HigherGroupoidStructure C-elim
  private module DG = HigherGroupoidStructure D-elim

  module _ {A : Ty} (A-contr : IsContractible A) (P : (a : Tm A) → D-Ty) where
    open HasAllPaths (contractible-has-all-paths A-contr)
    open IsProposition (contractible-is-proposition A-contr)
    module Hom {x} {y} = HasAllPaths (contractible-has-all-paths $ contractible-homs {x} {y})

    transport-contr :
      {x : Tm A}
      (y : Tm A)
      (d : D-Tm (P x))
      → ---------------------------------------
      D-Tm (P y)

    transport-contr {x} y d = transport P all-paths d

    transport-contr-eq :
      {x y : Tm A}
      {p₁ p₂ : Tm (Id x y)}
      {d : D-Tm (P x)}
      → -----------------------------------------------
      D-Tm $ D-Id (transport P p₁ d) (transport P p₂ d)

    transport-contr-eq {d = d} = respect (λ p → transport P p d) Hom.all-paths where

    transport-contr-id :
      {x : Tm A}
      {d : D-Tm (P x)}
      → -----------------------------------------
      D-Tm $ D-Id (transport-contr x d) d

    transport-contr-id {x} {d} = transport-contr-eq {p₁ = all-paths} {p₂ = r}

    transport-contr-comp :
      {x y z : Tm A}
      (d : D-Tm (P x))
      → -----------------------
      D-Tm $ D-Id (transport-contr z (transport-contr y d)) (transport-contr z d)

    transport-contr-comp {x} {y} d = DG.compose (transport-comp P {x = x} {y = y}) (transport-contr-eq {x = x})

module Singleton {C : Family} {C-intro : Intro C} (C-elim : Elim C-intro C) where
  open Family C
  open Intro C-intro
  open Elim' C-elim
  open Transport (elim-to-transport C-elim)
  open Inverse C-elim
  open ElimInverse C-elim C-elim

  private C-C = C FamilyOps.• C
  private C-C-intro = IntroOps.join C-intro C-intro C-elim

  open ContractibilityDefs C-C-intro 
  open IsContractible

  singleton-from-is-contr : {A : Ty} (a : Tm A) → IsContractible (A , (λ x → Id a x))
  singleton-from-is-contr a = λ where
    .center → (a , r)
    .spoke (x , p) → (p , J' (λ x p → Id (transport (λ x → Id a x) p r) p) r p)

  singleton-to-is-contr : {A : Ty} (a : Tm A) → IsContractible (A , (λ x → Id x a))
  singleton-to-is-contr a = λ where
    .center → (a , r)
    .spoke (x , p) → (invert p , J-inv (λ x p → Id (transport (λ x → Id x a) (invert p) r) p) r p)
