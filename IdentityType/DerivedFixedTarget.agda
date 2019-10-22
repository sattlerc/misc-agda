{-# OPTIONS --rewriting --confluence-check --double-check --postfix-projections #-}
module IdentityType.DerivedFixedTarget where

open import Basics
open import Families
open import IdentityType.Specification

module IntroOps where
  open Family
  private module F = FamilyOps
  open Intro
  open Elim

  ∐ :
    {Z : Set}
    {C : Z → Family}
    (C-intro : (z : Z) → Intro (C z))
    → -------------------------------
    Intro (F.∐ C)

  ∐ C-intro  = λ where
    .Id x y → (_ , C-intro _ .Id x y)
    .r → C-intro _ .r

  ---------------------------------
  unit : Intro FamilyOps.unit

  unit .Id tt tt = tt
  unit .r = tt

  join :
    {C₁ C₂ : Family}
    (C₁-intro : Intro C₁)
    (C₂-intro : Intro C₂)
    (C₁-elim-C₂ : Elim C₁-intro C₂)
    → -------------------------
    Intro (C₁ F.• C₂)

  join {C₁} {C₂} C₁-intro C₂-intro C₁-elim-C₂ = h where
    open Transport (elim-to-transport C₁-elim-C₂)

    h : Intro (C₁ F.• C₂)
    h .Id (x₁ , x₂) (y₁ , y₂) .fst = C₁-intro .Id x₁ y₁
    h .Id {A = (A₁ , A₂)} (x₁ , x₂) (y₁ , y₂) .snd p₁ = C₂-intro .Id (transport A₂ p₁ x₂) y₂
    h .r .fst = C₁-intro .r
    h .r .snd = C₂-intro .r

module ElimOpsFixedTarget {D : Family} where
  open Intro
  open Elim
  open Elim'

  ∐ :
    {Z : Set}
    {C : Z → Family}
    {C-intro : (z : Z) → Intro (C z)}
    (C-elim : (z : Z) → Elim (C-intro z) D)
    → -------------------------------------
    Elim (IntroOps.∐ C-intro) D

  ∐ C-elim = λ where
    .J P d p → C-elim _ .J P d p
    .J-β P d → C-elim _ .J-β P d

  ---------------------------
  unit : Elim IntroOps.unit D

  unit .J C d tt = d
  unit .J-β C d = refl

  join :
    {C₁ C₂ : Family}
    {C₁-intro : Intro C₁}
    {C₂-intro : Intro C₂}
    (C₁-elim-C₂ : Elim C₁-intro C₂)
    (C₁-elim-D : Elim C₁-intro D)
    (C₂-elim-D : Elim C₂-intro D)
    → -------------------------------------------
    Elim (IntroOps.join C₁-intro C₂-intro C₁-elim-C₂) D

  join {C₁} {C₂} {C₁-Intro} {C₂-Intro} C₁-Elim-C₂ C₁-Elim-D C₂-Elim-D = h where
    h : Elim (IntroOps.join C₁-Intro C₂-Intro C₁-Elim-C₂) D
    h .J {A = (A₁ , A₂)} C d (p₁ , p₂) = d'' where
      d'  = J' C₁-Elim-D (λ x₁ p₁ → C _ (p₁ , C₂-Intro .r)) d p₁
      d'' = J' C₂-Elim-D (λ x₂ p₂ → C _ (p₁ , p₂)) d' p₂
    h .J-β C d = refl

module ElimOpsFixedSource {C : Family} {C-intro : Intro C} where
  open Family C
  open Intro C-intro
  open Elim
  open Elim'

  -- Only valid for discrete index types (like ℕ here).
  module _ 
    (rep : IsRepresentable C)
    {D : ℕ → Family}
    (elim-D : (n : ℕ) → Elim C-intro (D n))
    where
    open Family (FamilyOps.∐ D) renaming (Ty to ∐-Ty; Tm to ∐-Tm)

    private
     module _ {A : Ty} {a : Tm A} where
      record Modular
        (P : Σ (Tm A) (λ x → Tm (Id a x)) → ∐-Ty)
        (d : ∐-Tm $ P (a , r)) : Set where
        field
          my-J : (z : Σ (Tm A) (λ x → Tm (Id a x))) → ∐-Tm (P z)
          my-J-β : my-J (a , r) == d
      open Modular

      module _
        (P' : Σ ℕ (λ n → Σ (Tm A) (λ x → Tm (Id a x)) → D n .Family.Ty)) where

        n = P' .fst

        P : Σ (Tm A) (λ x → Tm (Id a x)) → ∐-Ty
        P z = (n , P' .snd z)

        easy : (d : ∐-Tm (P (a , r))) → Modular P d
        easy d .my-J (x , p) = J' (elim-D n) (λ x p → P' .snd (x , p)) d p
        easy d .my-J-β = refl

      derived : (P : Σ (Tm A) (λ x → Tm (Id a x)) → ∐-Ty) (d : ∐-Tm (P (a , r))) → Modular P d
      derived P = transp (λ P → (d : ∐-Tm (P (a , r))) → Modular P d) inv-r (easy $ inverse P) where
        open IsRepresentable (FamilyOps.join-representable rep rep)
        open is-iso comparison-iso

    ∐ : Elim C-intro (FamilyOps.∐ D)
    ∐ = λ where
      .J {A} {a} P d {x} p → derived (λ {(x , p) → P x p}) d .my-J (x , p)
      .J-β P d → derived (λ {(x , p) → P x p}) d .my-J-β where
      open Modular

  ----------------------------------
  unit : Elim C-intro FamilyOps.unit

  unit .J C tt p = tt
  unit .J-β C d = refl

  join :
    {D₁ D₂ : Family}
    (elim-D₁ : Elim C-intro D₁)
    (elim-D₂ : Elim C-intro D₂)
    → ------------------------------
    Elim C-intro (D₁ FamilyOps.• D₂)

  join {D₁} {D₂} elim-D₁ elim-D₂ = λ where
    .J P (d₁ , d₂) p .fst → J' elim-D₁ _ d₁ p
    .J P (d₁ , d₂) p .snd → J' elim-D₂ (λ x p → P x p .snd (J' elim-D₁ _ d₁ p)) d₂ p
    .J-β P (d₁ , d₂) → refl
