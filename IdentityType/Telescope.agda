{-# OPTIONS --rewriting --confluence-check --double-check --postfix-projections #-}
module Frobenius.IdentityType.Telescope where

open import Frobenius.Basics
open import Frobenius.Families
open import Frobenius.IdentityType.Specification
open import Frobenius.IdentityType.DerivedFixedTarget

module Telescope {C : Family} {C-intro : Intro C} (C-elim : Elim C-intro C) where
  open Family C
  open Intro C-intro

  private
    C* = FamilyOps.star C

  manyfold-intro : (n : ℕ) → Intro (FamilyOps.manyfold C n)
  manyfold-elim-C : (n : ℕ) → Elim (manyfold-intro n) C

  manyfold-intro O = IntroOps.unit
  manyfold-intro (S n) = IntroOps.join (manyfold-intro n) C-intro (manyfold-elim-C n)

  manyfold-elim-C O = ElimOpsFixedTarget.unit
  manyfold-elim-C (S n) = ElimOpsFixedTarget.join (manyfold-elim-C n) (manyfold-elim-C n) C-elim

  star-intro : Intro C*
  star-intro = IntroOps.∐ manyfold-intro

  star-elim-C : Elim star-intro C
  star-elim-C = ElimOpsFixedTarget.∐ manyfold-elim-C

  C-elim-manyfold : (n : ℕ) → Elim C-intro (FamilyOps.manyfold C n)
  C-elim-manyfold O = ElimOpsFixedSource.unit
  C-elim-manyfold (S n) = ElimOpsFixedSource.join (C-elim-manyfold n) C-elim

  module _ {D : Family} (C-elim-D : Elim C-intro D) where
    manyfold-elim-D : (n : ℕ) → Elim (manyfold-intro n) D
    manyfold-elim-D O = ElimOpsFixedTarget.unit
    manyfold-elim-D (S n) = ElimOpsFixedTarget.join (manyfold-elim-C n) (manyfold-elim-D n) C-elim-D

    star-elim-D : Elim star-intro D
    star-elim-D = ElimOpsFixedTarget.∐ manyfold-elim-D

  -- Needs representablity of C.
  module _ (C-rep : IsRepresentable C) where
    C-elim-star : Elim C-intro C*
    C-elim-star = ElimOpsFixedSource.∐ C-rep C-elim-manyfold

    -- Telescopes eliminate over themselves.
    star-elim-star : Elim star-intro C*
    star-elim-star = star-elim-D C-elim-star
