-- Specifications of various kinds of identity types.
{-# OPTIONS --rewriting --confluence-check --double-check --postfix-projections #-}
module IdentityType.Specification where

open import Basics
open import Families

-- Type former and constructor for identity type.
record Intro (C : Family) : Set where
  open Family C
  field
    Id :
      {A : Ty}
      (x y : Tm A)
      → ----------
      Ty

    r :
      {A : Ty}
      {a : Tm A}
      → ---------
      Tm (Id a a)

-- Paulin-Mohring eliminator.
-- Parametrized over family for elimination target.
record Elim {C : Family} (C-intro : Intro C) (D : Family) : Set where
  open Family C
  open Intro C-intro
  open Family D renaming (Ty to D-Ty; Tm to D-Tm)
  field
    J :
      {A : Ty}
      {a : Tm A}
      (P : (x : Tm A) (p : Tm (Id a x)) → D-Ty)
      (d : D-Tm (P a r))
      {x : Tm A}
      (p : Tm (Id a x))
      → ---------------
      D-Tm (P x p)

    J-β :
      {A : Ty}
      {a : Tm A}
      (P : (x : Tm A) (p : Tm (Id a x)) → D-Ty)
      (d : D-Tm (P a r))
      → -----------------------
      J P d r == d

-- Duplicate of Pauling-Mohring eliminator that computes.
module Elim' {C : Family} {C-intro : Intro C} {D : Family} (C-elim-D : Elim C-intro D) where
  open Family C
  open Intro C-intro
  open Family D renaming (Ty to D-Ty; Tm to D-Tm)
  open Elim (abstract-center (singleton-contr C-elim-D) .fst) renaming (J to J'; J-β to J'-β) public
  {-# REWRITE J'-β #-}

-- variant of Paulin-Mohring eliminator.
-- Parametrized over two families, one for parameters and one for elimination target.
record ElimFrob {C : Family} (C-intro : Intro C) (Q D : Family) : Set where
  open Family C
  open Intro C-intro
  open Family Q renaming (Ty to Q-Ty; Tm to Q-Tm)
  open Family D renaming (Ty to D-Ty; Tm to D-Tm)
  field
    J :
      {A : Ty}
      {a : Tm A}
      (T : (x : Tm A) (p : Tm (Id a x)) → Q-Ty)
      (P : (x : Tm A) (p : Tm (Id a x)) (t : Q-Tm (T x p)) → D-Ty)
      (d : (t : Q-Tm (T a r)) → D-Tm (P a r t))
      {x : Tm A}
      (p : Tm (Id a x))
      (t : Q-Tm (T x p))
      → ------------------
      D-Tm (P x p t)

    J-β :
      {A : Ty}
      {a : Tm A}
      (T : (x : Tm A) (p : Tm (Id a x)) → Q-Ty)
      (P : (x : Tm A) (p : Tm (Id a x)) (t : Q-Tm (T x p)) → D-Ty)
      (d : (t : Q-Tm (T a r)) → D-Tm (P a r t))
      (t : Q-Tm (T a r))
      → ----------------------
      J T P d r t == d t

-- variant of Martin-Loef eliminator.
-- Parametrized over two families, one for parameters and one for elimination target.
record ElimMLFrob {C : Family} (C-intro : Intro C) (Q D : Family) : Set where
  open Family C
  open Intro C-intro
  open Family Q renaming (Ty to Q-Ty; Tm to Q-Tm)
  open Family D renaming (Ty to D-Ty; Tm to D-Tm)
  field
    J :
      {A : Ty}
      (T : (x y : Tm A) (p : Tm (Id x y)) → Q-Ty)
      (P : (x y : Tm A) (p : Tm (Id x y)) (t : Q-Tm (T x y p)) → D-Ty)
      (d : (a : Tm A) (t : Q-Tm (T a a r)) → D-Tm (P a a r t))
      {x y : Tm A}
      (p : Tm (Id x y))
      (t : Q-Tm (T x y p))
      → ------------------
      D-Tm (P x y p t)

    J-β :
      {A : Ty}
      (T : (x y : Tm A) (p : Tm (Id x y)) → Q-Ty)
      (P : (x y : Tm A) (p : Tm (Id x y)) (t : Q-Tm (T x y p)) → D-Ty)
      (d : (a : Tm A) (t : Q-Tm (T a a r)) → D-Tm (P a a r t))
      (a : Tm A)
      (t : Q-Tm (T a a r))
      → ----------------------
      J T P d r t == d a t

-- Transport structure.
record Transport {C : Family} (C-intro : Intro C) (D : Family) : Set where
  open Family C
  open Intro C-intro
  open Family D renaming (Ty to D-Ty; Tm to D-Tm)
  field
    transport :
      {A : Ty}
      (P : (a : Tm A) → D-Ty)
      {x y : Tm A}
      (p : Tm (Id x y))
      (d : D-Tm (P x))
      → ---------------------------------------
      D-Tm (P y)

    transport-β : 
      {A : Ty}
      (P : (a : Tm A) → D-Ty)
      {a : Tm A}
      (d : D-Tm (P a))
      → ---------------------------------------
      transport P r d == d

-- Duplicate of transport structure that computes.
module Transport' {C : Family} {C-intro : Intro C} {D : Family} (C-transport-D : Transport C-intro D) where
  open Family C
  open Intro C-intro
  open Family D renaming (Ty to D-Ty; Tm to D-Tm)
  open Transport (abstract-center (singleton-contr C-transport-D) .fst) renaming (transport to transport'; transport-β to transport'-β) public
  {-# REWRITE transport'-β #-}

-- Transport structure from Paulin-Mohring eliminator.
elim-to-transport :
  {C D : Family}
  {C-intro : Intro C}
  (C-elim : Elim C-intro D)
  → -----------------------
  Transport C-intro D 

elim-to-transport C-elim = λ where
  .transport P p d → J' (λ y p → P y) d p
  .transport-β P d → refl
 where
  open Elim' C-elim
  open Transport
