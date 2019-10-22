{-# OPTIONS --postfix-projections #-}
module Frobenius.Families where

open import Frobenius.Basics

record Family : Set₁ where
  field
    Ty : Set
    Tm : Ty → Set

-- In the intended semantics of presheaves over a cwf C with presheaves Ty of types and Tm of terms, we have an internal family (Ty, Tm).
-- Representability of the morphism Tm → Ty (meaning that ∫ Tm → ∫ Ty has a right adjoint, i.e. context extension) can be captured internally only using a crisp extension of type theory.
-- Here, we only need a consequence of representability: internally, for any A : Ty, exponentiation with Tm A preserves dependent sums indexed over a discrete type.
-- For this development, we only need the case of dependent sums over ℕ, which is discrete in every presheaf category.
record IsRepresentable (C : Family) : Set₁ where
  open Family C
  field
    comparison-iso : {A : Ty} {P : ℕ → Set} → is-iso {Σ ℕ (λ n → Tm A → P n)} {Tm A → Σ ℕ P} (λ { (n , f) a → (n , f a)})

  module _ {A : Ty} {P : ℕ → Set} (f : Tm A → Σ ℕ P) where
    open is-iso (comparison-iso {A} {P})

    index : ℕ
    index = inverse f .fst

    function : Tm A → P index
    function = inverse f .snd

    constancy : (a : Tm A) → f a == (index , function a)
    constancy a = ap (λ f → f a) (! (inv-r))

{-
  We have a commuting cube with front face
    Σ ℕ (λ n → (a : Tm A) → P n a) ------> (a : Tm A) → Σ ℕ (λ n → P n a)
    |                                      |
    Σ ℕ (λ n → Tm A → Σ (Tm A) (P n)) ---> Tm A → Σ ℕ (Σ (Tm A) (P n))
  and back face
    Σ ℕ 1 -------------------------------> Tm A → ℕ
    |                                      |
    Σ ℕ (λ n → Tm A → Tm A) -------------> Tm A → Σ ℕ (Tm A).
  The horizontal morphisms except the first one are isomorphisms by assumption.
  The left and right squares are pullbacks.
  It follows that the first horizontal map is an isomorphism.
-}
  module _ {A : Ty} {P : ℕ → Tm A → Set} where
    open is-iso (comparison-iso {A} {λ n → Σ (Tm A) (P n)})
    private module Base = is-iso (comparison-iso {A} {λ n → Tm A})

    InFiberL : Σ ℕ (λ n → Tm A → Σ (Tm A) (P n)) → Set
    InFiberL (n , f) = (a : Tm A) → f a .fst == a

    InFiberR : (Tm A → Σ ℕ (λ n → Σ (Tm A) (P n))) → Set
    InFiberR g = (a : Tm A) → g a .snd .fst == a

    -- for now, see informal proof above (could also take as primitive)
    postulate
      comparison-iso-dep : is-iso {Σ ℕ (λ n → (a : Tm A) → P n a)} {(a : Tm A) → Σ ℕ (λ n → P n a)} (λ { (n , f) a → (n , f a)})

module FamilyOps where
  open Family
  open IsRepresentable

  ∐ : {Z : Set} (C : Z → Family) → Family
  ∐ {Z} C = λ where
    .Ty → Σ Z (λ z → C z .Ty)
    .Tm (z , A) → C z .Tm A

  module _ {Z : Set} {C : Z → Family} (C-rep : (z : Z) → IsRepresentable (C z)) where
    ∐-representable : IsRepresentable (∐ C)
    ∐-representable .comparison-iso {A = (z , A)} {P} = h .snd where
      h =
          Σ ℕ (λ n → C _ .Tm A → P n)
        ≅⟨ (_ , C-rep _ .comparison-iso) ⟩
          (C _ .Tm A → Σ ℕ P)
        ≅∎

  unit : Family
  unit .Ty = ⊤
  unit .Tm unit = ⊤

  -- Agda bug (already reported last year):
  -- Termination checking fails despite no recursive call.
  {-# TERMINATING #-}
  unit-representable : IsRepresentable unit
  unit-representable .comparison-iso .is-iso.inverse f = (f tt .fst , λ {tt → f tt .snd})
  unit-representable .comparison-iso .is-iso.inv-l = refl
  unit-representable .comparison-iso .is-iso.inv-r = funext $ λ {tt → refl}

  _•_ : (C₁ C₂ : Family) → Family
  C₁ • C₂ = λ where
    .Ty → Σ (C₁ .Ty) (λ A₁ → C₁ .Tm A₁ → C₂ .Ty)
    .Tm (A₁ , A₂) → Σ (C₁ .Tm A₁) (λ t₁ → C₂ .Tm (A₂ t₁))

  module _ {C D : Family} (C-rep : IsRepresentable C) (D-rep : IsRepresentable D) where
    open Family C renaming (Ty to C-Ty; Tm to C-Tm)
    open Family D renaming (Ty to D-Ty; Tm to D-Tm)

    join-representable : IsRepresentable (C • D)
    join-representable .comparison-iso {A = (A-C , A-D)} {P} = h .snd where
      h =
          Σ ℕ (λ n → Σ (C-Tm A-C) (λ a-C → D-Tm (A-D a-C)) → P n)
        ≅⟨ Σ-r-iso (λ n → curry-iso) ⟩
          Σ ℕ (λ n → (a-C : (C-Tm A-C)) → D-Tm (A-D a-C) → P n)
        ≅⟨ (_ , comparison-iso-dep C-rep) ⟩
          ((a-C : (C-Tm A-C)) → Σ ℕ (λ n → D-Tm (A-D a-C) → P n))
        ≅⟨ Π-r-iso (λ a-C → (_ , D-rep .comparison-iso {A-D a-C} {P})) ⟩
          ((a-C : (C-Tm A-C)) → D-Tm (A-D a-C) → Σ ℕ P)
        ≅⟨ curry-iso ⁻¹ ⟩
          (Σ (C-Tm A-C) (λ a-C → D-Tm (A-D a-C)) → Σ ℕ P)
        ≅∎

  manyfold : (C : Family) (n : ℕ) → Family
  manyfold C O = unit
  manyfold C (S n) = (manyfold C n) • C

  manyfold-representable : {C : Family} (C-rep : IsRepresentable C) {n : ℕ} → IsRepresentable (manyfold C n)
  manyfold-representable {C} C-rep {O} = unit-representable
  manyfold-representable {C} C-rep {S n} = join-representable (manyfold-representable C-rep {n}) C-rep

  star : (C : Family) → Family
  star C = ∐ (manyfold C)

  star-representable : {C : Family} (C-rep : IsRepresentable C) → IsRepresentable (star C)
  star-representable C-rep = ∐-representable $ λ n → manyfold-representable C-rep {n}
