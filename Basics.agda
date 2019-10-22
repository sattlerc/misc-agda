{-# OPTIONS --rewriting --confluence-check --double-check  --postfix-projections #-}
module Basics where

open import Agda.Primitive public

-- Equality
-----------

data _==_ {i} {A : Set i} : (x y : A) → Set i where
  refl : {a : A} → a == a

{-# BUILTIN REWRITE _==_ #-}

-- Function extensionality.
postulate
  funext : ∀ {i j} {A : Set i} {B : A → Set j} {f g : (a : A) → B a} (p : (a : A) → f a == g a) → f == g

! : ∀ {i} {A : Set i} {x y : A} (p : x == y) → y == x
! refl = refl

infixr 20 _∙_
_∙_ : ∀ {i} {A : Set i} {x y z : A} (p : x == y) (q : y == z) → x == z
refl ∙ refl = refl

transp : ∀ {i j} {A : Set i} (B : A → Set j) {x y : A} (p : x == y) (b : B x) → B y
transp B refl b = b

ap : ∀ {i j} {A : Set i} {B : Set j} (f : A → B) {x y : A} (p : x == y) → f x == f y
ap f refl = refl

record is-contr {i} (A : Set i) : Set i where
  constructor _,_
  field
    center : A
    spoke : (x : A) → x == center

-- Other basic type formers
---------------------------

record ⊤ : Set where
  constructor tt

infixr 5 _,_
record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public

Π : ∀ {i j} (A : Set i) (B : A → Set j) → Set (i ⊔ j)
Π A B = (a : A) → B a

pair= : ∀ {i j} {A : Set i} {B : A → Set j} {a₁ a₂ : A} (p : a₁ == a₂) {b₁ : B a₁} {b₂ : B a₂} (q : transp B p b₁ == b₂) → _==_ {A = Σ A B} (a₁ , b₁) (a₂ , b₂)
pair= refl refl = refl

data ℕ : Set where
  O : ℕ
  S : ℕ → ℕ

-- Helpers
----------

infixr 20 _$_
_$_ : ∀ {i j} {A : Set i} {B : A → Set j} (f : (a : A) → B a) (a : A) → B a
f $ a = f a

id : {A : Set} → A → A
id x = x

infixr 10 _∘_
_∘_ : {A B C : Set} (g : B → C) (f : A → B) → A → C
(g ∘ f) x = g (f x)

record is-iso {A B : Set} (f : A → B) : Set where
  field
    inverse : B → A
    inv-l : {a : A} → inverse (f a) == a
    inv-r : {b : B} → f (inverse b) == b

  reflect-eq : {a₁ a₂ : A} (q : f a₁ == f a₂) → a₁ == a₂
  reflect-eq q = ! inv-l ∙ ap (λ b → inverse b) q ∙ inv-l

_≅_ : (A B : Set) → Set
A ≅ B = Σ (A → B) is-iso

idi : {A : Set} → A ≅ A
idi .fst = id
idi .snd .is-iso.inverse = id
idi .snd .is-iso.inv-l = refl
idi .snd .is-iso.inv-r = refl

_⁻¹ : {A B : Set} (f : A ≅ B) → B ≅ A
(f , f-iso) ⁻¹ = λ where
  .fst → inverse
  .snd .is-iso.inverse → f
  .snd .is-iso.inv-l → inv-r
  .snd .is-iso.inv-r → inv-l where
  open is-iso f-iso

infixr 10 _∘i_
_∘i_ : {A B C : Set} (g : B ≅ C) (f : A ≅ B) → A ≅ C
(g , g-iso) ∘i (f , f-iso) = ((g ∘ f) , h) where
  module F = is-iso f-iso
  module G = is-iso g-iso

  h : is-iso (g ∘ f)
  h .is-iso.inverse = F.inverse ∘ G.inverse
  h .is-iso.inv-l = ap F.inverse G.inv-l ∙ F.inv-l
  h .is-iso.inv-r = ap g F.inv-r ∙ G.inv-r

Π-r-iso : {A : Set} {B₁ B₂ : A → Set} (h : (a : A) → B₁ a ≅ B₂ a) → Π A B₁ ≅ Π A B₂
Π-r-iso {A} {B₁} {B₂} h = λ where
  .fst f₁ a → g a (f₁ a)
  .snd .is-iso.inverse f₂ a → inverse a (f₂ a)
  .snd .is-iso.inv-l → funext $ λ a → inv-l _
  .snd .is-iso.inv-r → funext $ λ a → inv-r _ where

  g : (a : A) → B₁ a → B₂ a
  g a = h a .fst

  open module Dummy a = is-iso (h a .snd)

{-
Π-l-iso : {A₁ A₂ : Set} {B : A₂ → Set} (h : A₁ ≅ A₂) → Π A₁ (λ a₁ → B (h .fst a₁)) ≅ Π A₂ B
Π-l-iso {A₁} {A₂} {B} h = helper where
  g : A₁ → A₂
  g = h .fst

  open is-iso (h .snd)

  foo : {f₁ : Π A₁ (λ a₁ → B (h .fst a₁))} {a₁ : A₁} → transp B inv-r (f₁ $ inverse (g a₁)) == f₁ a₁
  foo = {!!}

  bar : {f₂ : Π A₂ B} {a₂ : A₂} → transp B inv-r (f₂ $ g (inverse a₂)) == f₂ a₂
  bar = {!!}

  helper : Π A₁ (λ a₁ → B (h .fst a₁)) ≅ Π A₂ B
  helper .fst f₁ a₂ = transp B inv-r (f₁ (inverse a₂))
  helper .snd .is-iso.inverse f₂ a₁ = f₂ (g a₁)
  helper .snd .is-iso.inv-l {f₁} = funext $ λ a₁ → foo {f₁} {a₁}
  helper .snd .is-iso.inv-r {f₂} = funext $ λ a₂ → bar {f₂} {a₂}
-}

Σ-r-iso : {A : Set} {B₁ B₂ : A → Set} (h : (a : A) → B₁ a ≅ B₂ a) → Σ A B₁ ≅ Σ A B₂
Σ-r-iso {A} {B₁} {B₂} h = λ where
  .fst (a , b₁) → (a , g a b₁)
  .snd .is-iso.inverse (a , b₂) → (a , inverse a b₂)
  .snd .is-iso.inv-l → pair= refl (inv-l _)
  .snd .is-iso.inv-r → pair= refl (inv-r _) where

  g : (a : A) → B₁ a → B₂ a
  g a = h a .fst

  open module Dummy a = is-iso (h a .snd)

curry-iso : {A : Set} {B : (a : A) → Set} {C : (a : A) (b : B a) → Set} → Π (Σ A B) (λ {(a , b) → C a b}) ≅ Π A (λ a → Π (B a) (C a))
curry-iso {A} {B} {C} = λ where
  .fst f a b → f (a , b)
  .snd .is-iso.inverse g (a , b) → g a b
  .snd .is-iso.inv-l → refl
  .snd .is-iso.inv-r → refl

infixr 10 _≅⟨_⟩_
infix  15 _≅∎

_≅⟨_⟩_ : ∀ (A : Set) {B C : Set} → A ≅ B → B ≅ C → A ≅ C
_ ≅⟨ f ⟩ g = g ∘i f

_≅∎ : ∀ (A : Set) → A ≅ A
_ ≅∎ = idi

infixl 40 ap
syntax ap f p = p |in-ctx f

{-
record CommutingTriangle
  {A B C : Set}
  (f : A → B)
  (g : B → C)
  (h : A → C) : Set where
  field
    witness : ∀ a → g (f a) == h a

-- First the vertical maps, then the horizontal ones.
record CommutingSquare
  {A₀₀ A₀₁ A₁₀ A₁₁ : Set}
  (f₋₀ : A₀₀ → A₁₀)
  (f₋₁ : A₀₁ → A₁₁)
  (f₀₋ : A₀₀ → A₀₁)
  (f₁₋ : A₁₀ → A₁₁) : Set where
  field
    witness : ∀ a → f₋₁ (f₀₋ a) == f₁₋ (f₋₀ a)

{-
module _
  {A₀₀ A₀₁ A₀₂ A₁₀ A₁₁ A₁₂ : Set}
  {f₀₀,₁₀ : A₀₀ → A₁₀}
  {f₀₁,₁₁ : A₀₁ → A₁₁}
  {f₀₋ : A₀₀ → A₀₁}
  {f₁₋ : A₁₀ → A₁₁}
  {f₀₊ : A₀₁ → A₀₂}
  {f₁₊ : A₁₁ → A₁₂}
  (p : CommutingSquare f₋₀ f₋₁ f₀₋ f₁₋)
  (q : CommutingSquare f₋₀ f₋₁ f₀₊ f₁₊)
-}


record PullbackUP 
  {A₀₀ A₀₁ A₁₀ A₁₁ : Set}
  (f₋₀ : A₀₀ → A₁₀)
  (f₋₁ : A₀₁ → A₁₁)
  (f₀₋ : A₀₀ → A₀₁)
  (f₁₋ : A₁₀ → A₁₁)
  (p : CommutingSquare f₋₀ f₋₁ f₀₋ f₁₋)
  (a₀₁ : A₀₁) (a₁₀ : A₁₀) (q : f₋₁ a₀₁ == f₁₋ a₁₀) : Set where
  field
    a₀₀ : A₀₀
    f₀₋-coh : f₀₋ a₀₀ == a₀₁
    f₋₀-coh : f₋₀ a₀₀ == a₁₀
    unique : {a₀₀' : A₀₀} (f₀₋-coh' : f₀₋ a₀₀ == a₀₁) (f₋₀-coh' : f₋₀ a₀₀ == a₁₀) → a₀₀' == a₀₀

record IsPullback
  {A₀₀ A₀₁ A₁₀ A₁₁ : Set}
  (f₋₀ : A₀₀ → A₁₀)
  (f₋₁ : A₀₁ → A₁₁)
  (f₀₋ : A₀₀ → A₀₁)
  (f₁₋ : A₁₀ → A₁₁)
  (p : CommutingSquare f₋₀ f₋₁ f₀₋ f₁₋) : Set where
  field
    up : ∀ a₀₁ a₁₀ q → PullbackUP f₋₀ f₋₁ f₀₋ f₁₋ p a₀₁ a₁₀ q

module _
  {A₀₀ A₀₁ A₁₀ A₁₁ : Set}
  {f₋₀ : A₀₀ → A₁₀}
  {f₋₁ : A₀₁ → A₁₁}
  {f₀₋ : A₀₀ → A₀₁}
  {f₁₋ : A₁₀ → A₁₁}
  (p : CommutingSquare f₋₀ f₋₁ f₀₋ f₁₋)
  (A-pullback : IsPullback f₋₀ f₋₁ f₀₋ f₁₋ p)
  {A₀₀' A₀₁' A₁₀' A₁₁' : Set}
  {f₋₀' : A₀₀' → A₁₀'}
  {f₋₁' : A₀₁' → A₁₁'}
  {f₀₋' : A₀₀' → A₀₁'}
  {f₁₋' : A₁₀' → A₁₁'}
  (p' : CommutingSquare f₋₀' f₋₁' f₀₋' f₁₋')
  (A'-pullback : IsPullback f₋₀' f₋₁' f₀₋' f₁₋' p') where

  open IsPullback A-pullback renaming (up to A-up)
  open IsPullback A'-pullback renaming (up to A'-up)

  module _
    (u₀₀ : A₀₀ → A₀₀')
    {u₀₁ : A₀₁ → A₀₁'} (u₀₁-iso : is-iso u₀₁)
    {u₁₀ : A₁₀ → A₁₀'} (u₁₀-iso : is-iso u₁₀)
    {u₁₁ : A₁₁ → A₁₁'} (u₁₁-iso : is-iso u₁₁)
    (c₋₀ : CommutingSquare f₋₀ f₋₀' u₀₀ u₁₀)
    (c₋₁ : CommutingSquare f₋₁ f₋₁' u₀₁ u₁₁)
    (c₀₋ : CommutingSquare f₀₋ f₀₋' u₀₀ u₀₁)
    (c₁₋ : CommutingSquare f₁₋ f₁₋' u₁₀ u₁₁) where

    private module I₀₁ = is-iso u₀₁-iso
    private module I₁₀ = is-iso u₁₀-iso
    private module I₁₁ = is-iso u₁₁-iso

    open PullbackUP

{-
    pullback-iso : is-iso u₀₀
    pullback-iso .is-iso.inverse a₀₀' = {!lift .a₀₀!} where
      a₁₀ = I₁₀.inverse (f₋₀' a₀₀')
      a₀₁ = I₀₁.inverse (f₀₋' a₀₀')
      -- lift = A-up a₀₁ a₁₀ (I₁₁.reflect-eq (! (c₋₁ _) ∙ ap f₋₁' I₀₁.inv-r ∙ p' _ ∙ ! (! (c₁₋ _) ∙ ap f₁₋' I₁₀.inv-r)))
    pullback-iso .is-iso.inv-l {a₀₀} = {!!}
    pullback-iso .is-iso.inv-r = {!!}
-}
-}

-- Tools for rewriting
----------------------

-- Clearly admissible.
postulate
  abstract-center : ∀ {i} {X : Set i} (c : is-contr X) → X

module _ {i} {A : Set i} (a : A) where
  singleton-contr : is-contr (Σ A (λ x → x == a))
  singleton-contr = λ where
    .center → (a , refl)
    .spoke (a , refl) → refl
   where
    open is-contr

  abstr : A
  abstr = abstract-center singleton-contr .fst

  abstr-coh : abstr == a
  abstr-coh = abstract-center singleton-contr .snd

-- Using 'abstr a' for 'a' allows us to declare rewriting rules involving 'a'
-- in situation where normally the rewriting rule would start with a parameter.
