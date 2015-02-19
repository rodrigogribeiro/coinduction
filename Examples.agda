open import Coinduction

open import Data.Empty
open import Data.Nat
open import Data.Vec using (Vec ; [] ; _∷_)

open import Function

open import Relation.Binary.PropositionalEquality using (_≡_ ; refl ; trans)
open import Relation.Nullary

module Examples where

  -- a type of streams

  module Example1 where

    data Stream (A : Set) : Set where
      _∷_ : A → ∞ (Stream A) → Stream A

    -- some little functions on streams

    take : ∀ {A : Set} n → Stream A → Vec A n
    take zero (x ∷ _) = []
    take (suc n) (x ∷ xs) = x ∷ take n (♭ xs)

    map : ∀ {A B : Set} → (A → B) → Stream A → Stream B
    map f (x ∷ xs) = f x ∷ ♯ (map f (♭ xs))

    zeros : Stream ℕ
    zeros = 0 ∷ ♯ zeros

    ones : Stream ℕ
    ones = 1 ∷ ♯ ones

    ones' : Stream ℕ
    ones' = map suc zeros

    {-
      the proof, equationally

      ones' = map suc zeros
            = map suc (zero ∷ ♯ zeros)
            = suc zero ∷ ♯ map suc (♭ (♯ zeros))
            = 1 ∷ ♯ map suc zeros
            = 1 ∷ ones'
            = 1 ∷ ones
            = ones
    -}


    module EqualityTake1 where

      -- stream equality

      data _≈_ {A : Set} : Stream A → Stream A → Set where
        _∷_ : ∀ {x y xs ys} → x ≡ y → ∞ (♭ xs ≈ ♭ ys) → (x ∷ xs) ≈ (y ∷ ys)

      ones≈ones' : ones ≈ ones'
      ones≈ones' = refl ∷ ♯ ones≈ones'

    module EqualityTake2 where

      -- stream equality, other version

      data _≈'_ {A : Set} : Stream A → Stream A → Set where
        _∷_ : ∀ x {xs ys} → ∞ (♭ xs ≈' ♭ ys) → (x ∷ xs) ≈' (x ∷ ys)

      ones≈'ones' : ones ≈' ones'
      ones≈'ones' = suc zero ∷ ♯ ones≈'ones'

    module EqualityCoincides where

      open EqualityTake1
      open EqualityTake2

      ≈⇒≈' : ∀ {A : Set}(xs ys : Stream A) → xs ≈ ys → xs ≈' ys
      ≈⇒≈' ._ ._ (refl ∷ p) = _ ∷ ♯ ≈⇒≈' _ _ (♭ p)

      ≈'⇒≈ : ∀ {A : Set}(xs ys : Stream A) → xs ≈' ys → xs ≈ ys
      ≈'⇒≈ ._ ._ (x ∷ p) = refl ∷ ♯ (≈'⇒≈ _ _ (♭ p))

    -- trying some equational reasoning

    module ≈-Reasoning where

      open EqualityTake1

      infix 4 _≈P_ _≈x_
      infixr 5 _∷_
      infix 3 _≈⟨_⟩_
      infix 2 _□

      -- a data type for equational reasoning using codata

      data _≈P_ {A : Set} : Stream A → Stream A → Set where
        _∷_   : ∀ {x y xs ys} → x ≡ y → ∞ (♭ xs ≈P ♭ ys) → x ∷ xs ≈P y ∷ ys
        _≈⟨_⟩_ : ∀ (xs : Stream A) {ys zs} → xs ≈P ys → ys ≈P zs → xs ≈P zs
        _□    : ∀ xs → xs ≈P xs

      -- stream equality implies ≈P

      ≈P-complete : ∀ {A : Set}{xs ys : Stream A} → xs ≈ ys → xs ≈P ys
      ≈P-complete (eq ∷ p) = eq ∷ ♯ (≈P-complete (♭ p))

      -- a stream equality that uses ≈P

      data _≈x_ {A : Set} : Stream A → Stream A → Set where
        _∷_ : ∀ {x y : A}{xs ys} → x ≡ y → (♭ xs ≈P ♭ ys) → (x ∷ xs) ≈x (x ∷ ys)

      ≈x-refl : ∀ {A}(xs : Stream A) → xs ≈x xs
      ≈x-refl (x ∷ xs) = refl ∷ (♭ xs □)

      ≈x-trans : ∀ {A}{xs ys zs : Stream A} → xs ≈x ys → ys ≈x zs → xs ≈x zs
      ≈x-trans {A}{_ ∷ xs}(refl ∷ p) (refl ∷ p') = refl ∷ (♭ xs ≈⟨ p ⟩ p')

      ≈P⇒≈x : ∀ {A}{xs ys : Stream A} → xs ≈P ys → xs ≈x ys
      ≈P⇒≈x (refl ∷ p) = refl ∷ ♭ p
      ≈P⇒≈x (xs ≈⟨ p ⟩ p₁) = ≈x-trans (≈P⇒≈x p) (≈P⇒≈x p₁)
      ≈P⇒≈x (xs □) = ≈x-refl xs

      -- soundness

      mutual
        ≈P-sound : ∀ {A : Set}{xs ys : Stream A} → xs ≈P ys → xs ≈ ys
        ≈P-sound = ≈x-sound ∘ ≈P⇒≈x

        ≈x-sound : ∀ {A : Set}{xs ys : Stream A} → xs ≈x ys → xs ≈ ys
        ≈x-sound (refl ∷ p) = refl ∷ ♯ (≈P-sound p)


    -- -- all natural numbers set

    -- allℕ : Stream ℕ
    -- allℕ = enum 0
    --      where
    --        enum : ℕ → Stream ℕ
    --        enum n = n ∷ (♯ enum (suc n))

    -- -- describing a coinductive property

    -- infix 4 _∈_

    -- data _∈_ {A : Set} : A → Stream A → Set where
    --   here  : ∀ {x xs} → x ∈ x ∷ xs
    --   there : ∀ {x y xs} → (x ∈ ♭ xs) → x ∈ y ∷ xs

    -- allℕisℕ : ∀ (n : ℕ) → n ∈ allℕ
    -- allℕisℕ n = {!!}
