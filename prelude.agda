module prelude where

open import level public
open import product public
open import product-thms public
open import sum public
open import empty public
open import unit public
open import functions renaming (id to id-set) public
open import eq public
open import list public
open import list-thms public
open import bool public
open import bool-thms public

-- Extensionality will be used when proving equivalences of morphisms.
postulate ext-set : ∀{l1 l2 : level} → extensionality {l1} {l2}
-- These are isomorphisms, but Agda has no way to prove these as
-- equivalences.  They are consistent to adopt as equivalences by
-- univalence:
postulate ∧-unit : ∀{ℓ}{A : Set ℓ} → A ≡ ((⊤ {ℓ}) ∧ A)
postulate ∧-sym : ∀{ℓ}{A B : Set ℓ} → (A ∧ B) ≡ (B ∧ A)
postulate ∧-unit-r : ∀{ℓ}{A : Set ℓ} → A ≡ (A ∧ (⊤ {ℓ}))
postulate ∧-assoc : ∀{ℓ}{A B C : Set ℓ} →  (A ∧ (B ∧ C)) ≡ ((A ∧ B) ∧ C)

-- The following defines a commutative monoid as lists:
_* = 𝕃
postulate *-comm : ∀{ℓ : Level}{A : Set ℓ}{l₁ l₂ : A *} → l₁ ++ l₂ ≡ l₂ ++ l₁
