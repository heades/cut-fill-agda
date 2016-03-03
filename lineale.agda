-----------------------------------------------------------------------
-- The definition of lineales. They are used to enforce the weak     --
-- adjunction condition on arrows in dialectica categories.          --
-- Lineales are due to Martin Hyland and Valeria de Paiva:           --
--   http://www.cs.bham.ac.uk/~vdp/publications/Lineales91.pdf       --
-----------------------------------------------------------------------

module lineale where

open import prelude

record Poset {ℓ : Level}(A : Set ℓ) : Set (lsuc ℓ) where
 constructor MkPoset
 field
   rel : A → A → Set
   prefl : ∀{a : A} → rel a a
   ptrans : ∀{a b c : A} → rel a b → rel b c → rel a c

open Poset public

record MonPoset {ℓ : Level}(P : Set ℓ) : Set (lsuc ℓ) where
 constructor MkMonPoset
 field
   mul : P → P → P
   unit : P
   
   poset : Poset P
   assoc : ∀{a b c : P} → mul a (mul b c) ≡ mul (mul a b) c
   left-ident : ∀{a : P} → mul unit a ≡ a
   right-ident : ∀{a : P} → mul a unit ≡ a
   symm : ∀{a b : P} → mul a b ≡ mul b a
   compat : ∀{a b : P} → (rel poset) a b → (∀{c : P} → (rel poset) (mul a c) (mul b c))

open MonPoset public

record Lineale {ℓ : Level}(L : Set ℓ) : Set (lsuc ℓ) where
 constructor MkLineale
 field
   mposet : MonPoset L
   l-imp : L → L → L
   
   rlcomp : (a b : L) → (rel (poset mposet)) ((mul mposet) a (l-imp a b)) b
   adj : {a b y : L} → (rel (poset mposet)) (mul mposet a y) b → (rel (poset mposet)) y (l-imp a b)

open Lineale public
