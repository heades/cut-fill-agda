-----------------------------------------------------------------------
-- The definition of lineales. They are used to enforce the weak     --
-- adjunction condition on arrows in dialectica categories.          --
-- Lineales are due to Martin Hyland and Valeria de Paiva:           --
--   http://www.cs.bham.ac.uk/~vdp/publications/Lineales91.pdf       --
-----------------------------------------------------------------------

module lineale where

open import prelude

record Proset {ℓ : Level}(A : Set ℓ) : Set (lsuc ℓ) where
 constructor MkProset
 field
   rel : A → A → Set
   prefl : ∀{a : A} → rel a a
   ptrans : ∀{a b c : A} → rel a b → rel b c → rel a c

open Proset public

record MonProset {ℓ : Level}(P : Set ℓ) : Set (lsuc ℓ) where
 constructor MkMonProset
 field
   mul : P → P → P
   unit : P
   
   proset : Proset P
   assoc : ∀{a b c : P} → mul a (mul b c) ≡ mul (mul a b) c
   left-ident : ∀{a : P} → mul unit a ≡ a
   right-ident : ∀{a : P} → mul a unit ≡ a
   symm : ∀{a b : P} → mul a b ≡ mul b a
   compat : ∀{a b : P} → (rel proset) a b → (∀{c : P} → (rel proset) (mul a c) (mul b c))

open MonProset public

record Lineale {ℓ : Level}(L : Set ℓ) : Set (lsuc ℓ) where
 constructor MkLineale
 field
   mproset : MonProset L
   l-imp : L → L → L
   
   rlcomp : (a b : L) → (rel (proset mproset)) ((mul mproset) a (l-imp a b)) b
   adj : {a b y : L} → (rel (proset mproset)) (mul mproset a y) b → (rel (proset mproset)) y (l-imp a b)

open Lineale public
