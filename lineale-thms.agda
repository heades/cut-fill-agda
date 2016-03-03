-----------------------------------------------------------------------
-- Theorems about lineals.                                           --
-----------------------------------------------------------------------
module lineale-thms where

open import prelude
open import lineale

compat-sym : ∀{ℓ}{P : Set ℓ}{p : MonProset P}{a b : P} → (rel (proset p)) a b → (∀{c : P} → (rel (proset p)) ((mul p) c a) ((mul p) c b))
compat-sym {_}{P}{MkMonProset _⊗_ ut (MkProset _≤_ r t) asc li ri sm cp} {a}{b} p₁ {c} rewrite sm {c}{a} | sm {c}{b} = cp {a}{b} p₁ {c}

l-mul-funct : ∀{ℓ}{L : Set ℓ}{p : MonProset L}{a c b d : L}
  → (rel (proset p)) a c
  → (rel (proset p)) b d
  → (rel (proset p)) (mul p a b) (mul p c d)
l-mul-funct {_}{P}{MkMonProset _⊗_ ut (MkProset _≤_ r t) asc li ri sm cp}{a}{c}{b}{d} p₁ p₂ =
 let mp = MkMonProset _⊗_ ut (MkProset _≤_ r t) asc li ri sm cp
     p₃ = compat mp {a}{c} p₁ {b}
     p₄ = compat-sym {p = mp}{b}{d} p₂ {c}
  in ptrans (proset mp) p₃ p₄ 

l-imp-funct : ∀{ℓ}{L : Set ℓ}{p : Lineale L}{c a b d : L}
  → (rel (proset (mproset p))) c a
  → (rel (proset (mproset p))) b d
  → (rel (proset (mproset p))) (l-imp p a b) (l-imp p c d)
l-imp-funct {_}{L}{MkLineale (MkMonProset _⊗_ e (MkProset _≤_ pr pt) asc li ri sm cp) _→l_ rc adj}{c}{a}{b}{d} r₁ r₂
 with pt (cp r₁ {a →l b}) (pt (rc a b) r₂)
... | g = adj g
  
adj-inv : {ℓ : Level}{L : Set ℓ}{r : Lineale L}{a b y : L} → (rel (proset (mproset r))) y (l-imp r a b) → (rel (proset (mproset r))) (mul (mproset r) a y) b
adj-inv {_}{L}{MkLineale (MkMonProset _⊗_ e (MkProset _≤_ pr pt) asc li ri sm cp) _→l_ rc adj} {a} {b}{y} p =
 let mp = MkMonProset _⊗_ e (MkProset _≤_ pr pt) asc li ri sm cp
  in pt (compat-sym {p = mp}{y}{a →l b} p {a}) (rc a b) 
