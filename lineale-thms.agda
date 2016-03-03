-----------------------------------------------------------------------
-- Theorems about lineals.                                           --
-----------------------------------------------------------------------
module lineale-thms where

open import prelude
open import lineale

compat-sym : ∀{ℓ}{P : Set ℓ}{p : MonPoset P}{a b : P} → (rel (poset p)) a b → (∀{c : P} → (rel (poset p)) ((mul p) c a) ((mul p) c b))
compat-sym {_}{P}{MkMonPoset _⊗_ ut (MkPoset _≤_ r t) asc li ri sm cp} {a}{b} p₁ {c} rewrite sm {c}{a} | sm {c}{b} = cp {a}{b} p₁ {c}

l-mul-funct : ∀{ℓ}{L : Set ℓ}{p : MonPoset L}{a c b d : L}
  → (rel (poset p)) a c
  → (rel (poset p)) b d
  → (rel (poset p)) (mul p a b) (mul p c d)
l-mul-funct {_}{P}{MkMonPoset _⊗_ ut (MkPoset _≤_ r t) asc li ri sm cp}{a}{c}{b}{d} p₁ p₂ =
 let mp = MkMonPoset _⊗_ ut (MkPoset _≤_ r t) asc li ri sm cp
     p₃ = compat mp {a}{c} p₁ {b}
     p₄ = compat-sym {p = mp}{b}{d} p₂ {c}
  in ptrans (poset mp) p₃ p₄ 

l-imp-funct : ∀{ℓ}{L : Set ℓ}{p : Lineale L}{c a b d : L}
  → (rel (poset (mposet p))) c a
  → (rel (poset (mposet p))) b d
  → (rel (poset (mposet p))) (l-imp p a b) (l-imp p c d)
l-imp-funct {_}{L}{MkLineale (MkMonPoset _⊗_ e (MkPoset _≤_ pr pt) asc li ri sm cp) _→l_ rc adj}{c}{a}{b}{d} r₁ r₂
 with pt (cp r₁ {a →l b}) (pt (rc a b) r₂)
... | g = adj g
  
adj-inv : {ℓ : Level}{L : Set ℓ}{r : Lineale L}{a b y : L} → (rel (poset (mposet r))) y (l-imp r a b) → (rel (poset (mposet r))) (mul (mposet r) a y) b
adj-inv {_}{L}{MkLineale (MkMonPoset _⊗_ e (MkPoset _≤_ pr pt) asc li ri sm cp) _→l_ rc adj} {a} {b}{y} p =
 let mp = MkMonPoset _⊗_ e (MkPoset _≤_ pr pt) asc li ri sm cp
  in pt (compat-sym {p = mp}{y}{a →l b} p {a}) (rc a b) 
