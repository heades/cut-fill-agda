-----------------------------------------------------------------------
-- This file formalizes the proof that Dial₂(Sets) is indeed a model --
-- of Full Tensorial Logic.  See Lemma 16 and Lemma 17 of the paper. --
-----------------------------------------------------------------------
module Tensorial where

open import prelude
open import lineale 
open import concrete-lineales 
open import DCSets Set isLinealeSet


-- We first must prove that Dial₂(Sets) is a dialogue category.  The
-- defining feature is that we use primarily implication for this.

-- This defines the negation functor: ¬ : Dial₂(Sets) → Dial₂ᵒᵖ(Sets)
¬ₒ : Obj → Obj
¬ₒ A = A ⊸ₒ J


¬ₐ-aux : ∀{U V Y X : Set₁}{f : U → V}{F : Y → X}
  → Σ (V → (⊤ {lsuc lzero})) (λ x → (⊤ {lsuc lzero}) → Y)
  → Σ (U → ⊤) (λ x → ⊤ → X)
¬ₐ-aux {f = f}{F}(j₁ , j₂) = (λ u → j₁ (f u)) , (λ t → F (j₂ t))

¬ₐ-aux' : ∀{U V : Set₁}{f : U → V}
  → Σ U (λ x → (⊤ {lsuc lzero}))
  → Σ V (λ x → (⊤ {lsuc lzero}))
¬ₐ-aux' {f = f} (u , triv) = f u , triv

¬ₐ : {A B : Obj} → Hom A B → Hom (¬ₒ B) (¬ₒ A)
¬ₐ {(U , X , α)}{(V , Y , β)} (f , F , p) = (λ x → ¬ₐ-aux {f = f}{F} x) , ¬ₐ-aux' {f = f} , (λ {u} → ¬ₐ-cond {u})
 where    
   ¬ₐ-cond : {u : Σ (V → ⊤) (λ x → ⊤ → Y)} {y : Σ U (λ x → ⊤)}
     → ⊸-cond β (λ x y₁ → (⊤ {lzero})) u (¬ₐ-aux' {f = f} y)
     → ⊸-cond α (λ x y₁ → ⊤) (¬ₐ-aux {f = f}{F} u) y
   ¬ₐ-cond {j₁ , j₂}{u , triv} p₁ p₂ = p₁ (p p₂)

-- At this point we must show that the required family of bijections
-- exist.
--
-- The bijection φ turns out to be a simple use of the combination of
-- currying and associativity:
--
--   Hom(A ⊗ B,¬ C) = Hom(A ⊗ B,C ⊸ ⊥)
--                  ≅ Hom((A ⊗ B) ⊗ C, ⊥)
--                  ≅ Hom(A ⊗ (B ⊗ C), ⊥)
--                  ≅ Hom(A, (B ⊗ C) ⊸ ⊥)
--                  = Hom(A, ¬ (B ⊗ C))
-- 
-- Note that the previous string of isomorphisms do not depend on the
-- fact that ⊥ is the intial object.  In fact, we can replace ⊥ with
-- any object at all, and the result still holds.

φ : {A B C : Obj}
  → Hom (A ⊗ₒ B) (¬ₒ C)
  → Hom A (¬ₒ (B ⊗ₒ C))
φ {A}{B}{C} f = cur ((α⊗-inv {A}{B}{C}) ○ (uncur f))

φ-inv : {A B C : Obj}
  → Hom A (¬ₒ (B ⊗ₒ C))
  → Hom (A ⊗ₒ B) (¬ₒ C)
φ-inv {A}{B}{C} g = cur ((α⊗ {A}{B}{C}) ○ (uncur g))

φ-bij₁ : ∀{A B C : Obj}{f : Hom (A ⊗ₒ B) (¬ₒ C)}
  → φ-inv (φ f) ≡h f
φ-bij₁ {A}{B}{C}{f} with
    (cur-uncur-bij₁ {A}{B ⊗ₒ C}{J}{comp (α⊗-inv {A}{B}{C}) (uncur {A ⊗ₒ B}{C}{J} f)}) 
... | eq₁ with
    cur-≡h (≡h-subst-○ {(A ⊗ₒ B) ⊗ₒ C}{A ⊗ₒ (B ⊗ₒ C)}{J}{α⊗}{α⊗}
      {j = uncur f} (≡h-refl {(A ⊗ₒ B) ⊗ₒ C}{A ⊗ₒ (B ⊗ₒ C)} {f = α⊗}) eq₁
      (≡h-trans (○-assoc {f = α⊗ {A} {B} {C}} {α⊗-inv} {uncur f})
      (≡h-subst-○ {f₁ = α⊗ {A} {B} {C} ○ α⊗-inv} {id} {uncur f} {uncur f}
      {uncur f} α⊗-id₁ ≡h-refl ○-idl)))
... | eq₂ = ≡h-trans eq₂ cur-uncur-bij₂

φ-bij₂ : ∀{A B C : Obj}{f : Hom A (¬ₒ (B ⊗ₒ C))}
  → φ (φ-inv f) ≡h f
φ-bij₂ {A}{B}{C}{f} with
  cur-uncur-bij₁ {f = comp (α⊗ {A}{B}{C}) (uncur f)}
... | eq₁ with
  cur-≡h (≡h-subst-○ {f₁ = α⊗-inv {A}{B}{C}}{α⊗-inv {A}{B}{C}}
                       {j = comp α⊗-inv (comp α⊗ (uncur f))} ≡h-refl eq₁ ≡h-refl)
... | eq₂ with
  (cur-≡h (○-assoc {f = α⊗-inv {A} {B} {C}} {α⊗} {uncur f}))
... | eq₃ with
  cur-≡h (≡h-subst-○ {f₁ = comp (α⊗-inv {A}{B}{C}) α⊗}{id}
                       {uncur f}{uncur f}{comp id (uncur f)} α⊗-id₂ ≡h-refl ≡h-refl)
... | eq₄ = ≡h-trans eq₂ (≡h-trans eq₃ (≡h-trans eq₄ (≡h-trans
                     (cur-≡h (○-idl {f = uncur f})) (cur-uncur-bij₂ {g = f}))))

-- The following shows that Dial₂(Sets)! is cartesian.

Jₒ = !ₒ

-- First, we define the cartesian product in Dial₂(Sets), and then use
-- Jₒ to put us inside of Dial₂(Sets)!.
_&ᵣ_ : {U X V Y : Set₁}
  → (α : U → X → Set)
  → (β : V → Y → Set)
  → Σ U (λ x → V)
  → X ⊎ Y
  → Set
_&ᵣ_ α β (u , v) (inj₁ x) = α u x
_&ᵣ_ α β (u , v) (inj₂ y) = β v y

_&ₒ_ : (A B : Obj) → Obj
(U , X , α) &ₒ (V , Y , β) = (U × V) , (X ⊎ Y) , α &ᵣ β

-- The remainder of this file will work under the Jₒ functor which
-- will put us inside of Dial₂(Sets)!.

-- This defines the projection morphism: π₁ : F(A & B) → F(A).
π₁ : {A B : Obj} → Hom (Jₒ (A &ₒ B)) (Jₒ A)
π₁ {U , X , α}{V , Y , β} =
  fst ,
  (λ (f : U → (X *)) (p : U × V) → map inj₁ (f (fst p))) ,
  (λ {u y} → π₁-cond {u}{y})
 where
  π₁-cond : {u : Σ U (λ x → V)} {y : U → 𝕃 X} →
      foldr (λ a y₁ → Σ ((α &ᵣ β) u a) (λ x → y₁)) (⊤ {lzero}) (map inj₁ (y (fst u))) →
      foldr (λ a y₁ → Σ (α (fst u) a) (λ x → y₁)) (⊤ {lzero}) (y (fst u))
  π₁-cond {u , v}{y} p = aux {y u} p 
   where
    aux : ∀{l}
      → foldr (λ a y₁ → Σ ((α &ᵣ β) (u , v) a) (λ x → y₁)) (⊤ {lzero}) (map inj₁ l)
      → foldr (λ a y₁ → Σ (α u a) (λ x → y₁)) (⊤ {lzero}) l
    aux {[]} _ = triv
    aux {x :: l} (p₁ , p₂) = p₁ , aux {l} p₂

-- This defines the projection morphism: π₂ : A & B → B.
π₂ : {A B : Obj} → Hom (Jₒ (A &ₒ B)) (Jₒ B)
π₂ {U , X , α}{V , Y , β} =
  snd , (λ f p → map inj₂ (f (snd p))) , (λ {u y} → π₂-cond {u}{y})
 where
  π₂-cond : {u : Σ U (λ x → V)} {y : V → 𝕃 Y} →
      foldr (λ a y₁ → Σ ((α &ᵣ β) u a) (λ x → y₁)) (⊤ {lzero}) (map inj₂ (y (snd u))) →
      foldr (λ a y₁ → Σ (β (snd u) a) (λ x → y₁)) (⊤ {lzero}) (y (snd u))
  π₂-cond {u , v}{y} p = aux {y v} p
   where
    aux : ∀{l}
      → foldr (λ a y₁ → Σ ((α &ᵣ β) (u , v) a) (λ x → y₁)) (⊤ {lzero}) (map inj₂ l)
      → foldr (λ a y₁ → Σ (β v a) (λ x → y₁)) (⊤ {lzero}) l
    aux {[]} _ = triv
    aux {x :: l} (p₁ , p₂) = p₁ , aux {l} p₂

cart-ar-crt : {U X V Y W Z : Set₁}
  → {α : U → X → Set}
  → {β : V → Y → Set}
  → {γ : W → Z → Set}
  → Hom (Jₒ (W , Z , γ)) (Jₒ (U , X , α))
  → Hom (Jₒ (W , Z , γ)) (Jₒ (V , Y , β))
  → (Σ U (λ x → V) → 𝕃 (X ⊎ Y)) → W → 𝕃 Z
cart-ar-crt  (f , F , p₁) (g , G , p₂) j w
  with (λ u → (proj-⊎₁ (j (u , g w)))) | (λ v → (proj-⊎₂ (j (f w , v))))
... | j₁ | j₂ = F j₁ w ++ G j₂ w 

foldr-append-× : {ℓ ℓ' : Level}{A : Set ℓ}{f : A → (Set ℓ')}{l₁ l₂ : 𝕃 A}
  → (p₁ : ∀{ℓ}{A : Set ℓ} → A ≡ ((⊤ {ℓ}) ∧ A))
  → (p₂ : ∀{ℓ}{A B C : Set ℓ} →  (A ∧ (B ∧ C)) ≡ ((A ∧ B) ∧ C))
  →   (foldr (λ a r → (f a) × r) (⊤ {ℓ'}) (l₁ ++ l₂))
    ≡ ((foldr (λ a r → (f a) × r) (⊤ {ℓ'}) l₁) × (foldr (λ a r → (f a) × r) (⊤ {ℓ'}) l₂))
foldr-append-× {l₁ = []}{l₂} p₁ p₂ = p₁
foldr-append-× {ℓ}{ℓ'}{A}{f}{l₁ = x :: l₁}{l₂} p₁ p₂ rewrite foldr-append-× {ℓ}{ℓ'}{A}{f}{l₁ = l₁}{l₂} p₁ p₂ = p₂
 
-- This takes two morphisms f : C → A and g : C → B, and constructs
-- a morphism (f,g) : C → A & B.
cart-ar : {C A B : Obj}
  → Hom (Jₒ C) (Jₒ A)
  → Hom (Jₒ C) (Jₒ B)
  → Hom (Jₒ C) (Jₒ (A &ₒ B))
cart-ar {W , Z , γ}{U , X , α}{V , Y , β} (f , F , p₁) (g , G , p₂)
  = (λ w → (f w , g w)) ,
    cart-ar-crt {α = α}{β}{γ} (f , F , p₁) (g , G , p₂) ,
    (λ {u y} → cart-ar-cond {u}{y})
  where
    cart-ar-cond : {u : W} {y : Σ U (λ x → V) → 𝕃 (X ⊎ Y)} →
      foldr (λ a y₁ → Σ (γ u a) (λ x → y₁)) (⊤ {lzero})
      (F (λ u₁ → proj-⊎₁ (y (u₁ , g u))) u ++
       G (λ v → proj-⊎₂ (y (f u , v))) u) →
      foldr (λ a y₁ → Σ ((α &ᵣ β) (f u , g u) a) (λ x → y₁)) (⊤ {lzero})
      (y (f u , g u))
    cart-ar-cond {u}{j} p
      rewrite
        foldr-append-× {ℓ' = lzero}
                       {f = γ u}
                       {F (λ u₁ → proj-⊎₁ (j (u₁ , g u))) u}
                       {G (λ v → proj-⊎₂ (j (f u , v))) u}
                       ∧-unit
                       ∧-assoc with p
    ... | (r₁ , r₂) = aux {j (f u , g u)} (p₁ r₁) (p₂ r₂)
     where
      aux : ∀{l}
       → foldr (λ a y → Σ (α (f u) a) (λ x → y)) (⊤ {lzero}) (proj-⊎₁ l)
       → foldr (λ a y → Σ (β (g u) a) (λ x → y)) (⊤ {lzero}) (proj-⊎₂ l)
       → foldr (λ a y₁ → Σ ((α &ᵣ β) (f u , g u) a) (λ x → y₁)) (⊤ {lzero}) l
      aux {[]} _ _ = triv
      aux {inj₁ x :: l} (s₁ , s₂) x₂ = s₁ , aux {l} s₂ x₂
      aux {inj₂ y :: l} x₁ (s₁ , s₂) = s₁ , aux {l} x₁ s₂

-- This shows that f ≡ (f,g);π₁.
cart-diag₁ : {A B C : Obj}
  → {f : Hom C A}
  → {g : Hom C B}
  → _≡h_ { Jₒ C}{ Jₒ A}
    (!ₐ {C}{A} f)
    (comp { Jₒ C}
          {(Jₒ (A &ₒ B))}
          { Jₒ A}
          (cart-ar
            (!ₐ {C}{A} f) (!ₐ {C}{B} g))
          π₁)
cart-diag₁ {U , X , α}{V , Y , β}{W , Z , γ}{f = f , F , p₁}{g , G , p₂}
  = refl , ext-set (λ {j₁} → ext-set (λ {w} → aux))
  where
    aux : ∀{l : X *} →
      map F l ≡
      map F (proj-⊎₁ {_}{_}{X}{Y} (map inj₁ l)) ++
      map G (proj-⊎₂ (map inj₁ l))
    aux {l} rewrite
      map-proj-⊎₁ {_}{_}{X}{Y} l |
      map-proj-⊎₂-[] {_}{_}{X}{Y} l = sym (++[] (map F l))

-- This shows that g ≡ (f,g);π₂.
cart-diag₂ : {A B C : Obj}
  → {f : Hom C A}
  → {g : Hom C B}
  → _≡h_ { Jₒ C}{ Jₒ B}
    (!ₐ {C}{B} g)
    (comp { Jₒ C}
          {(Jₒ (A &ₒ B))}
          { Jₒ B}
          (cart-ar
            (!ₐ {C}{A} f) (!ₐ {C}{B} g))
          π₂)
cart-diag₂ {U , X , α}{V , Y , β}{W , Z , γ}{f = f , F , p₁}{g , G , p₂}
  = refl , ext-set (λ {j₁} → ext-set (λ {w} → aux))
  where
    aux : ∀{l : Y *} →
      map G l ≡
      map F (proj-⊎₁ {_}{_}{X}{Y} (map inj₂ l)) ++
      map G (proj-⊎₂ {_}{_}{X}{Y} (map inj₂ l))
    aux {l} rewrite map-proj-⊎₂ {_}{_}{X}{Y} l |
                    map-proj-⊎₁-[] {_}{_}{X}{Y} l = refl

term-diag : ∀{A : Obj} → Hom (Jₒ A) (Jₒ (⊤ , ⊥ , λ x y → ⊤))
term-diag {U , X , α} =
  (λ x → triv) , (λ f u → aux (f triv) u) , ((λ {u}{y} → aux' {u}{y triv}))
 where
   aux : 𝕃 ⊥ → U → 𝕃 X
   aux [] u = []
   aux (x :: l) u = ⊥-elim x :: aux l u

   aux' : {u : U} {l : 𝕃 ⊥} →
      foldr (λ a y₁ → Σ (α u a) (λ x → y₁)) (⊤ {lzero}) (aux l u) →
      foldr (λ a y₁ → Σ ⊤ (λ x → y₁)) (⊤ {lzero}) l
   aux' {u}{l = []} p = p
   aux' {u}{l = x :: l} (p , p') = triv , aux' {u}{l} p' 


term-cart-crt₁ : {X : Set₁} → 𝕃 (X ⊎ ⊥) → 𝕃 X
term-cart-crt₁ [] = []
term-cart-crt₁ (inj₁ x :: l) = x :: term-cart-crt₁ l
term-cart-crt₁ (inj₂ y :: l) = ⊥-elim y :: term-cart-crt₁ l

term-cart₁ : ∀{A : Obj} → Hom (Jₒ A) (Jₒ (A &ₒ (⊤ , ⊥ , λ x y → ⊤)))
term-cart₁ {U , X , α} =
  (λ x → x , triv) , (λ f u → term-cart-crt₁ (f (u , triv))) , (λ {u} {l} → cond {u}{l (u , triv)})
 where
   cond : {u : U} {l : 𝕃 (X ⊎ ⊥)} →
      foldr (λ a y₁ → Σ (α u a) (λ x → y₁)) (⊤ {lzero})
      (term-cart-crt₁ l) →
      foldr (λ a y₁ → Σ ((α &ᵣ (λ x y₂ → ⊤)) (u , triv) a) (λ x → y₁)) (⊤ {lzero})
      l
   cond {u}{[]} p = triv
   cond {u}{inj₁ x :: l} (p , p') = p , cond {u}{l} p'
   cond {u}{inj₂ y :: l} (p , p') = triv , cond {u}{l} p'

term-cart₂ : ∀{A : Obj} → Hom (Jₒ (A &ₒ (⊤ , ⊥ , λ x y → ⊤))) (Jₒ A)
term-cart₂ {U , X , α} = π₁


term-cart-iso₁ : ∀{A : Obj}
  → _≡h_ {Jₒ A} {Jₒ A} (comp {Jₒ A}{Jₒ (A &ₒ (⊤ , ⊥ , λ x y → ⊤))}
                             {Jₒ A} term-cart₁ term-cart₂) id
term-cart-iso₁ {U , X , α} = refl , ext-set (λ {f} → ext-set (λ {u} → aux))
 where
   aux : ∀{l : X *} → term-cart-crt₁ (map inj₁ l) ≡ l
   aux {[]} = refl
   aux {x :: l} rewrite aux {l} = refl

term-cart-iso₂ : ∀{A : Obj}
  → _≡h_ {Jₒ (A &ₒ (⊤ , ⊥ , λ x y → ⊤))}
         {Jₒ (A &ₒ (⊤ , ⊥ , λ x y → ⊤))}
         (comp {Jₒ (A &ₒ (⊤ , ⊥ , λ x y → ⊤))}{Jₒ A}
         {Jₒ (A &ₒ (⊤ , ⊥ , λ x y → ⊤))}
         term-cart₂ term-cart₁) id
term-cart-iso₂ {U , X , α} =
  ext-set aux , ext-set (λ {f} → ext-set (aux' {f}))
 where
   aux : {a : Σ U (λ x → ⊤)} → (fst a , triv) ≡ a
   aux {u , triv} = refl

   aux' : {f : Σ U (λ x → ⊤)
     → 𝕃 (X ⊎ ⊥)}{a : Σ U (λ x → ⊤)}
     → map inj₁ (term-cart-crt₁ (f (fst a , triv))) ≡ f a
   aux' {f}{u , triv} = aux''
    where
      aux'' : ∀{l : (X ⊎ ⊥) *} → map inj₁ (term-cart-crt₁ l) ≡ l
      aux'' {[]} = refl
      aux'' {inj₁ x :: l} rewrite aux'' {l} = refl
      aux'' {inj₂ y :: l} = ⊥-elim y

twist-cart : ∀{A B : Obj}
  → Hom (Jₒ (A &ₒ B)) (Jₒ (B &ₒ A)) 
twist-cart {A}{B} = cart-ar {A &ₒ B} {B} {A} π₂ π₁

