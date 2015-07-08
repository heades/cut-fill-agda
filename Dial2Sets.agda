-----------------------------------------------------------------------
-- This file defines Dial₂(Sets) and its SMC structure.              --
-----------------------------------------------------------------------
module Dial2Sets where

open import prelude

-- The objects:
Obj : Set₁
Obj = Σ[ U ∈ Set ] (Σ[ X ∈ Set ] (U → X → Set))

-- The morphisms:
Hom : Obj → Obj → Set
Hom (U , X , α) (V , Y , β) =
  Σ[ f ∈ (U → V) ]
    (Σ[ F ∈ (Y → X) ] (∀{u : U}{y : Y} → α u (F y) → β (f u) y))

-- Composition:
comp : {A B C : Obj} → Hom A B → Hom B C → Hom A C
comp {(U , X , α)} {(V , Y , β)} {(W , Z , γ)} (f , F , p₁) (g , G , p₂) =
  (g ∘ f , F ∘ G , (λ {u z} p-α → p₂ (p₁ p-α)))

infixl 5 _○_

_○_ = comp

-- The contravariant hom-functor:
Homₐ :  {A' A B B' : Obj} → Hom A' A → Hom B B' → Hom A B → Hom A' B'
Homₐ f h g = comp f (comp g h)

-- The identity function:
id : {A : Obj} → Hom A A 
id {(U , V , α)} = (id-set , id-set , id-set)

-- In this formalization we will only worry about proving that the
-- data of morphisms are equivalent, and not worry about the morphism
-- conditions.  This will make proofs shorter and faster.
--
-- If we have parallel morphisms (f,F) and (g,G) in which we know that
-- f = g and F = G, then the condition for (f,F) will imply the
-- condition of (g,G) and vice versa.  Thus, we can safly ignore it.
infix 4 _≡h_

_≡h_ : {A B : Obj} → (f g : Hom A B) → Set
_≡h_ {(U , X , α)}{(V , Y , β)} (f , F , p₁) (g , G , p₂) = f ≡ g × F ≡ G

-----------------------------------------------------------------------
-- Dial₂(Sets) is a SMC                                              --
-----------------------------------------------------------------------

-- The tensor functor: ⊗
_⊗ᵣ_ : ∀{U X V Y : Set} → (U → X → Set) → (V → Y → Set) → ((U × V) → ((V → X) × (U → Y)) → Set)
_⊗ᵣ_ α β (u , v) (f , g) = (α u (f v)) × (β v (g u))

_⊗ₒ_ : (A B : Obj) → Obj
(U , X , α) ⊗ₒ (V , Y , β) = ((U × V) , ((V → X) × (U → Y)) , α ⊗ᵣ β)

F⊗ : ∀{S Z W T V X U Y : Set}{f : U → W}{F : Z → X}{g : V → S}{G : T → Y} → (S → Z) × (W → T) → (V → X) × (U → Y)
F⊗ {f = f}{F}{g}{G} (h₁ , h₂) = (λ v → F(h₁ (g v))) , (λ u → G(h₂ (f u)))
  
_⊗ₐ_ : {A B C D : Obj} → Hom A C → Hom B D → Hom (A ⊗ₒ B) (C ⊗ₒ D)
_⊗ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) = ⟨ f , g ⟩ , F⊗ {f = f}{F}{g}{G} , p
 where
  p : {u : U × V} {y : (S → Z) × (W → T)} → (α ⊗ᵣ β) u ((F⊗ {f = f}{F}{g}{G}) y) → (γ ⊗ᵣ δ) (⟨ f , g ⟩ u) y
  p {(u , v)} {(h₁ , h₂)} (p-α , p-β) = p₁ p-α , p₂ p-β

-- The unit for tensor:
ι : ⊤ → ⊤ → Set
ι triv triv = ⊤

I : Obj
I = (⊤ , ⊤ , ι)

-- The left-unitor:
λ⊗-p : ∀{U X α}{u : ⊤ × U} {x : X} → (ι ⊗ᵣ α) u ((λ _ → triv) , (λ _ → x)) → α (snd u) x
λ⊗-p {U}{X}{α}{(triv , u)}{x} (triv , p-α) = p-α
   
λ⊗ : ∀{A : Obj} → Hom (I ⊗ₒ A) A
λ⊗ {(U , X , α)} = snd , (λ x → (λ _ → triv) , (λ _ → x)) , λ⊗-p

λ⁻¹⊗ : ∀{A : Obj} → Hom A (I ⊗ₒ A)
λ⁻¹⊗ {(U , X , α)} = (λ u → triv , u) , ((λ x → snd x triv) , λ⁻¹⊗-p)  
 where
  λ⁻¹⊗-p : ∀{U X α} → {u : U} {y : (U → ⊤) × (⊤ → X)} → α u (snd y triv) → (ι ⊗ᵣ α) (triv , u) y
  λ⁻¹⊗-p {U}{X}{α}{u}{(h₁ , h₂)} p-α with h₁ u
  ... | triv = triv , p-α

-- The right-unitor:
ρ⊗ : ∀{A : Obj} → Hom (A ⊗ₒ I) A
ρ⊗ {(U , X , α)} = fst , (λ x → (λ x₁ → x) , (λ x₁ → triv)) , ρ⊗-p
 where
  ρ⊗-p : ∀{U X α}{u : U × ⊤}{x : X} → (α ⊗ᵣ ι) u ((λ _ → x) , (λ _ → triv)) → α (fst u) x
  ρ⊗-p {U}{X}{α}{(u , triv)}{x} (p-α , triv) = p-α

ρ⊗-inv : ∀{A : Obj} → Hom A (A ⊗ₒ I)
ρ⊗-inv {(U , X , α)} = (λ x → x , triv) , (λ x → fst x triv) , ρ⊗-p-inv
 where
  ρ⊗-p-inv : ∀{U X α}{u : U} {y : Σ (⊤ → X) (λ x → U → ⊤)} → α u (fst y triv) → (α ⊗ᵣ ι) (u , triv) y
  ρ⊗-p-inv {U}{X}{α}{u}{(f , g)} p-α rewrite single-range {g = g}{u} = p-α , triv

-- Symmetry:
β⊗ : ∀{A B : Obj} → Hom (A ⊗ₒ B) (B ⊗ₒ A)
β⊗ {(U , X , α)}{(V , Y , β)} = twist-× , twist-× , β⊗-p
 where
   β⊗-p : ∀{U V Y X α β} → {u : U × V} {y : (U → Y) × (V → X)} →
       (α ⊗ᵣ β) u (twist-× y) → (β ⊗ᵣ α) (twist-× u) y
   β⊗-p {U}{V}{Y}{X}{α}{β}{(u , v)}{(h₁ , h₂)} p-α = twist-× p-α

-- The associator:
α⊗-inv : ∀{A B C : Obj} → Hom (A ⊗ₒ (B ⊗ₒ C)) ((A ⊗ₒ B) ⊗ₒ C)
α⊗-inv {(U , X , α)}{(V , Y , β)}{(W , Z , γ)} = rl-assoc-× , Fα-inv , α-inv-cond
 where
   Fα-inv : (W → (V → X) × (U → Y)) × (U × V → Z) → (V × W → X) × (U → (W → Y) × (V → Z))
   Fα-inv = (λ p → (λ p' → fst ((fst p) (snd p')) (fst p')) , (λ u → (λ w → snd (fst p w) u) , (λ v → (snd p) (u , v))))
   α-inv-cond : ∀{u : U × V × W} {y : (W → (V → X) × (U → Y)) × (U × V → Z)} → (α ⊗ᵣ (β ⊗ᵣ γ)) u (Fα-inv y) → ((α ⊗ᵣ β) ⊗ᵣ γ) (rl-assoc-× u) y
   α-inv-cond {(u , v , w)} {(h₁ , h₂)} (p₁ , p₂ , p₃) with h₁ w
   ... | (a , b) = (p₁ , p₂) , p₃

Fα : ∀{V W X Y U V Z : Set} → Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z))
       → Σ (W → Σ (V → X) (λ x → U → Y)) (λ x → Σ U (λ x₁ → V) → Z)
Fα (f ,  g) = (λ x → (λ x₁ → f ((x₁ , x))) , (λ x₁ → fst (g x₁) x)) , (λ x → snd (g (fst x)) (snd x))

α⊗ : ∀{A B C : Obj} → Hom ((A ⊗ₒ B) ⊗ₒ C) (A ⊗ₒ (B ⊗ₒ C)) 
α⊗ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)} = (lr-assoc-× , Fα {V} , α-cond)
 where
  α-cond : {u : Σ (Σ U (λ x → V)) (λ x → W)}{y : Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z))} →
      ((α ⊗ᵣ β) ⊗ᵣ γ) u (Fα {V} y) → (α ⊗ᵣ (β ⊗ᵣ γ)) (lr-assoc-× u) y
  α-cond {(u , v) , w}{(f , g)} ((p₁ , p₂) , p₃) with g u
  ... | (h₁ , h₂) = p₁ , p₂ , p₃

-- Internal hom:
⊸-cond : ∀{U V X Y : Set} → (U → X → Set) → (V → Y → Set) → (U → V) × (Y → X) → U × Y → Set
⊸-cond α β (f , g) (u , y) = α u (g y) → β (f u) y

_⊸ₒ_ : Obj → Obj → Obj
(U , X , α) ⊸ₒ (V , Y , β) = ((U → V) × (Y → X)) , (U × Y) , ⊸-cond α β

_⊸ₐ_ : {A B C D : Obj} → Hom C A → Hom B D → Hom (A ⊸ₒ B) (C ⊸ₒ D)
_⊸ₐ_ {(U , X , α)}{(V , Y , β)}{(W , Z , γ)}{(S , T , δ)} (f , F , p₁) (g , G , p₂) =
  h , H , p₃
  where
   h : Σ (U → V) (λ x → Y → X) → Σ (W → S) (λ x → T → Z)
   h (h₁ , h₂) = (λ w → g (h₁ (f w))) , (λ t → F (h₂ (G t)))
   H : Σ W (λ x → T) → Σ U (λ x → Y)
   H (w , t) = f w , G t
   p₃ : {u : Σ (U → V) (λ x → Y → X)} {y : Σ W (λ x → T)} → ⊸-cond α β u (H y) → ⊸-cond γ δ (h u) y
   p₃ {h₁ , h₂}{w , t} c c' = p₂ (c (p₁ c'))

-- The of-course exponential:
!ₒ-cond : ∀{U X : Set}
  → (U → X → Set)
  → U
  → (U → X *)
  → Set
!ₒ-cond α u f = all-pred (α u) (f u)
   
!ₒ : Obj → Obj
!ₒ (U , X , α) = U , (U → X *) , !ₒ-cond α

!-cta : {V Y U X : Set}
  → (Y → X)
  → (U → V)
  → (V → Y *)
  → (U → X *)
!-cta F f g = λ u → list-funct F (g (f u))

!ₐ-cond : ∀{U V Y X : Set}{F : Y → X}{f : U → V}
  → (α : U → X → Set)
  → (β : V → Y → Set)
  → (p : {u : U} {y : Y} → α u (F y) → β (f u) y)
    {u : U}{l : Y *}
  → all-pred (α u) (list-funct F l)
  → all-pred (β (f u)) l
!ₐ-cond _ _ _ {l = []} _ = triv
!ₐ-cond α β p {u}{x :: xs} (p' , p'') = p p' , !ₐ-cond α β p p''     
      
!ₐ : {A B : Obj} → Hom A B → Hom (!ₒ A) (!ₒ B)
!ₐ {U , X , α}{V , Y , β} (f , F , p) = f , !-cta F f , !ₐ-cond α β p

-- Of-course is a comonad:
ε : ∀{A} → Hom (!ₒ A) A
ε {U , X , α} = id-set , (λ x y → [ x ]) , fst

δ-cta : {U X : Set} → (U → 𝕃 (U → 𝕃 X)) → U → 𝕃 X
δ-cta g u = foldr (λ f rest → (f u) ++ rest) [] (g u)
  
δ : ∀{A} → Hom (!ₒ A) (!ₒ (!ₒ A))
δ {U , X , α} = id-set , δ-cta , δ-cond
  where
   δ-cond : {u : U} {l : 𝕃 (U → 𝕃 X)}
     → all-pred (α u) (foldr (λ f → _++_ (f u)) [] l)
     → all-pred (λ f
     → all-pred (α u) (f u)) l
   δ-cond {l = []} _ = triv
   δ-cond {u}{l = x :: l'} p with
     all-pred-append {X}{α u}
                     {x u}
                     {foldr (λ f → _++_ (f u)) [] l'}
                     ∧-unit ∧-assoc
   ... | p' rewrite p' = fst p , δ-cond {u} {l'} (snd p)

-- These diagrams can be found on page 22 of the report.
comonand-diag₁ : ∀{A}
  → (δ {A}) ○ (!ₐ (δ {A})) ≡h (δ {A}) ○ (δ { !ₒ A})
comonand-diag₁ {U , X , α} =
  refl , ext-set (λ {a} → ext-set (λ {a₁} → aux {a₁}{a a₁}))
 where
   aux : ∀{a₁ : U}{l : 𝕃 (U → 𝕃 (U → 𝕃 X))} →
      foldr (λ f → _++_ (f a₁)) []
      (map (λ g u → foldr (λ f → _++_ (f u)) [] (g u)) l)
      ≡
      foldr (λ f → _++_ (f a₁)) [] (foldr (λ f → _++_ (f a₁)) [] l)
   aux {a}{[]} = refl  
   aux {a}{x :: l} rewrite
     sym (foldr-append {l₁ = x a}{foldr (λ f → _++_ (f a)) [] l}{a})
     = cong2 {a = foldr (λ f → _++_ (f a)) [] (x a)}
             _++_
             refl
             (aux {a}{l})

comonand-diag₂ : ∀{A}
  → (δ {A}) ○ (ε { !ₒ A}) ≡h (δ {A}) ○ (!ₐ (ε {A}))
comonand-diag₂ {U , X , α} =
  refl , ext-set (λ {f} → ext-set (λ {a} → aux {a}{f a}))
 where
  aux : ∀{a : U}{l : X *}
    → l ++ [] ≡ foldr (λ f₁ → _++_ (f₁ a)) [] (map (λ x y → x :: []) l)
  aux {a}{[]} = refl
  aux {a}{x :: l} with aux {a}{l}
  ... | IH rewrite ++[] l =
    cong2 {a = x} {x} {l}
          {foldr (λ f₁ → _++_ (f₁ a)) [] (map (λ x₁ y → x₁ :: []) l)} _::_ refl
          IH
          
module Cartesian where
  π₁ : {U X V Y : Set}
    → {α : U → X → Set}
    → {β : V → Y → Set}
    → Hom ((!ₒ (U , X , α)) ⊗ₒ (!ₒ (V , Y , β))) (!ₒ (U , X , α))
  π₁ {U}{X}{V}{Y}{α}{β} = fst , (λ f → (λ v u → f u) , (λ u v → [])) , π₁-cond
    where
      π₁-cond : ∀{u : Σ U (λ x → V)} {y : U → 𝕃 X} →
        ((λ u₁ f → all-pred (α u₁) (f u₁)) ⊗ᵣ
        (λ u₁ f → all-pred (β u₁) (f u₁)))
        u ((λ v u₁ → y u₁) , (λ u₁ v → [])) →
        all-pred (α (fst u)) (y (fst u))
      π₁-cond {u , v}{f} (p₁ , p₂) = p₁

  π₂ : {U X V Y : Set}
      → {α : U → X → Set}
      → {β : V → Y → Set}
      → Hom ((!ₒ (U , X , α)) ⊗ₒ (!ₒ (V , Y , β))) (!ₒ (V , Y , β))
  π₂ {U}{X}{V}{Y}{α}{β} = snd , (λ f → (λ v u → []) , (λ u v → f v)) , π₂-cond
      where
        π₂-cond : ∀{u : Σ U (λ x → V)} {y : V → 𝕃 Y} →
          ((λ u₁ f → all-pred (α u₁) (f u₁)) ⊗ᵣ
            (λ u₁ f → all-pred (β u₁) (f u₁)))
              u ((λ v u₁ → []) , (λ u₁ v → y v)) →
            all-pred (β (snd u)) (y (snd u))
        π₂-cond {u , v}{f} (p₁ , p₂) = p₂

  cart-ar-crt : {U X V Y W Z : Set}
    → {α : U → X → Set}
    → {β : V → Y → Set}
    → {γ : W → Z → Set}
    → Hom (!ₒ (W , Z , γ)) (!ₒ (U , X , α))
    → Hom (!ₒ (W , Z , γ)) (!ₒ (V , Y , β))
    → Σ (V → U → 𝕃 X) (λ x → U → V → 𝕃 Y) → W → 𝕃 Z
  cart-ar-crt  (f , F , p₁) (g , G , p₂) (j₁ , j₂) w = F (j₁ (g w)) w ++ G (j₂ (f w)) w

  cart-ar : {U X V Y W Z : Set}
    → {α : U → X → Set}
    → {β : V → Y → Set}
    → {γ : W → Z → Set}
    → Hom (!ₒ (W , Z , γ)) (!ₒ (U , X , α))
    → Hom (!ₒ (W , Z , γ)) (!ₒ (V , Y , β))
    → Hom (!ₒ (W , Z , γ)) ((!ₒ (U , X , α)) ⊗ₒ (!ₒ (V , Y , β)))
  cart-ar {U}{X}{V}{Y}{W}{Z}{α}{β}{γ} (f , F , p₁) (g , G , p₂)
    = (λ w → f w , g w) , cart-ar-crt {α = α}{β} (f , F , p₁) (g , G , p₂) , cart-ar-cond
      where
        cart-ar-cond : ∀{u : W} {y : Σ (V → U → 𝕃 X) (λ x → U → V → 𝕃 Y)} →
          all-pred (γ u) (cart-ar-crt {α = α}{β} (f , F , p₁) (g , G , p₂) y u) →
          ((λ u₁ f₁ → all-pred (α u₁) (f₁ u₁)) ⊗ᵣ
          (λ u₁ f₁ → all-pred (β u₁) (f₁ u₁)))
          (f u , g u) y
        cart-ar-cond {w}{j₁ , j₂} p
          rewrite
            all-pred-append {f = γ w}{F (j₁ (g w)) w}{G (j₂ (f w)) w} ∧-unit ∧-assoc with p
        ... | (a , b) = p₁ a , p₂ b

  cart-diag₁ : {U X V Y W Z : Set}
    → {α : U → X → Set}
    → {β : V → Y → Set}
    → {γ : W → Z → Set}
    → {f : Hom (W , Z , γ) (U , X , α)}
    → {g : Hom (W , Z , γ) (V , Y , β)}
    → _≡h_ { !ₒ (W , Z , γ)}{ !ₒ (U , X , α)}
      (!ₐ {W , Z , γ}{U , X , α} f)
      (comp { !ₒ (W , Z , γ)}
            {((!ₒ (U , X , α)) ⊗ₒ (!ₒ (V , Y , β)))}
            { !ₒ (U , X , α)}
            (cart-ar {α = α}{β}{γ} (!ₐ {W , Z , γ}{U , X , α} f) (!ₐ {W , Z , γ}{V , Y , β} g))
            π₁)
  cart-diag₁ {f = f , F , p₁}{g , G , p₂}
    = refl , ext-set (λ {j} → ext-set (λ {w} → sym (++[] (map F (j (f w))))))

  cart-diag₂ : {U X V Y W Z : Set}
    → {α : U → X → Set}
    → {β : V → Y → Set}
    → {γ : W → Z → Set}
    → {f : Hom (W , Z , γ) (U , X , α)}
    → {g : Hom (W , Z , γ) (V , Y , β)}
    → _≡h_ { !ₒ (W , Z , γ)}{ !ₒ (V , Y , β)}
      (!ₐ {W , Z , γ}{V , Y , β} g)
      (comp { !ₒ (W , Z , γ)}
            {((!ₒ (U , X , α)) ⊗ₒ (!ₒ (V , Y , β)))}
            { !ₒ (V , Y , β)}
            (cart-ar {α = α}{β}{γ} (!ₐ {W , Z , γ}{U , X , α} f) (!ₐ {W , Z , γ}{V , Y , β} g))
            π₂)
  cart-diag₂ {f = f , F , p₁}{g , G , p₂}
    = refl , ext-set (λ {j} → ext-set (λ {w} → refl))
