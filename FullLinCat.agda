-----------------------------------------------------------------------
-- This file formalizes the proof that Dial₂(Sets) is a full linear  --
-- category.  See Lemma 12 of the paper.                             --
-----------------------------------------------------------------------
module FullLinCat where

open import prelude
open import Dial2Sets

-- Monoidal nat. trans. m⊤ : ⊤ → !⊤:
m⊤ : Hom I (!ₒ I)
m⊤ = id-set , (λ f → triv) , m⊤-cond
 where
  m⊤-cond : {u : ⊤} {l : 𝕃 ⊤} → ι u triv → all-pred (ι u) l
  m⊤-cond {triv}{[]} triv = triv
  m⊤-cond {triv}{triv :: l} triv = triv , m⊤-cond {triv}{l} triv

-- These diagrams can be found on page 23 of the report.
m⊤-diag₁ : _≡h_ {I}{ !ₒ (!ₒ I)}
  (comp {I} { !ₒ I} { !ₒ (!ₒ I)} m⊤ (!ₐ {I}{ !ₒ I} m⊤))
  (comp {I} { !ₒ I} { !ₒ (!ₒ I)} m⊤ (δ {I}))
m⊤-diag₁ = refl , refl

m⊤-diag₂ : _≡h_ {I}{I} (comp {I}{ !ₒ I}{I} m⊤ (ε {I})) (id {I})
m⊤-diag₂ = refl , ext-set aux
 where
  aux : {a : ⊤} → triv ≡ a
  aux {triv} = refl

-- The monoidal nat. trans. m : !A ⊗ !B → !(A ⊗ B):
h'₁ : {U V X Y : Set} → (((V → X) × (U → Y)) *) → (V → U → (X *))
h'₁ [] v u = []
h'₁ ((j₁ , j₂) :: js) v u = (j₁ v) :: h'₁ js v u

h'₁-append : ∀{U V X Y : Set}{l₁ l₂ : ((V → X) × (U → Y)) *}{v u}
  → (h'₁ l₁ v u) ++ (h'₁ l₂ v u) ≡ h'₁ (l₁ ++ l₂) v u
h'₁-append {l₁ = []} = refl
h'₁-append {l₁ = (j₁ , j₂) :: js}{l₂}{v}{u}
  rewrite h'₁-append {l₁ = js}{l₂}{v}{u} = refl

h₁ : {U V X Y : Set}
  → ((U × V)
  → (((V → X) × (U → Y)) *))
  → (V → U → (X *))
h₁ g v u = h'₁ (g (u , v)) v u

h'₂ : {U V X Y : Set}
  → (((V → X) × (U → Y)) *)
  → (U → V → (Y *))
h'₂ [] u v = []
h'₂ ((j₁ , j₂) :: js) u v = (j₂ u) :: h'₂ js u v

h'₂-append : ∀{U V X Y : Set}{l₁ l₂ : ((V → X) × (U → Y)) *}{v u}
  → (h'₂ l₁ v u) ++ (h'₂ l₂ v u) ≡ h'₂ (l₁ ++ l₂) v u
h'₂-append {l₁ = []} = refl
h'₂-append {l₁ = (j₁ , j₂) :: js}{l₂}{v}{u}
  rewrite h'₂-append {l₁ = js}{l₂}{v}{u} = refl

h₂ : {U V X Y : Set}
  → ((U × V)
  → (((V → X) × (U → Y)) *))
  → (U → V → (Y *))
h₂ g u v = h'₂ (g (u , v)) u v

m⊗ : {A B : Obj} → Hom ((!ₒ A) ⊗ₒ (!ₒ B)) (!ₒ (A ⊗ₒ B))
m⊗ {U , X , α} {V , Y , β} =
  id-set , (λ g → h₁ g , h₂ g) , (λ {u}{y} x → m⊗-cond {u}{y} x)
 where
  m⊗-cond : {u : Σ U (λ x → V)}
      {y : Σ U (λ x → V) → 𝕃 (Σ (V → X) (λ x → U → Y))} →
      ((λ u₁ f → all-pred (α u₁) (f u₁)) ⊗ᵣ
       (λ u₁ f → all-pred (β u₁) (f u₁)))
      u
      ((λ v u₁ → h'₁ (y (u₁ , v)) v u₁) ,
       (λ u₁ v → h'₂ (y (u₁ , v)) u₁ v)) →
      all-pred ((α ⊗ᵣ β) u) (y u)
  m⊗-cond {(u , v)}{g} (p₁ , p₂) = aux p₁ p₂
   where
    aux : ∀{l}
        → all-pred (α u) (h'₁ l v u)
        → all-pred (β v) (h'₂ l u v)
        → all-pred ((α ⊗ᵣ β) (u , v)) l
    aux {[]} p₁ p₂ = triv
    aux {(j₁ , j₂) :: js} (p₁ , p₂) (p₃ , p₄) = (p₁ , p₃) , aux {js} p₂ p₄

-- The following diagrams can be found on page 24 of the report.
m⊗-diag-A : ∀{A}
  → (m⊤ ⊗ₐ (id { !ₒ A})) ○ (m⊗ {I} {A} ○ !ₐ (λ⊗ {A})) ≡h λ⊗ { !ₒ A}
m⊗-diag-A {U , X , α} = ext-set (λ {a} → aux {a}) ,
                        ext-set (λ {g} → cong2 _,_ refl (ext-set (aux' {g})))
 where
  aux : {a : Σ ⊤ (λ x → U)}
    → snd (⟨ (λ x → x) , (λ x → x) ⟩ a) ≡ snd a
  aux {triv , u} = refl
  aux' : {g : U → X *} → {a : ⊤}
    → (λ v → h'₂ (map (λ x → (λ _ → triv) , (λ _ → x)) (g v)) a v) ≡ g
  aux' {g}{triv} = ext-set (λ {a} → aux'' {a}{g a})
   where
    aux'' : {a : U}{l : X *}
      → h'₂ (map (λ x → (λ _ → triv) , (λ _ → x)) l) triv a ≡ l
    aux'' {u}{[]} = refl
    aux'' {u}{x :: xs} rewrite aux'' {u}{xs} = refl

m⊗-diag-B : ∀{A}
  → ((id { !ₒ A}) ⊗ₐ m⊤) ○ (m⊗ {A} {I} ○ !ₐ (ρ⊗ {A})) ≡h ρ⊗ { !ₒ A}
m⊗-diag-B {U , X , α} =
  (ext-set (λ {a} → aux {a})) , ext-set (λ {g} → cong2 _,_ (ext-set aux') refl)
 where
   aux : {a : Σ U (λ x → ⊤)}
     → fst (⟨ (λ x → x) , (λ x → x) ⟩ a) ≡ fst a
   aux {u , triv} = refl
   aux' : {g : U → X *} → {a : ⊤}
     → (λ u → h'₁ (map (λ x → (λ x₁ → x) , (λ x₁ → triv)) (g u)) a u) ≡ g
   aux' {g}{triv} = ext-set (λ {u} →  aux'' {g u}{u})
    where
      aux'' : ∀{l : X *}{u : U}
        → h'₁ (map (λ x → (λ x₁ → x) , (λ x₁ → triv)) l) triv u ≡ l
      aux'' {[]}{u}  = refl
      aux'' {x :: xs}{u} rewrite aux'' {xs}{u} = refl

m⊗-diag-C : ∀{A B}
  → β⊗ { !ₒ A} { !ₒ B} ○ m⊗ {B} {A} ≡h (m⊗ {A}{B}) ○ (!ₐ (β⊗ {A}{B}))
m⊗-diag-C {U , X , α}{V , Y , β} =
          refl ,
          ext-set (λ {g} →
               cong2 _,_ (ext-set (λ {v} → ext-set (λ {u} → aux {g (v , u)}{u}{v})))
                         (ext-set (λ {u} → ext-set (λ {v} → aux' {g (v , u)}{u}{v}))))
 where
   aux : ∀{l : 𝕃 (Σ (U → Y) (λ x → V → X))}{u v}
     → h'₂ l v u ≡  h'₁ (map twist-× l) v u
   aux {[]} = refl
   aux {(j₁ , j₂) :: js} {u}{v} rewrite aux {js}{u}{v} = refl
   aux' : ∀{l : 𝕃 (Σ (U → Y) (λ x → V → X))}{u v}
     → h'₁ l u v ≡  h'₂ (map twist-× l) u v
   aux' {[]} = refl
   aux' {(j₁ , j₂) :: js} {u}{v} rewrite aux' {js}{u}{v} = refl

m⊗-diag-D : ∀{A B C : Obj}
  →  α⊗ { !ₒ A} { !ₒ B} { !ₒ C} ○ id { !ₒ A} ⊗ₐ m⊗ {B} {C} ○ m⊗ {A} {B ⊗ₒ C}
  ≡h ((m⊗ {A}{B}) ⊗ₐ (id { !ₒ C})) ○ (m⊗ {A ⊗ₒ B}{C}) ○ (!ₐ (α⊗ {A}{B}{C})) 
m⊗-diag-D {U , X , α}{V , Y , β}{W , Z , γ} =
  ext-set aux  ,
  ext-set (λ {g} →
    cong2 _,_
          (ext-set
             (λ {w} → cong2 _,_
                            (ext-set
                               (λ {v} → ext-set
                                          (λ {u} → aux' {g (u , v , w)}{u}{v}{w})))
                            (ext-set (λ {u} → ext-set (λ {v} → aux'' {g (u , v , w)}{u}{v}{w})))))
          (ext-set (λ {a} → aux''' {a}{g})))
 where
  aux : {a : Σ (Σ U (λ x → V)) (λ x → W)}
    → ⟨ (λ x → x) , (λ x → x) ⟩ (lr-assoc-× a) ≡ lr-assoc-× (⟨ (λ x → x) , (λ x → x) ⟩ a)
  aux {((u , v) , w)} = refl
  aux' : ∀{l : 𝕃 (Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z)))}{u v w}
    → h'₁ l (v , w) u ≡ h'₁ (h'₁ (map (Fα {V}{W}{X}{Y}{U}{V}{Z}) l) w (u , v)) v u
  aux' {[]} = refl
  aux' {(j₁ , j₂) :: js}{u}{v}{w} rewrite aux' {js}{u}{v}{w} = refl
  aux'' : ∀{l : 𝕃 (Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z)))}{u v w}
    → h'₁ (h'₂ l u (v , w)) w v ≡ h'₂ (h'₁ (map (Fα {V}{W}{X}{Y}{U}{V}{Z}) l) w (u , v)) u v
  aux'' {[]} = refl
  aux'' {(j₁ , j₂) :: js}{u}{v}{w} with j₂ u
  ... | (j₃ , j₄) rewrite aux'' {js}{u}{v}{w} = refl
  aux''' : ∀{a : Σ U (λ x → V)}{g : Σ U (λ x → Σ V (λ x₁ → W)) →
    𝕃 (Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z)))} →
       (λ v →
          h'₂ (h'₂ (g (fst a , snd a , v)) (fst a) (snd a , v)) (snd a) v)
       ≡ (λ v → h'₂ (map (Fα {V}{W}{X}{Y}{U}{V}{Z}) (g (lr-assoc-× (a , v)))) a v)
  aux''' {u , v}{g} = ext-set (λ {w} → aux'''' {g (u , v , w)}{w})
   where
     aux'''' : ∀{l : 𝕃 (Σ (Σ V (λ x → W) → X) (λ x → U → Σ (W → Y) (λ x₁ → V → Z)))}{w : W}
       → h'₂ (h'₂ l u (v , w)) v w ≡ h'₂ (map (Fα {V}{W}{X}{Y}{U}{V}{Z}) l) (u , v) w
     aux'''' {[]} = refl
     aux'''' {(j₁ , j₂) :: js}{w} with j₂ u
     ... | (j₃ , j₄) rewrite aux'''' {js}{w} = refl

-- The following diagrams can be found on the bottom of page 26.
m⊗-diag-E : ∀{A B : Obj} → ε {A} ⊗ₐ ε {B} ≡h (m⊗ {A}{B}) ○ (ε {A ⊗ₒ B})
m⊗-diag-E {U , X , α}{V , Y , β} = ext-set aux , ext-set aux'
 where
  aux : {a : Σ U (λ x → V)} → ⟨ (λ x → x) , (λ x → x) ⟩ a ≡ a
  aux {u , v} = refl
  aux' : {a : Σ (V → X) (λ x → U → Y)}
    →   F⊗ {f = λ x → x} {λ x y → x :: []}{λ x → x} {λ x y → x :: []} a
      ≡ ((λ v u → h'₁ (a :: []) v u) , (λ u v → h'₂ (a :: []) u v))
  aux' {j₁ , j₂} = refl  

m⊗-diag-F : ∀{A B : Obj}
  → δ {A} ⊗ₐ δ {B} ○ m⊗ { !ₒ A} { !ₒ B} ○ !ₐ (m⊗ {A} {B}) ≡h (m⊗ {A}{B}) ○ (δ {A ⊗ₒ B})
m⊗-diag-F {U , X , α}{V , Y , β} =
  ext-set aux , ext-set (λ {g} →
    cong2 _,_ (ext-set (λ {v} → ext-set (λ {u} → aux' {g (u , v)}{v}{u})))
              (ext-set (λ {u} → ext-set (λ {v} → aux'' {g (u , v)}{v}{u}))))
 where
   aux : {a : Σ U (λ x → V)} → ⟨ (λ x → x) , (λ x → x) ⟩ a ≡ a
   aux {u , v} = refl
   aux' : ∀{l : 𝕃 (Σ U (λ x → V)
     → 𝕃 (Σ (V → X) (λ x → U → Y)))}{v u}
     → foldr (λ f → _++_ (f u)) []
      (h'₁
       (map
        (λ g₁ →
           (λ v₁ u₁ → h'₁ (g₁ (u₁ , v₁)) v₁ u₁) ,
           (λ u₁ v₁ → h'₂ (g₁ (u₁ , v₁)) u₁ v₁))
        l)
       v u)
      ≡ h'₁ (foldr (λ f → _++_ (f (u , v))) [] l) v u
   aux' {[]} = refl
   aux' {j :: js}{v}{u} with j (u , v)
   ... | [] rewrite aux' {js}{v}{u} = refl
   ... | (j₁ , j₂) :: js' rewrite aux' {js}{v}{u}
     = cong2 {a = j₁ v} _::_ refl (h'₁-append {l₁ = js'})

   aux'' : ∀{l : 𝕃 (Σ U (λ x → V) → 𝕃 (Σ (V → X) (λ x → U → Y)))}{v u}
     → foldr (λ f → _++_ (f v)) []
      (h'₂
       (map
        (λ g₁ →
           (λ v₁ u₂ → h'₁ (g₁ (u₂ , v₁)) v₁ u₂) ,
           (λ u₂ v₁ → h'₂ (g₁ (u₂ , v₁)) u₂ v₁))
        l)
       u v)
      ≡ h'₂ (foldr (λ f → _++_ (f (u , v))) [] l) u v
   aux'' {[]} = refl
   aux'' {j :: js}{v}{u} with j (u , v)
   ... | [] = aux'' {js}
   ... | (j₁ , j₂) :: js' rewrite aux'' {js}{v}{u}
     = cong2 {a = j₂ u} _::_ refl (h'₂-append {l₁ = js'})

-- Now we show that whenever (!A , δ) is a free comonoid, then we have
-- distinguished nat. trans. e : !A → ⊤ and d : !A → !A ⊗ !A.  These
-- constructions and their diagrams can be found on page 27 of the
-- report.

e : {A : Obj} → Hom (!ₒ A) I
e {U , X , α} = (λ x → triv) , (λ x u → []) , (λ {u}{y} x → e-cond {u}{y} x)
 where
   e-cond : {u : U} {y : ⊤} → ⊤ → ι triv y
   e-cond {u}{triv} triv = triv

θ : ∀{U X : Set} → ((U → U → (X *)) × (U → U → (X *))) → U → X *
θ {U}{X} (f , g) u = (f u u) ++ (g u u)

d : {A : Obj} → Hom (!ₒ A) ((!ₒ A) ⊗ₒ (!ₒ A))
d {U , X , α} = (λ x → (x , x)) , θ , d-cond
 where
   d-cond : {u : U} {y : Σ (U → U → 𝕃 X) (λ x → U → U → 𝕃 X)} →
      all-pred (α u) (θ y u) →
      ((λ u₁ f → all-pred (α u₁) (f u₁)) ⊗ᵣ
       (λ u₁ f → all-pred (α u₁) (f u₁)))
      (u , u) y
   d-cond {u}{f , g} = aux
    where
      aux : ∀{l₁ l₂ : X *}
        → all-pred (α u) (l₁ ++ l₂)
        → ((all-pred (α u) l₁) × (all-pred (α u) l₂))
      aux {[]} p = triv , p
      aux {x :: xs} (p₁ , p₂) = (p₁ , fst (aux {xs} p₂)) , snd (aux {xs} p₂)

-- e must be a monoidal nat. trans.
e-diag-G : ∀{A B : Obj}{f : Hom A B} → !ₐ f ○ e {B} ≡h e {A}
e-diag-G {U , X , α}{V , Y , β}{(f , F , _)} = refl , refl

e-diag-H : _≡h_ {I}{I} (comp {I}{ !ₒ I}{I} m⊤ (e {I})) (id {I})
e-diag-H = ext-set aux , ext-set aux
 where
   aux : {a : ⊤} → triv ≡ a
   aux {triv} = refl

e-diag-I : ∀{A B : Obj} → m⊗ {A} {B} ○ e {A ⊗ₒ B} ≡h e {A} ⊗ₐ e {B} ○ λ⊗ {I}
e-diag-I {U , X , α}{V , Y , β} = (ext-set (λ {a} → aux {a})) , refl
 where
   aux : {a : Σ U (λ x → V)} → triv ≡ snd (⟨ (λ x → triv) , (λ x → triv) ⟩ a)
   aux {u , v} = refl

-- d must be a monoidal nat. trans.  The following diagrams can be
-- found on page 28 of the report.
d-diag-J : ∀{A B : Obj}{f : Hom A B} → !ₐ f ○ d {B} ≡h (d {A}) ○ ((!ₐ f) ⊗ₐ (!ₐ f))
d-diag-J {U , X , α}{V , Y , β}{f , F , _} = refl , ext-set (λ {a} → aux {a})
 where
   aux : {a : Σ (V → V → 𝕃 Y) (λ x → V → V → 𝕃 Y)}
     →   (λ u → map F (θ a (f u)))
       ≡ θ (F⊗ {f = f} {λ g u → map F (g (f u))} {f}
               {λ g u → map F (g (f u))} a)
   aux {j₁ , j₂} = ext-set (λ {u} → map-append F (j₁ (f u) (f u)) (j₂ (f u) (f u)))

d-diag-K : _≡h_ {I}{(!ₒ I) ⊗ₒ (!ₒ I)}
  (comp {I}{ !ₒ I}{(!ₒ I) ⊗ₒ (!ₒ I)} m⊤ (d {I}))
  (comp {I}{I ⊗ₒ I}{(!ₒ I) ⊗ₒ (!ₒ I)} (λ⁻¹⊗ {I}) (m⊤ ⊗ₐ m⊤))
d-diag-K = ext-set aux , ext-set (λ {a} → aux' {a})
 where
   aux : {a : ⊤} → (a , a) ≡ (triv , a)
   aux {triv} = refl
   aux' : {a : Σ (⊤ → ⊤ → 𝕃  ⊤) (λ x → ⊤ → ⊤ → 𝕃  ⊤)}
     →   triv
       ≡ (snd (F⊗ {f = λ x → x} {λ f → triv} {λ x → x} {λ f → triv} a) triv)
   aux' {j₁ , j₂} = refl

iso : {A B : Obj} → Hom (((!ₒ A) ⊗ₒ (!ₒ A)) ⊗ₒ ((!ₒ B) ⊗ₒ (!ₒ B)))
                        (((!ₒ A) ⊗ₒ (!ₒ B)) ⊗ₒ ((!ₒ A) ⊗ₒ (!ₒ B)))
iso {A}{B} =
    α⊗ {(!ₒ A)} {(!ₒ A)} {(!ₒ B) ⊗ₒ (!ₒ B)}
  ○ (id {(!ₒ A)} ⊗ₐ α⊗-inv {(!ₒ A)} {(!ₒ B)} {(!ₒ B)}
  ○ (id {(!ₒ A)} ⊗ₐ (β⊗ {(!ₒ A)} {(!ₒ B)} ⊗ₐ id {(!ₒ B)})
  ○ (id {(!ₒ A)} ⊗ₐ α⊗ {(!ₒ B)} {(!ₒ A)} {(!ₒ B)}
  ○ α⊗-inv {(!ₒ A)} {(!ₒ B)} {(!ₒ A) ⊗ₒ (!ₒ B)})))

d-diag-L : ∀{A B : Obj}
  → m⊗ {A} {B} ○ d {A ⊗ₒ B} ≡h ((d {A}) ⊗ₐ (d {B})) ○ (iso ○ ((m⊗ {A}{B}) ⊗ₐ (m⊗ {A}{B}))) 
d-diag-L {U , X , α}{V , Y , β} = ext-set aux , ext-set (λ {a} → aux' {a})
 where
   aux : {a : U × V}
     →   (a , a)
       ≡ ⟨ (λ x → x) , (λ x → x) ⟩
           (rl-assoc-×
             (⟨ (λ x → x) , lr-assoc-× ⟩
             (⟨ (λ x → x) , ⟨ twist-× , (λ x → x) ⟩ ⟩
             (⟨ (λ x → x) , rl-assoc-× ⟩
             (lr-assoc-× (⟨ (λ x → x , x) , (λ x → x , x) ⟩ a))))))
   aux {u , v} = refl
   -- The type of aux' is the fully expanded version of the following type:
   -- ((λ v u → h'₁ (θ a (u , v)) v u) , (λ u v → h'₂ (θ a (u , v)) u v))
   -- ≡ ((λ v u → fst (fst (F⊗ a) (u , v)) v u ++ fst (snd (F⊗ a) (u , v)) v u)
   --    ,
   --    (λ u u₁ → snd (fst (F⊗ a) (u , u₁)) u u₁ ++ snd (snd (F⊗ a) (u , u₁)) u u₁).
   -- Agda's type inference algorithm was having trouble inferring the annotations, and
   -- so we used Agda to generate the fully expanded version.
   aux' : {a
       : Σ {_} {_}
         (Σ {_} {_} U (λ x → V) →
          Σ {_} {_} U (λ x → V) →
          𝕃 {_}
          (Σ {_} {_} (V → X)
           (λ x → U → Y)))
         (λ x →
            Σ {_} {_} U (λ x₁ → V) →
            Σ {_} {_} U (λ x₁ → V) →
            𝕃 {_}
            (Σ {_} {_} (V → X)
             (λ x₁ → U → Y)))} →
      _≡_ {_}
      {Σ {_} {_}
       (V → U → 𝕃 {_} X)
       (λ x → U → V → 𝕃 {_} Y)}
      ((λ v u →
          h'₁ {U} {V} {X} {Y}
          (θ {Σ {_} {_} U (λ x → V)}
           {Σ {_} {_} (V → X)
            (λ x → U → Y)}
           a (u , v))
          v u)
       ,
       (λ u v →
          h'₂ {U} {V} {X} {Y}
          (θ {Σ {_} {_} U (λ x → V)}
           {Σ {_} {_} (V → X)
            (λ x → U → Y)}
           a (u , v))
          u v))
      ((λ v u →
          _++_ {_} {X}
          (fst {_} {_}
           {V → U → 𝕃 {_} X}
           {U → V → 𝕃 {_} Y}
           (fst {_} {_}
            {Σ {_} {_} U (λ x → V) →
             Σ {_} {_}
             (V → U → 𝕃 {_} X)
             (λ x → U → V → 𝕃 {_} Y)}
            {Σ {_} {_} U (λ x → V) →
             Σ {_} {_}
             (V → U → 𝕃 {_} X)
             (λ x → U → V → 𝕃 {_} Y)}
            (F⊗ {Σ {_} {_} U (λ x → V)}
             {Σ {_} {_} U (λ x → V) →
              𝕃 {_}
              (Σ {_} {_} (V → X)
               (λ x → U → Y))}
             {Σ {_} {_} U (λ x → V)}
             {Σ {_} {_} U (λ x → V) →
              𝕃 {_}
              (Σ {_} {_} (V → X)
               (λ x → U → Y))}
             {Σ {_} {_} U (λ x → V)}
             {Σ {_} {_}
              (V → U → 𝕃 {_} X)
              (λ x → U → V → 𝕃 {_} Y)}
             {Σ {_} {_} U (λ x → V)}
             {Σ {_} {_}
              (V → U → 𝕃 {_} X)
              (λ x → U → V → 𝕃 {_} Y)}
             {λ x → x}
             {λ g →
                (λ v₁ u₁ → h'₁ {U} {V} {X} {Y} (g (u₁ , v₁)) v₁ u₁) ,
                (λ u₁ v₁ → h'₂ {U} {V} {X} {Y} (g (u₁ , v₁)) u₁ v₁)}
             {λ x → x}
             {λ g →
                (λ v₁ u₁ → h'₁ {U} {V} {X} {Y} (g (u₁ , v₁)) v₁ u₁) ,
                (λ u₁ v₁ → h'₂ {U} {V} {X} {Y} (g (u₁ , v₁)) u₁ v₁)}
             a)
            (u , v))
           v u)
          (fst {_} {_}
           {V → U → 𝕃 {_} X}
           {U → V → 𝕃 {_} Y}
           (snd {_} {_}
            {Σ {_} {_} U (λ x → V) →
             Σ {_} {_}
             (V → U → 𝕃 {_} X)
             (λ x → U → V → 𝕃 {_} Y)}
            {Σ {_} {_} U (λ x → V) →
             Σ {_} {_}
             (V → U → 𝕃 {_} X)
             (λ x → U → V → 𝕃 {_} Y)}
            (F⊗ {Σ {_} {_} U (λ x → V)}
             {Σ {_} {_} U (λ x → V) →
              𝕃 {_}
              (Σ {_} {_} (V → X)
               (λ x → U → Y))}
             {Σ {_} {_} U (λ x → V)}
             {Σ {_} {_} U (λ x → V) →
              𝕃 {_}
              (Σ {_} {_} (V → X)
               (λ x → U → Y))}
             {Σ {_} {_} U (λ x → V)}
             {Σ {_} {_}
              (V → U → 𝕃 {_} X)
              (λ x → U → V → 𝕃 {_} Y)}
             {Σ {_} {_} U (λ x → V)}
             {Σ {_} {_}
              (V → U → 𝕃 {_} X)
              (λ x → U → V → 𝕃 {_} Y)}
             {λ x → x}
             {λ g →
                (λ v₁ u₁ → h'₁ {U} {V} {X} {Y} (g (u₁ , v₁)) v₁ u₁) ,
                (λ u₁ v₁ → h'₂ {U} {V} {X} {Y} (g (u₁ , v₁)) u₁ v₁)}
             {λ x → x}
             {λ g →
                (λ v₁ u₁ → h'₁ {U} {V} {X} {Y} (g (u₁ , v₁)) v₁ u₁) ,
                (λ u₁ v₁ → h'₂ {U} {V} {X} {Y} (g (u₁ , v₁)) u₁ v₁)}
             a)
            (u , v))
           v u))
       ,
       (λ u u₁ →
          _++_ {_} {Y}
          (snd {_} {_}
           {V → U → 𝕃 {_} X}
           {U → V → 𝕃 {_} Y}
           (fst {_} {_}
            {Σ {_} {_} U (λ x → V) →
             Σ {_} {_}
             (V → U → 𝕃 {_} X)
             (λ x → U → V → 𝕃 {_} Y)}
            {Σ {_} {_} U (λ x → V) →
             Σ {_} {_}
             (V → U → 𝕃 {_} X)
             (λ x → U → V → 𝕃 {_} Y)}
            (F⊗ {Σ {_} {_} U (λ x → V)}
             {Σ {_} {_} U (λ x → V) →
              𝕃 {_}
              (Σ {_} {_} (V → X)
               (λ x → U → Y))}
             {Σ {_} {_} U (λ x → V)}
             {Σ {_} {_} U (λ x → V) →
              𝕃 {_}
              (Σ {_} {_} (V → X)
               (λ x → U → Y))}
             {Σ {_} {_} U (λ x → V)}
             {Σ {_} {_}
              (V → U → 𝕃 {_} X)
              (λ x → U → V → 𝕃 {_} Y)}
             {Σ {_} {_} U (λ x → V)}
             {Σ {_} {_}
              (V → U → 𝕃 {_} X)
              (λ x → U → V → 𝕃 {_} Y)}
             {λ x → x}
             {λ g →
                (λ v u₂ → h'₁ {U} {V} {X} {Y} (g (u₂ , v)) v u₂) ,
                (λ u₂ v → h'₂ {U} {V} {X} {Y} (g (u₂ , v)) u₂ v)}
             {λ x → x}
             {λ g →
                (λ v u₂ → h'₁ {U} {V} {X} {Y} (g (u₂ , v)) v u₂) ,
                (λ u₂ v → h'₂ {U} {V} {X} {Y} (g (u₂ , v)) u₂ v)}
             a)
            (u , u₁))
           u u₁)
          (snd {_} {_}
           {V → U → 𝕃 {_} X}
           {U → V → 𝕃 {_} Y}
           (snd {_} {_}
            {Σ {_} {_} U (λ x → V) →
             Σ {_} {_}
             (V → U → 𝕃 {_} X)
             (λ x → U → V → 𝕃 {_} Y)}
            {Σ {_} {_} U (λ x → V) →
             Σ {_} {_}
             (V → U → 𝕃 {_} X)
             (λ x → U → V → 𝕃 {_} Y)}
            (F⊗ {Σ {_} {_} U (λ x → V)}
             {Σ {_} {_} U (λ x → V) →
              𝕃 {_}
              (Σ {_} {_} (V → X)
               (λ x → U → Y))}
             {Σ {_} {_} U (λ x → V)}
             {Σ {_} {_} U (λ x → V) →
              𝕃 {_}
              (Σ {_} {_} (V → X)
               (λ x → U → Y))}
             {Σ {_} {_} U (λ x → V)}
             {Σ {_} {_}
              (V → U → 𝕃 {_} X)
              (λ x → U → V → 𝕃 {_} Y)}
             {Σ {_} {_} U (λ x → V)}
             {Σ {_} {_}
              (V → U → 𝕃 {_} X)
              (λ x → U → V → 𝕃 {_} Y)}
             {λ x → x}
             {λ g →
                (λ v u₂ → h'₁ {U} {V} {X} {Y} (g (u₂ , v)) v u₂) ,
                (λ u₂ v → h'₂ {U} {V} {X} {Y} (g (u₂ , v)) u₂ v)}
             {λ x → x}
             {λ g →
                (λ v u₂ → h'₁ {U} {V} {X} {Y} (g (u₂ , v)) v u₂) ,
                (λ u₂ v → h'₂ {U} {V} {X} {Y} (g (u₂ , v)) u₂ v)}
             a)
            (u , u₁))
           u u₁)))
   aux' {j₁ , j₂} =
     cong2
      {a = λ v u → h'₁ (j₁ (u , v) (u , v) ++ j₂ (u , v) (u , v)) v u}
      _,_ (ext-set
              (λ {v} → ext-set
                          (λ {u} → sym (h'₁-append
                                          {l₁ = j₁ (u , v) (u , v)}
                                          {l₂ = j₂ (u , v) (u , v)}{v}{u}))))
          (ext-set
              (λ {u} → (ext-set
                           (λ {v} → sym (h'₂-append
                                          {l₁ = j₁ (u , v) (u , v)}
                                          {l₂ = j₂ (u , v) (u , v)}{u}{v})))))

-- Show that (!A, d, e) is a commutative comonoid.  The following
-- diagrams can be found on page 29 of the report.
de-diag-M : ∀{A : Obj}
  → ρ⊗-inv {(!ₒ A)} ≡h (d {A}) ○ ((id {(!ₒ A)}) ⊗ₐ (e {A}))
de-diag-M {U , X , α} = refl , ext-set (λ {a} → aux {a})
 where
   aux : {a : Σ (⊤ → U → 𝕃 X) (λ x → U → ⊤)}
       →   (fst a triv)
         ≡ (θ (F⊗ {f = λ x → x} {λ x → x} {λ x → triv} {λ x u → []} a))
   aux {j₁ , j₂} = ext-set (λ {u} → sym (++[] (j₁ triv u)))

de-diag-N : ∀{A : Obj}
  → λ⁻¹⊗ {(!ₒ A)} ≡h (d {A}) ○ ((e {A}) ⊗ₐ (id {(!ₒ A)}))
de-diag-N {U , X , α} = refl , ext-set (λ {a} → aux {a})
 where
   aux : {a : Σ (U → ⊤) (λ x → ⊤ → U → 𝕃 X)} →
       _≡_ (snd a triv) (θ (F⊗ {f = λ x → triv}
                               {λ x u → []}
                               {λ x → x}
                               {λ x → x} a))
   aux {j₁ , j₂} = refl

de-diag-O : ∀{A : Obj}
  → d {A} ≡h (d {A}) ○ (β⊗ {(!ₒ A)}{(!ₒ A)})
de-diag-O {U , X , α} = refl , ext-set (λ {a} → aux {a})
 where
   aux : {a : Σ (U → U → 𝕃 X) (λ x → U → U → 𝕃 X)}
     → θ a ≡ θ (twist-× a)
   aux {j₁ , j₂} = ext-set (λ {u} → *-comm {l₁ = j₁ u u}{j₂ u u})

de-diag-P : ∀{A : Obj}
  →      (d {A})
       ○ (((d {A}) ⊗ₐ (id {(!ₒ A)}))
       ○ (α⊗ {(!ₒ A)}{(!ₒ A)}{(!ₒ A)}))
    ≡h (d {A}) ○ ((id {(!ₒ A)}) ⊗ₐ (d {A}))
de-diag-P {U , X , α} = refl , ext-set ((λ {a} → aux {a}))
 where
   aux : {a : Σ (Σ U (λ x → U) → U → 𝕃 X)
                    (λ x → U → Σ (U → U → 𝕃 X)
                (λ x₁ → U → U → 𝕃 X))}
     →   (θ (F⊗ {f = λ x → x , x} {θ {U} {X}} {λ x → x} {λ x → x}
                (Fα {U} {U} {U → 𝕃 X} {U → 𝕃 X} {U} {U} {U → 𝕃 X} a)))
       ≡ (θ (F⊗ {Σ U (λ x → U)} {U → 𝕃 X} {U}
                {Σ (U → U → 𝕃 X) (λ x → U → U → 𝕃 X)}
                {U} {U → 𝕃 X} {U} {U → 𝕃 X} {λ x → x}
                {λ x → x} {λ x → x , x} {θ} a))
   aux {x , y} = ext-set (λ {u} → aux')
    where
      aux' : ∀{u : U}
        →   (x (u , u) u ++ fst (y u) u u) ++ snd (y u) u u
          ≡ x (u , u) u ++ θ (y u) u
      aux' {u} with y u
      ... | j₁ , j₂ = ++-assoc (x (u , u) u) (j₁ u u) (j₂ u u)

-- The morphism e and d must be a coalgebra morphisms.  The following
-- diagram can be found on page 30 of the report.
e-diag-Q : ∀{A : Obj}
  → δ {A} ○ !ₐ (e {A}) ≡h (e {A}) ○ m⊤
e-diag-Q {U , X , α} =
  refl , ext-set (λ {a} → ext-set (λ {u} → aux {a triv}))
 where
   aux : ∀{l : ⊤ *}{u : U} → _≡_ {_} {𝕃 {_} X}
      (foldr {_} {_}
       {U → 𝕃 {_} X} {𝕃 {_} X}
       (λ f → _++_ {_} {X} (f u)) []
       (map {_} {_} {⊤}
        {U → 𝕃 {_} X} (λ x u₁ → []) l))
      []
   aux {[]} = refl
   aux {x :: l}{u} = aux {l}{u}

d-diag-R : ∀{A : Obj}
  → δ {A} ○ !ₐ (d {A}) ≡h (d {A}) ○ (((δ {A}) ⊗ₐ (δ {A})) ○ (m⊗ {(!ₒ A)}{(!ₒ A)})) 
d-diag-R {U , X , α} = refl , ext-set (λ {a} → ext-set (λ {u} → aux {a (u , u)}{u}))
 where
   aux : ∀{l : 𝕃 (Σ (U → U → 𝕃 X) (λ x → U → U → 𝕃 X))}{u : U}
     →   foldr (λ f → _++_ (f u)) [] (map θ l)
       ≡ foldr (λ f → _++_ (f u)) [] (h'₁ l u u) ++
         foldr (λ f → _++_ (f u)) [] (h'₂ l u u)
   aux {[]} = refl
   aux {(j₁ , j₂) :: js}{u}
     rewrite
       ++-assoc (j₁ u u)
                (foldr (λ f → _++_ (f u)) [] (h'₁ js u u))
                (j₂ u u ++ foldr (λ f → _++_ (f u)) [] (h'₂ js u u))
     | sym (++-assoc (foldr (λ f → _++_ (f u)) [] (h'₁ js u u))
                     (j₂ u u)
                     (foldr (λ f → _++_ (f u)) [] (h'₂ js u u)))
     | *-comm {l₁ = foldr (λ f → _++_ (f u)) [] (h'₁ js u u)}{j₂ u u}
     | ++-assoc (j₂ u u)
                (foldr (λ f → _++_ (f u)) [] (h'₁ js u u))
                (foldr (λ f → _++_ (f u)) [] (h'₂ js u u))
     | sym (++-assoc (j₁ u u)
                     (j₂ u u)
                     (foldr (λ f → _++_ (f u)) [] (h'₁ js u u) ++
                      foldr (λ f → _++_ (f u)) [] (h'₂ js u u)))
     | aux {js}{u}
    = refl

-- The following diagrams can be found on page 31 of the report.
diag-S : ∀{A B : Obj}{f : Hom (!ₒ A) (!ₒ B)}
  → ((δ {A}) ○ (!ₐ f)) ≡h (f ○ (δ {B}))
  → f ○ (e {B}) ≡h e {A}
diag-S {U , X , _}{V , Y , _}{f , F , _} (p , p') =
  refl , ext-set (λ {a} → ext-set
                           (λ {u} → sym (congf2 {b = λ _ → []}
                                                {λ _ → []}{u}{u}
                                                p' refl refl)))

diag-T : ∀{A B : Obj}{f : Hom (!ₒ A) (!ₒ B)}
  → ((δ {A}) ○ (!ₐ f)) ≡h (f ○ (δ {B}))
  → f ○ d {B} ≡h (d {A}) ○ (f ⊗ₐ f)
diag-T {U , X , _}{V , Y , _}{f , F , _} (p , p') =
  refl , ext-set (λ {a} → aux {a})
 where
   aux : {a : Σ (V → V → 𝕃 Y) (λ x → V → V → 𝕃 Y)}
     → F (θ a) ≡ θ (F⊗ {f = f}{F}{f}{F} a)
   aux {j₁ , j₂} = ext-set (λ {u} → aux' {u})
     where
       aux'' : ∀{j₁ j₂ : V → V → 𝕃 Y}
         →   (λ u₁ → j₁ u₁ u₁ ++ j₂ u₁ u₁ ++ [])
           ≡ λ u₁ → j₁ u₁ u₁ ++ j₂ u₁ u₁
       aux'' {j₁}{j₂} =
         ext-set (λ {v} → cong2 {a = j₁ v v}
                                {j₁ v v}
                                {j₂ v v ++ []}
                                {j₂ v v}
                                _++_
                                refl
                                (++[] (j₂ v v)))
       aux' : ∀{u : U}
         →   F (λ u₁ → j₁ u₁ u₁ ++ j₂ u₁ u₁) u
           ≡ F (j₁ (f u)) u ++ F (j₂ (f u)) u
       aux' {u} with
         congf2 {b = λ x → j₁ x :: j₂ x :: []}
                {λ x → j₁ x :: j₂ x :: []}
                {u}{u}
                p' refl refl
       ... | p'' rewrite
           ++[] (F (j₂ (f u)) u)
         | aux'' {j₁}{j₂} = sym p''
