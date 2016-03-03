-----------------------------------------------------------------------
-- Definitions of concrete lineales.                                 --
-----------------------------------------------------------------------

module concrete-lineales where

open import prelude
open import lineale

-----------------------------------------------------------------------
-- The lineale Set                                                   --
-----------------------------------------------------------------------

isProsetSet : Proset Set
isProsetSet = (MkProset (λ A B → (A → B)) id-set (λ f g a → g (f a)))

isMonProsetSet : MonProset Set
isMonProsetSet =
  MkMonProset _×_ ⊤ isProsetSet ∧-assoc
    (sym ∧-unit) ((sym ∧-unit-r)) ∧-sym (λ x x₁ → x (fst x₁) , snd x₁)

isLinealeSet : Lineale Set
isLinealeSet =
  MkLineale isMonProsetSet (λ A B → (A → B)) (λ a b x → snd x (fst x))
    (λ x x₁ x₂ → x (x₂ , x₁))

-----------------------------------------------------------------------
-- The lineale 2                                                     --
-----------------------------------------------------------------------
Two : Set
Two = 𝔹

_≤2_ : Two → Two → Set
tt ≤2 ff = ⊥
_ ≤2 _ = ⊤

_⊗2_ : Two → Two → Two
_⊗2_ = _&&_

_→2_ : Two → Two → Two
tt →2 ff = ff
_ →2 _ = tt

isProset2 : Proset Two
isProset2 = MkProset _≤2_ aux₁ aux₂
 where
  aux₁ : {a : Two} → a ≤2 a
  aux₁ {tt} = triv
  aux₁ {ff} = triv

  aux₂ : {a b c : Two} → a ≤2 b → b ≤2 c → a ≤2 c
  aux₂ {tt} {tt} {ff} x x₁ = x₁
  aux₂ {tt} {ff} {ff} x x₁ = x
  aux₂ {tt} {tt} {tt} x x₁ = triv
  aux₂ {ff} {tt} {tt} x x₁ = triv
  aux₂ {ff} {tt} {ff} x x₁ = triv
  aux₂ {ff} {ff} {tt} x x₁ = triv
  aux₂ {ff} {ff} {ff} x x₁ = triv
  aux₂ {tt} {ff} {tt} x x₁ = triv


  aux₃ : {a b : Two} → a ≤2 b → b ≤2 a → a ≡ b
  aux₃ {tt} {tt} x x₁ = refl
  aux₃ {tt} {ff} x x₁ = ⊥-elim x
  aux₃ {ff} {tt} x x₁ = ⊥-elim x₁
  aux₃ {ff} {ff} x x₁ = refl


isMonProset2 : MonProset Two
isMonProset2 = MkMonProset _⊗2_ tt isProset2 (λ {a b c} → aux₁ {a}{b}{c}) refl aux₂ (λ {a b} → aux₃ {a}{b}) aux₄
  where
    aux₁ : {a b c : Two} → a && b && c ≡ (a && b) && c
    aux₁ {tt} {tt} {tt} = refl
    aux₁ {tt} {tt} {ff} = refl
    aux₁ {tt} {ff} {tt} = refl
    aux₁ {tt} {ff} {ff} = refl
    aux₁ {ff} {tt} {tt} = refl
    aux₁ {ff} {tt} {ff} = refl
    aux₁ {ff} {ff} {tt} = refl
    aux₁ {ff} {ff} {ff} = refl

    aux₂ : {a : Two} → a && tt ≡ a
    aux₂ {tt} = refl
    aux₂ {ff} = refl

    aux₃ : {a b : Two} → a && b ≡ b && a
    aux₃ {tt} {tt} = refl
    aux₃ {tt} {ff} = refl
    aux₃ {ff} {tt} = refl
    aux₃ {ff} {ff} = refl

    aux₄ : {a b : Two} → a ≤2 b → {c : Two} → (a && c) ≤2 (b && c)
    aux₄ {tt} {tt} x {tt} = triv
    aux₄ {tt} {tt} x {ff} = triv
    aux₄ {tt} {ff} x {tt} = x
    aux₄ {tt} {ff} x {ff} = triv
    aux₄ {ff} {tt} x {tt} = triv
    aux₄ {ff} {tt} x {ff} = triv
    aux₄ {ff} {ff} x {tt} = triv
    aux₄ {ff} {ff} x {ff} = triv


isLineale2 : Lineale Two
isLineale2 = MkLineale isMonProset2 _→2_ aux₁ aux₂
 where
   aux₁ : (a b : Two) → (a && a →2 b) ≤2 b
   aux₁ tt tt = triv
   aux₁ tt ff = triv
   aux₁ ff tt = triv
   aux₁ ff ff = triv

   aux₂ : {a b y : Two} → (a && y) ≤2 b → y ≤2 (a →2 b)
   aux₂ {tt} {tt} {tt} x = triv
   aux₂ {tt} {tt} {ff} x = triv
   aux₂ {tt} {ff} {tt} x = x
   aux₂ {tt} {ff} {ff} x = triv
   aux₂ {ff} {tt} {tt} x = triv
   aux₂ {ff} {tt} {ff} x = triv
   aux₂ {ff} {ff} {tt} x = triv
   aux₂ {ff} {ff} {ff} x = triv


-----------------------------------------------------------------------
-- The lineale 3                                                     --
-----------------------------------------------------------------------

data Three : Set where
  zero : Three
  half : Three
  one : Three

_≤3_ : Three → Three → Set
half ≤3 zero = ⊥
one ≤3 zero = ⊥
one ≤3 half = ⊥
_ ≤3 _ = ⊤


isProset3 : Proset Three
isProset3 = MkProset _≤3_ (λ {a} → aux₁ {a}) (λ{a b c} → aux₂ {a}{b}{c})
 where
   aux₁ : {a : Three} → a ≤3 a
   aux₁ {zero} = triv
   aux₁ {half} = triv
   aux₁ {one} = triv   

   aux₂ : {a b c : Three} → a ≤3 b → b ≤3 c → a ≤3 c
   aux₂ {zero} {zero} {zero} p₁ p₂ = triv
   aux₂ {zero} {zero} {half} p₁ p₂ = triv
   aux₂ {zero} {zero} {one} p₁ p₂ = triv
   aux₂ {zero} {half} {zero} p₁ p₂ = triv
   aux₂ {zero} {half} {half} p₁ p₂ = triv
   aux₂ {zero} {half} {one} p₁ p₂ = triv
   aux₂ {zero} {one} {zero} p₁ p₂ = triv
   aux₂ {zero} {one} {half} p₁ p₂ = triv
   aux₂ {zero} {one} {one} p₁ p₂ = triv
   aux₂ {half} {zero} {zero} p₁ p₂ = p₁
   aux₂ {half} {zero} {half} p₁ p₂ = triv
   aux₂ {half} {zero} {one} p₁ p₂ = triv
   aux₂ {half} {half} {zero} p₁ p₂ = p₂
   aux₂ {half} {half} {half} p₁ p₂ = triv
   aux₂ {half} {half} {one} p₁ p₂ = triv
   aux₂ {half} {one} {zero} p₁ p₂ = p₂
   aux₂ {half} {one} {half} p₁ p₂ = triv
   aux₂ {half} {one} {one} p₁ p₂ = triv
   aux₂ {one} {zero} {zero} p₁ p₂ = p₁
   aux₂ {one} {zero} {half} p₁ p₂ = p₁
   aux₂ {one} {zero} {one} p₁ p₂ = triv
   aux₂ {one} {half} {zero} p₁ p₂ = p₂
   aux₂ {one} {half} {half} p₁ p₂ = p₁
   aux₂ {one} {half} {one} p₁ p₂ = p₂
   aux₂ {one} {one} {zero} p₁ p₂ = p₂
   aux₂ {one} {one} {half} p₁ p₂ = p₂
   aux₂ {one} {one} {one} p₁ p₂ = triv


-- The following defines the non-linear intuitionistic three element
-- lineale; a Heyting algebra:
_⊗3ᵢ_ : Three → Three → Three
zero ⊗3ᵢ zero = zero
zero ⊗3ᵢ one = zero
one ⊗3ᵢ zero = zero
one ⊗3ᵢ one = one
zero ⊗3ᵢ half = zero
half ⊗3ᵢ zero = zero
half ⊗3ᵢ half = half
half ⊗3ᵢ one = half
one ⊗3ᵢ half = half

_→3ᵢ_ : Three → Three → Three
half →3ᵢ zero = zero
one →3ᵢ zero = zero
one →3ᵢ half = half
_ →3ᵢ _ = one

assoc3ᵢ : {a b c : Three} → a ⊗3ᵢ (b ⊗3ᵢ c) ≡ (a ⊗3ᵢ b) ⊗3ᵢ c
assoc3ᵢ {zero} {zero} {zero} = refl
assoc3ᵢ {zero} {zero} {half} = refl
assoc3ᵢ {zero} {zero} {one} = refl
assoc3ᵢ {zero} {half} {zero} = refl
assoc3ᵢ {zero} {half} {half} = refl
assoc3ᵢ {zero} {half} {one} = refl
assoc3ᵢ {zero} {one} {zero} = refl
assoc3ᵢ {zero} {one} {half} = refl
assoc3ᵢ {zero} {one} {one} = refl
assoc3ᵢ {half} {zero} {zero} = refl
assoc3ᵢ {half} {zero} {half} = refl
assoc3ᵢ {half} {zero} {one} = refl
assoc3ᵢ {half} {half} {zero} = refl
assoc3ᵢ {half} {half} {half} = refl
assoc3ᵢ {half} {half} {one} = refl
assoc3ᵢ {half} {one} {zero} = refl
assoc3ᵢ {half} {one} {half} = refl
assoc3ᵢ {half} {one} {one} = refl
assoc3ᵢ {one} {zero} {zero} = refl
assoc3ᵢ {one} {zero} {half} = refl
assoc3ᵢ {one} {zero} {one} = refl
assoc3ᵢ {one} {half} {zero} = refl
assoc3ᵢ {one} {half} {half} = refl
assoc3ᵢ {one} {half} {one} = refl
assoc3ᵢ {one} {one} {zero} = refl
assoc3ᵢ {one} {one} {half} = refl
assoc3ᵢ {one} {one} {one} = refl


left-ident3ᵢ : {a : Three} → one ⊗3ᵢ a ≡ a
left-ident3ᵢ {zero} = refl
left-ident3ᵢ {half} = refl
left-ident3ᵢ {one} = refl

right-ident3ᵢ : {a : Three} → a ⊗3ᵢ one ≡ a
right-ident3ᵢ {zero} = refl
right-ident3ᵢ {half} = refl
right-ident3ᵢ {one} = refl

symm3ᵢ : {a b : Three} → a ⊗3ᵢ b ≡ b ⊗3ᵢ a
symm3ᵢ {zero} {zero} = refl
symm3ᵢ {zero} {half} = refl
symm3ᵢ {zero} {one} = refl
symm3ᵢ {half} {zero} = refl
symm3ᵢ {half} {half} = refl
symm3ᵢ {half} {one} = refl
symm3ᵢ {one} {zero} = refl
symm3ᵢ {one} {half} = refl
symm3ᵢ {one} {one} = refl


comp3ᵢ : {a b : Three} → a ≤3 b → {c : Three} → (a ⊗3ᵢ c) ≤3 (b ⊗3ᵢ c)
comp3ᵢ {zero} {zero} x {zero} = triv
comp3ᵢ {zero} {zero} x {half} = triv
comp3ᵢ {zero} {zero} x {one} = triv
comp3ᵢ {zero} {half} x {zero} = triv
comp3ᵢ {zero} {half} x {half} = triv
comp3ᵢ {zero} {half} x {one} = triv
comp3ᵢ {zero} {one} x {zero} = triv
comp3ᵢ {zero} {one} x {half} = triv
comp3ᵢ {zero} {one} x {one} = triv
comp3ᵢ {half} {zero} x {zero} = triv
comp3ᵢ {half} {zero} x {half} = x
comp3ᵢ {half} {zero} x {one} = x
comp3ᵢ {half} {half} x {zero} = triv
comp3ᵢ {half} {half} x {half} = triv
comp3ᵢ {half} {half} x {one} = triv
comp3ᵢ {half} {one} x {zero} = triv
comp3ᵢ {half} {one} x {half} = triv
comp3ᵢ {half} {one} x {one} = triv
comp3ᵢ {one} {zero} x {zero} = triv
comp3ᵢ {one} {zero} x {half} = x
comp3ᵢ {one} {zero} x {one} = x
comp3ᵢ {one} {half} x {zero} = triv
comp3ᵢ {one} {half} x {half} = triv
comp3ᵢ {one} {half} x {one} = x
comp3ᵢ {one} {one} x {zero} = triv
comp3ᵢ {one} {one} x {half} = triv
comp3ᵢ {one} {one} x {one} = triv


isMonProset3ᵢ : MonProset Three
isMonProset3ᵢ = MkMonProset _⊗3ᵢ_ one isProset3 (λ{a b c} → assoc3ᵢ {a}{b}{c}) left-ident3ᵢ right-ident3ᵢ (λ{a b} → symm3ᵢ {a}{b}) (λ {a b} → comp3ᵢ {a}{b})

adj3ᵢ : {a b y : Three} → (a ⊗3ᵢ y) ≤3 b → y ≤3 (a →3ᵢ b)
adj3ᵢ {zero} {zero} {zero} p = triv
adj3ᵢ {zero} {zero} {half} p = triv
adj3ᵢ {zero} {zero} {one} p = triv
adj3ᵢ {zero} {half} {zero} p = triv
adj3ᵢ {zero} {half} {half} p = triv
adj3ᵢ {zero} {half} {one} p = triv
adj3ᵢ {zero} {one} {zero} p = triv
adj3ᵢ {zero} {one} {half} p = triv
adj3ᵢ {zero} {one} {one} p = triv
adj3ᵢ {half} {zero} {zero} p = triv
adj3ᵢ {half} {half} {zero} p = triv
adj3ᵢ {half} {half} {half} p = triv
adj3ᵢ {half} {half} {one} p = triv
adj3ᵢ {half} {one} {zero} p = triv
adj3ᵢ {half} {one} {half} p = triv
adj3ᵢ {half} {one} {one} p = triv
adj3ᵢ {one} {zero} {zero} p = triv
adj3ᵢ {one} {half} {zero} p = triv
adj3ᵢ {one} {half} {half} p = triv
adj3ᵢ {one} {one} {zero} p = triv
adj3ᵢ {one} {one} {half} p = triv
adj3ᵢ {one} {one} {one} p = triv
adj3ᵢ {half} {zero} {half} p = p
adj3ᵢ {half} {zero} {one} p = p
adj3ᵢ {one} {zero} {half} p = p
adj3ᵢ {one} {zero} {one} p = p
adj3ᵢ {one} {half} {one} p = p

rlcomp3ᵢ : (a b : Three) → (a ⊗3ᵢ (a →3ᵢ b)) ≤3 b
rlcomp3ᵢ zero zero = triv
rlcomp3ᵢ zero half = triv
rlcomp3ᵢ zero one = triv
rlcomp3ᵢ half zero = triv
rlcomp3ᵢ half half = triv
rlcomp3ᵢ half one = triv
rlcomp3ᵢ one zero = triv
rlcomp3ᵢ one half = triv
rlcomp3ᵢ one one = triv

isLineale3ᵢ : Lineale Three
isLineale3ᵢ = MkLineale isMonProset3ᵢ _→3ᵢ_ rlcomp3ᵢ (λ {a b y} → adj3ᵢ {a}{b}{y})


-- Now we define the three element proper lineale; intuitionistic and
-- linear:

_⊗3_ : Three → Three → Three
zero ⊗3 zero = zero
zero ⊗3 one = zero
one ⊗3 zero = zero
one ⊗3 one = one
zero ⊗3 half = zero
half ⊗3 zero = zero
half ⊗3 half = half
half ⊗3 one = one
one ⊗3 half = one

isMonProset3 : MonProset Three
isMonProset3 = MkMonProset _⊗3_ half isProset3 (λ {a b c} → assoc3 {a}{b}{c}) left-ident3 right-ident3 (λ {a b} → symm3 {a}{b}) (λ {a b} → comp3 {a}{b})
 where
   assoc3 : {a b c : Three} → a ⊗3 (b ⊗3 c) ≡ (a ⊗3 b) ⊗3 c
   assoc3 {zero} {zero} {zero} = refl
   assoc3 {zero} {zero} {half} = refl
   assoc3 {zero} {zero} {one} = refl
   assoc3 {zero} {half} {zero} = refl
   assoc3 {zero} {half} {half} = refl
   assoc3 {zero} {half} {one} = refl
   assoc3 {zero} {one} {zero} = refl
   assoc3 {zero} {one} {half} = refl
   assoc3 {zero} {one} {one} = refl
   assoc3 {half} {zero} {zero} = refl
   assoc3 {half} {zero} {half} = refl
   assoc3 {half} {zero} {one} = refl
   assoc3 {half} {half} {zero} = refl
   assoc3 {half} {half} {half} = refl
   assoc3 {half} {half} {one} = refl
   assoc3 {half} {one} {zero} = refl
   assoc3 {half} {one} {half} = refl
   assoc3 {half} {one} {one} = refl
   assoc3 {one} {zero} {zero} = refl
   assoc3 {one} {zero} {half} = refl
   assoc3 {one} {zero} {one} = refl
   assoc3 {one} {half} {zero} = refl
   assoc3 {one} {half} {half} = refl
   assoc3 {one} {half} {one} = refl
   assoc3 {one} {one} {zero} = refl
   assoc3 {one} {one} {half} = refl
   assoc3 {one} {one} {one} = refl

   left-ident3 : {a : Three} → half ⊗3 a ≡ a
   left-ident3 {zero} = refl
   left-ident3 {half} = refl
   left-ident3 {one} = refl

   right-ident3 : {a : Three} → a ⊗3 half ≡ a
   right-ident3 {zero} = refl
   right-ident3 {half} = refl
   right-ident3 {one} = refl

   symm3 : {a b : Three} → a ⊗3 b ≡ b ⊗3 a
   symm3 {zero} {zero} = refl
   symm3 {zero} {half} = refl
   symm3 {zero} {one} = refl
   symm3 {half} {zero} = refl
   symm3 {half} {half} = refl
   symm3 {half} {one} = refl
   symm3 {one} {zero} = refl
   symm3 {one} {half} = refl
   symm3 {one} {one} = refl

   comp3 : {a b : Three} → a ≤3 b → {c : Three} → (a ⊗3 c) ≤3 (b ⊗3 c)
   comp3 {zero} {zero} x {zero} = triv
   comp3 {zero} {zero} x {half} = triv
   comp3 {zero} {zero} x {one} = triv
   comp3 {zero} {half} x {zero} = triv
   comp3 {zero} {half} x {half} = triv
   comp3 {zero} {half} x {one} = triv
   comp3 {zero} {one} x {zero} = triv
   comp3 {zero} {one} x {half} = triv
   comp3 {zero} {one} x {one} = triv
   comp3 {half} {zero} x {zero} = triv
   comp3 {half} {zero} x {half} = x
   comp3 {half} {zero} x {one} = x
   comp3 {half} {half} x {zero} = triv
   comp3 {half} {half} x {half} = triv
   comp3 {half} {half} x {one} = triv
   comp3 {half} {one} x {zero} = triv
   comp3 {half} {one} x {half} = triv
   comp3 {half} {one} x {one} = triv
   comp3 {one} {zero} x {zero} = triv
   comp3 {one} {zero} x {half} = x
   comp3 {one} {zero} x {one} = x
   comp3 {one} {half} x {zero} = triv
   comp3 {one} {half} x {half} = x
   comp3 {one} {half} x {one} = triv
   comp3 {one} {one} x {zero} = triv
   comp3 {one} {one} x {half} = triv
   comp3 {one} {one} x {one} = triv

-- Note that these do not hold, we cannot fill in the holes.  Thus,
-- ⊗3 is a tensor product and not a cartesian product.
--
-- proj₁3 : ∀{a b} → ¡ _≤3_ (a ⊗3 b) a
-- proj₁3 {zero} {zero} = refl
-- proj₁3 {zero} {half} = refl
-- proj₁3 {zero} {one} = refl
-- proj₁3 {half} {zero} = refl
-- proj₁3 {half} {half} = refl
-- proj₁3 {half} {one} = {!!}
-- proj₁3 {one} {zero} = refl
-- proj₁3 {one} {half} = refl
-- proj₁3 {one} {one} = refl
--
-- proj₂3 : ∀{a b} → ¡ _≤3_ (a ⊗3 b) b
-- proj₂3 {zero} {zero} = refl
-- proj₂3 {zero} {half} = refl
-- proj₂3 {zero} {one} = refl
-- proj₂3 {half} {zero} = refl
-- proj₂3 {half} {half} = refl
-- proj₂3 {half} {one} = refl
-- proj₂3 {one} {zero} = refl
-- proj₂3 {one} {half} = {!!}
-- proj₂3 {one} {one} = refl


_→3_ : Three → Three → Three
half →3 zero = zero
one →3 zero = zero
one →3 half = zero
half →3 half = half
_ →3 _ = one

isLineale3 : Lineale Three
isLineale3 = MkLineale isMonProset3 _→3_ aux (λ {a b y} → aux' a b y)
 where
   aux : (a b : Three) → (a ⊗3 (a →3 b)) ≤3 b
   aux zero zero = triv
   aux zero half = triv
   aux zero one = triv
   aux half zero = triv
   aux half half = triv
   aux half one = triv
   aux one zero = triv
   aux one half = triv
   aux one one = triv

   aux' : (a b y : Three) → (a ⊗3 y) ≤3 b → y ≤3 (a →3 b)
   aux' zero zero zero x = triv
   aux' zero zero half x = triv
   aux' zero zero one x = triv
   aux' zero half zero x = triv
   aux' zero half half x = triv
   aux' zero half one x = triv
   aux' zero one zero x = triv
   aux' zero one half x = triv
   aux' zero one one x = triv
   aux' half zero zero x = triv
   aux' half zero half x = x
   aux' half zero one x = x
   aux' half half zero x = triv
   aux' half half half x = triv
   aux' half half one x = x
   aux' half one zero x = triv
   aux' half one half x = triv
   aux' half one one x = triv
   aux' one zero zero x = triv
   aux' one zero half x = x
   aux' one zero one x = x
   aux' one half zero x = triv
   aux' one half half x = x
   aux' one half one x = x
   aux' one one zero x = triv
   aux' one one half x = triv
   aux' one one one x = triv


-----------------------------------------------------------------------
-- The lineale 4                                                     --
-----------------------------------------------------------------------

data Four : Set where
  zero : Four
  quater : Four
  half : Four
  one : Four

_≤4_ : Four → Four → Set
quater ≤4 zero = ⊥
half ≤4 zero = ⊥
one ≤4 zero = ⊥
half ≤4 quater = ⊥
one ≤4 quater = ⊥
one ≤4 half = ⊥
_ ≤4 _ = ⊤


isProset4 : Proset Four
isProset4 = MkProset _≤4_ (λ {a} → refl4 {a}) (λ {a b c} → trans4 {a}{b}{c}) 
 where
  refl4 : {a : Four} → a ≤4 a
  refl4 {zero} = triv
  refl4 {quater} = triv
  refl4 {half} = triv
  refl4 {one} = triv

  trans4 : {a b c : Four} → a ≤4 b → b ≤4 c → a ≤4 c
  trans4 {zero} {zero} {zero} x x₁ = triv
  trans4 {zero} {zero} {quater} x x₁ = triv
  trans4 {zero} {zero} {half} x x₁ = triv
  trans4 {zero} {zero} {one} x x₁ = triv
  trans4 {zero} {quater} x x₁ = triv
  trans4 {zero} {half} {zero} x x₁ = triv
  trans4 {zero} {half} {quater} x x₁ = triv
  trans4 {zero} {half} {half} x x₁ = triv
  trans4 {zero} {half} {one} x x₁ = triv
  trans4 {zero} {one} {zero} x x₁ = triv
  trans4 {zero} {one} {quater} x x₁ = triv
  trans4 {zero} {one} {half} x x₁ = triv
  trans4 {zero} {one} {one} x x₁ = triv
  trans4 {quater} {zero} {zero} x x₁ = x
  trans4 {quater} {zero} {quater} x x₁ = triv
  trans4 {quater} {zero} {half} x x₁ = triv
  trans4 {quater} {zero} {one} x x₁ = triv
  trans4 {quater} {quater} {zero} x x₁ = x₁
  trans4 {quater} {quater} {quater} x x₁ = triv
  trans4 {quater} {quater} {half} x x₁ = triv
  trans4 {quater} {quater} {one} x x₁ = triv
  trans4 {quater} {half} {zero} x x₁ = x₁
  trans4 {quater} {half} {quater} x x₁ = triv
  trans4 {quater} {half} {half} x x₁ = triv
  trans4 {quater} {half} {one} x x₁ = triv
  trans4 {quater} {one} {zero} x x₁ = x₁
  trans4 {quater} {one} {quater} x x₁ = triv
  trans4 {quater} {one} {half} x x₁ = triv
  trans4 {quater} {one} {one} x x₁ = triv
  trans4 {half} {zero} {zero} x x₁ = x
  trans4 {half} {zero} {quater} x x₁ = x
  trans4 {half} {zero} {half} x x₁ = triv
  trans4 {half} {zero} {one} x x₁ = triv
  trans4 {half} {quater} {zero} x x₁ = x₁
  trans4 {half} {quater} {quater} x x₁ = x
  trans4 {half} {quater} {half} x x₁ = triv
  trans4 {half} {quater} {one} x x₁ = triv
  trans4 {half} {half} {zero} x x₁ = x₁
  trans4 {half} {half} {quater} x x₁ = x₁
  trans4 {half} {half} {half} x x₁ = triv
  trans4 {half} {half} {one} x x₁ = triv
  trans4 {half} {one} {zero} x x₁ = x₁
  trans4 {half} {one} {quater} x x₁ = x₁
  trans4 {half} {one} {half} x x₁ = triv
  trans4 {half} {one} {one} x x₁ = triv
  trans4 {one} {zero} {zero} x x₁ = x
  trans4 {one} {zero} {quater} x x₁ = x
  trans4 {one} {zero} {half} x x₁ = x
  trans4 {one} {zero} {one} x x₁ = triv
  trans4 {one} {quater} {zero} x x₁ = x
  trans4 {one} {quater} {quater} x x₁ = x
  trans4 {one} {quater} {half} x x₁ = x
  trans4 {one} {quater} {one} x x₁ = triv
  trans4 {one} {half} {zero} x x₁ = x₁
  trans4 {one} {half} {quater} x x₁ = x₁
  trans4 {one} {half} {half} x x₁ = x
  trans4 {one} {half} {one} x x₁ = triv
  trans4 {one} {one} {zero} x x₁ = x₁
  trans4 {one} {one} {quater} x x₁ = x₁
  trans4 {one} {one} {half} x x₁ = x₁
  trans4 {one} {one} {one} x x₁ = triv

-- The intuitionistic non-linear lineale 4; a four element Hayting
-- algebra:
_⊗4ᵢ_ : Four → Four → Four
zero ⊗4ᵢ zero = zero
zero ⊗4ᵢ one = zero
one ⊗4ᵢ zero = zero
one ⊗4ᵢ one = one
zero ⊗4ᵢ half = zero
half ⊗4ᵢ zero = zero
half ⊗4ᵢ half = half
half ⊗4ᵢ one = half
one ⊗4ᵢ half = half
zero ⊗4ᵢ quater = zero
quater ⊗4ᵢ zero = zero
quater ⊗4ᵢ quater = quater
quater ⊗4ᵢ half = quater
quater ⊗4ᵢ one = quater
half ⊗4ᵢ quater = quater
one ⊗4ᵢ quater = quater


isMonProset4ᵢ : MonProset Four
isMonProset4ᵢ = MkMonProset _⊗4ᵢ_ one isProset4 (λ {a b c} → assoc4ᵢ {a}{b}{c}) left-ident4ᵢ right-ident4ᵢ (λ {a b} → symm4ᵢ {a}{b}) (λ {a b} → compat4ᵢ {a}{b})
 where
  assoc4ᵢ : {a b c : Four} → a ⊗4ᵢ (b ⊗4ᵢ c) ≡ (a ⊗4ᵢ b) ⊗4ᵢ c
  assoc4ᵢ {zero} {zero} {zero} = refl
  assoc4ᵢ {zero} {zero} {quater} = refl
  assoc4ᵢ {zero} {zero} {half} = refl
  assoc4ᵢ {zero} {zero} {one} = refl
  assoc4ᵢ {zero} {quater} {zero} = refl
  assoc4ᵢ {zero} {quater} {quater} = refl
  assoc4ᵢ {zero} {quater} {half} = refl
  assoc4ᵢ {zero} {quater} {one} = refl
  assoc4ᵢ {zero} {half} {zero} = refl
  assoc4ᵢ {zero} {half} {quater} = refl
  assoc4ᵢ {zero} {half} {half} = refl
  assoc4ᵢ {zero} {half} {one} = refl
  assoc4ᵢ {zero} {one} {zero} = refl
  assoc4ᵢ {zero} {one} {quater} = refl
  assoc4ᵢ {zero} {one} {half} = refl
  assoc4ᵢ {zero} {one} {one} = refl
  assoc4ᵢ {quater} {zero} {zero} = refl
  assoc4ᵢ {quater} {zero} {quater} = refl
  assoc4ᵢ {quater} {zero} {half} = refl
  assoc4ᵢ {quater} {zero} {one} = refl
  assoc4ᵢ {quater} {quater} {zero} = refl
  assoc4ᵢ {quater} {quater} {quater} = refl
  assoc4ᵢ {quater} {quater} {half} = refl
  assoc4ᵢ {quater} {quater} {one} = refl
  assoc4ᵢ {quater} {half} {zero} = refl
  assoc4ᵢ {quater} {half} {quater} = refl
  assoc4ᵢ {quater} {half} {half} = refl
  assoc4ᵢ {quater} {half} {one} = refl
  assoc4ᵢ {quater} {one} {zero} = refl
  assoc4ᵢ {quater} {one} {quater} = refl
  assoc4ᵢ {quater} {one} {half} = refl
  assoc4ᵢ {quater} {one} {one} = refl
  assoc4ᵢ {half} {zero} {zero} = refl
  assoc4ᵢ {half} {zero} {quater} = refl
  assoc4ᵢ {half} {zero} {half} = refl
  assoc4ᵢ {half} {zero} {one} = refl
  assoc4ᵢ {half} {quater} {zero} = refl
  assoc4ᵢ {half} {quater} {quater} = refl
  assoc4ᵢ {half} {quater} {half} = refl
  assoc4ᵢ {half} {quater} {one} = refl
  assoc4ᵢ {half} {half} {zero} = refl
  assoc4ᵢ {half} {half} {quater} = refl
  assoc4ᵢ {half} {half} {half} = refl
  assoc4ᵢ {half} {half} {one} = refl
  assoc4ᵢ {half} {one} {zero} = refl
  assoc4ᵢ {half} {one} {quater} = refl
  assoc4ᵢ {half} {one} {half} = refl
  assoc4ᵢ {half} {one} {one} = refl
  assoc4ᵢ {one} {zero} {zero} = refl
  assoc4ᵢ {one} {zero} {quater} = refl
  assoc4ᵢ {one} {zero} {half} = refl
  assoc4ᵢ {one} {zero} {one} = refl
  assoc4ᵢ {one} {quater} {zero} = refl
  assoc4ᵢ {one} {quater} {quater} = refl
  assoc4ᵢ {one} {quater} {half} = refl
  assoc4ᵢ {one} {quater} {one} = refl
  assoc4ᵢ {one} {half} {zero} = refl
  assoc4ᵢ {one} {half} {quater} = refl
  assoc4ᵢ {one} {half} {half} = refl
  assoc4ᵢ {one} {half} {one} = refl
  assoc4ᵢ {one} {one} {zero} = refl
  assoc4ᵢ {one} {one} {quater} = refl
  assoc4ᵢ {one} {one} {half} = refl
  assoc4ᵢ {one} {one} {one} = refl

  left-ident4ᵢ : {a : Four} → one ⊗4ᵢ a ≡ a
  left-ident4ᵢ {zero} = refl
  left-ident4ᵢ {quater} = refl
  left-ident4ᵢ {half} = refl
  left-ident4ᵢ {one} = refl

  right-ident4ᵢ : {a : Four} → a ⊗4ᵢ one ≡ a
  right-ident4ᵢ {zero} = refl
  right-ident4ᵢ {quater} = refl
  right-ident4ᵢ {half} = refl
  right-ident4ᵢ {one} = refl

  symm4ᵢ : {a b : Four} → a ⊗4ᵢ b ≡ b ⊗4ᵢ a
  symm4ᵢ {zero} {zero} = refl
  symm4ᵢ {zero} {quater} = refl
  symm4ᵢ {zero} {half} = refl
  symm4ᵢ {zero} {one} = refl
  symm4ᵢ {quater} {zero} = refl
  symm4ᵢ {quater} {quater} = refl
  symm4ᵢ {quater} {half} = refl
  symm4ᵢ {quater} {one} = refl
  symm4ᵢ {half} {zero} = refl
  symm4ᵢ {half} {quater} = refl
  symm4ᵢ {half} {half} = refl
  symm4ᵢ {half} {one} = refl
  symm4ᵢ {one} {zero} = refl
  symm4ᵢ {one} {quater} = refl
  symm4ᵢ {one} {half} = refl
  symm4ᵢ {one} {one} = refl

  compat4ᵢ : {a b : Four} → a ≤4 b → {c : Four} → (a ⊗4ᵢ c) ≤4 (b ⊗4ᵢ c)
  compat4ᵢ {zero} {zero} x {zero} = triv
  compat4ᵢ {zero} {zero} x {quater} = triv
  compat4ᵢ {zero} {zero} x {half} = triv
  compat4ᵢ {zero} {zero} x {one} = triv
  compat4ᵢ {zero} {quater} x {zero} = triv
  compat4ᵢ {zero} {quater} x {quater} = triv
  compat4ᵢ {zero} {quater} x {half} = triv
  compat4ᵢ {zero} {quater} x {one} = triv
  compat4ᵢ {zero} {half} x {zero} = triv
  compat4ᵢ {zero} {half} x {quater} = triv
  compat4ᵢ {zero} {half} x {half} = triv
  compat4ᵢ {zero} {half} x {one} = triv
  compat4ᵢ {zero} {one} x {zero} = triv
  compat4ᵢ {zero} {one} x {quater} = triv
  compat4ᵢ {zero} {one} x {half} = triv
  compat4ᵢ {zero} {one} x {one} = triv
  compat4ᵢ {quater} {zero} x {zero} = triv
  compat4ᵢ {quater} {zero} x {quater} = x
  compat4ᵢ {quater} {zero} x {half} = x
  compat4ᵢ {quater} {zero} x {one} = x
  compat4ᵢ {quater} {quater} x {zero} = triv
  compat4ᵢ {quater} {quater} x {quater} = triv
  compat4ᵢ {quater} {quater} x {half} = triv
  compat4ᵢ {quater} {quater} x {one} = triv
  compat4ᵢ {quater} {half} x {zero} = triv
  compat4ᵢ {quater} {half} x {quater} = triv
  compat4ᵢ {quater} {half} x {half} = triv
  compat4ᵢ {quater} {half} x {one} = triv
  compat4ᵢ {quater} {one} x {zero} = triv
  compat4ᵢ {quater} {one} x {quater} = triv
  compat4ᵢ {quater} {one} x {half} = triv
  compat4ᵢ {quater} {one} x {one} = triv
  compat4ᵢ {half} {zero} x {zero} = triv
  compat4ᵢ {half} {zero} x {quater} = x
  compat4ᵢ {half} {zero} x {half} = x 
  compat4ᵢ {half} {zero} x {one} = x
  compat4ᵢ {half} {quater} x {zero} = triv
  compat4ᵢ {half} {quater} x {quater} = triv
  compat4ᵢ {half} {quater} x {half} = x
  compat4ᵢ {half} {quater} x {one} = x
  compat4ᵢ {half} {half} x {zero} = triv
  compat4ᵢ {half} {half} x {quater} = triv
  compat4ᵢ {half} {half} x {half} = triv
  compat4ᵢ {half} {half} x {one} = triv
  compat4ᵢ {half} {one} x {zero} = triv
  compat4ᵢ {half} {one} x {quater} = triv
  compat4ᵢ {half} {one} x {half} = triv
  compat4ᵢ {half} {one} x {one} = triv
  compat4ᵢ {one} {zero} x {zero} = triv
  compat4ᵢ {one} {zero} x {quater} = x
  compat4ᵢ {one} {zero} x {half} = x
  compat4ᵢ {one} {zero} x {one} = x
  compat4ᵢ {one} {quater} x {zero} = triv
  compat4ᵢ {one} {quater} x {quater} = triv
  compat4ᵢ {one} {quater} x {half} = x
  compat4ᵢ {one} {quater} x {one} = x
  compat4ᵢ {one} {half} x {zero} = triv
  compat4ᵢ {one} {half} x {quater} = triv
  compat4ᵢ {one} {half} x {half} = triv
  compat4ᵢ {one} {half} x {one} = x
  compat4ᵢ {one} {one} x {zero} = triv
  compat4ᵢ {one} {one} x {quater} = triv
  compat4ᵢ {one} {one} x {half} = triv
  compat4ᵢ {one} {one} x {one} = triv

_→4ᵢ_ : Four → Four → Four
one →4ᵢ zero = zero
half →4ᵢ zero = zero
one →4ᵢ half = half
quater →4ᵢ zero = zero
half →4ᵢ quater = quater
one →4ᵢ quater = quater
_ →4ᵢ _ = one

isLineale4ᵢ : Lineale Four
isLineale4ᵢ = MkLineale isMonProset4ᵢ _→4ᵢ_ rlcomp4ᵢ (λ {a b y} → adj4ᵢ {a}{b}{y})
 where
  rlcomp4ᵢ : (a b : Four) → (a ⊗4ᵢ (a →4ᵢ b)) ≤4 b
  rlcomp4ᵢ zero zero = triv
  rlcomp4ᵢ zero quater = triv
  rlcomp4ᵢ zero half = triv
  rlcomp4ᵢ zero one = triv
  rlcomp4ᵢ quater zero = triv
  rlcomp4ᵢ quater quater = triv
  rlcomp4ᵢ quater half = triv
  rlcomp4ᵢ quater one = triv
  rlcomp4ᵢ half zero = triv
  rlcomp4ᵢ half quater = triv
  rlcomp4ᵢ half half = triv
  rlcomp4ᵢ half one = triv
  rlcomp4ᵢ one zero = triv
  rlcomp4ᵢ one quater = triv
  rlcomp4ᵢ one half = triv
  rlcomp4ᵢ one one = triv

  adj4ᵢ : {a b y : Four} → (a ⊗4ᵢ y) ≤4 b → y ≤4 (a →4ᵢ b)
  adj4ᵢ {zero} {zero} {zero} x = triv
  adj4ᵢ {zero} {zero} {quater} x = triv
  adj4ᵢ {zero} {zero} {half} x = triv
  adj4ᵢ {zero} {zero} {one} x = triv
  adj4ᵢ {zero} {quater} {zero} x = triv
  adj4ᵢ {zero} {quater} {quater} x = triv
  adj4ᵢ {zero} {quater} {half} x = triv
  adj4ᵢ {zero} {quater} {one} x = triv
  adj4ᵢ {zero} {half} {zero} x = triv
  adj4ᵢ {zero} {half} {quater} x = triv
  adj4ᵢ {zero} {half} {half} x = triv
  adj4ᵢ {zero} {half} {one} x = triv
  adj4ᵢ {zero} {one} {zero} x = triv
  adj4ᵢ {zero} {one} {quater} x = triv
  adj4ᵢ {zero} {one} {half} x = triv
  adj4ᵢ {zero} {one} {one} x = triv
  adj4ᵢ {quater} {zero} {zero} x = triv
  adj4ᵢ {quater} {zero} {quater} x = x
  adj4ᵢ {quater} {zero} {half} x = x
  adj4ᵢ {quater} {zero} {one} x = x
  adj4ᵢ {quater} {quater} {zero} x = triv
  adj4ᵢ {quater} {quater} {quater} x = triv
  adj4ᵢ {quater} {quater} {half} x = triv
  adj4ᵢ {quater} {quater} {one} x = triv
  adj4ᵢ {quater} {half} {zero} x = triv
  adj4ᵢ {quater} {half} {quater} x = triv
  adj4ᵢ {quater} {half} {half} x = triv
  adj4ᵢ {quater} {half} {one} x = triv
  adj4ᵢ {quater} {one} {zero} x = triv
  adj4ᵢ {quater} {one} {quater} x = triv
  adj4ᵢ {quater} {one} {half} x = triv
  adj4ᵢ {quater} {one} {one} x = triv
  adj4ᵢ {half} {zero} {zero} x = triv
  adj4ᵢ {half} {zero} {quater} x = x
  adj4ᵢ {half} {zero} {half} x = x
  adj4ᵢ {half} {zero} {one} x = x
  adj4ᵢ {half} {quater} {zero} x = triv
  adj4ᵢ {half} {quater} {quater} x = triv
  adj4ᵢ {half} {quater} {half} x = x
  adj4ᵢ {half} {quater} {one} x = x
  adj4ᵢ {half} {half} {zero} x = triv
  adj4ᵢ {half} {half} {quater} x = triv
  adj4ᵢ {half} {half} {half} x = triv
  adj4ᵢ {half} {half} {one} x = triv
  adj4ᵢ {half} {one} {zero} x = triv
  adj4ᵢ {half} {one} {quater} x = triv
  adj4ᵢ {half} {one} {half} x = triv
  adj4ᵢ {half} {one} {one} x = triv
  adj4ᵢ {one} {zero} {zero} x = triv
  adj4ᵢ {one} {zero} {quater} x = x
  adj4ᵢ {one} {zero} {half} x = x
  adj4ᵢ {one} {zero} {one} x = x
  adj4ᵢ {one} {quater} {zero} x = triv
  adj4ᵢ {one} {quater} {quater} x = triv
  adj4ᵢ {one} {quater} {half} x = x
  adj4ᵢ {one} {quater} {one} x = x
  adj4ᵢ {one} {half} {zero} x = triv
  adj4ᵢ {one} {half} {quater} x = triv
  adj4ᵢ {one} {half} {half} x = triv
  adj4ᵢ {one} {half} {one} x = x
  adj4ᵢ {one} {one} {zero} x = triv
  adj4ᵢ {one} {one} {quater} x = triv
  adj4ᵢ {one} {one} {half} x = triv
  adj4ᵢ {one} {one} {one} x = triv


proj₁4ᵢ : ∀{a b} → (a ⊗4ᵢ b) ≤4 a
proj₁4ᵢ {zero} {zero} = triv
proj₁4ᵢ {zero} {quater} = triv
proj₁4ᵢ {zero} {half} = triv
proj₁4ᵢ {zero} {one} = triv
proj₁4ᵢ {quater} {zero} = triv
proj₁4ᵢ {quater} {quater} = triv
proj₁4ᵢ {quater} {half} = triv
proj₁4ᵢ {quater} {one} = triv
proj₁4ᵢ {half} {zero} = triv
proj₁4ᵢ {half} {quater} = triv
proj₁4ᵢ {half} {half} = triv
proj₁4ᵢ {half} {one} = triv
proj₁4ᵢ {one} {zero} = triv
proj₁4ᵢ {one} {quater} = triv
proj₁4ᵢ {one} {half} = triv
proj₁4ᵢ {one} {one} = triv

proj₂4ᵢ : ∀{a b} → (a ⊗4ᵢ b) ≤4 b
proj₂4ᵢ {zero} {zero} = triv
proj₂4ᵢ {zero} {quater} = triv
proj₂4ᵢ {zero} {half} = triv
proj₂4ᵢ {zero} {one} = triv
proj₂4ᵢ {quater} {zero} = triv
proj₂4ᵢ {quater} {quater} = triv
proj₂4ᵢ {quater} {half} = triv
proj₂4ᵢ {quater} {one} = triv
proj₂4ᵢ {half} {zero} = triv
proj₂4ᵢ {half} {quater} = triv
proj₂4ᵢ {half} {half} = triv
proj₂4ᵢ {half} {one} = triv
proj₂4ᵢ {one} {zero} = triv
proj₂4ᵢ {one} {quater} = triv
proj₂4ᵢ {one} {half} = triv
proj₂4ᵢ {one} {one} = triv

ctr4ᵢ : ∀{c a b} → c ≤4 a → c ≤4 b → c ≤4 (a ⊗4ᵢ b)
ctr4ᵢ {zero} {zero} {zero} x x₁ = triv
ctr4ᵢ {zero} {zero} {quater} x x₁ = triv
ctr4ᵢ {zero} {zero} {half} x x₁ = triv
ctr4ᵢ {zero} {zero} {one} x x₁ = triv
ctr4ᵢ {zero} {quater} {zero} x x₁ = triv
ctr4ᵢ {zero} {quater} {quater} x x₁ = triv
ctr4ᵢ {zero} {quater} {half} x x₁ = triv
ctr4ᵢ {zero} {quater} {one} x x₁ = triv
ctr4ᵢ {zero} {half} {zero} x x₁ = triv
ctr4ᵢ {zero} {half} {quater} x x₁ = triv
ctr4ᵢ {zero} {half} {half} x x₁ = triv
ctr4ᵢ {zero} {half} {one} x x₁ = triv
ctr4ᵢ {zero} {one} {zero} x x₁ = triv
ctr4ᵢ {zero} {one} {quater} x x₁ = triv
ctr4ᵢ {zero} {one} {half} x x₁ = triv
ctr4ᵢ {zero} {one} {one} x x₁ = triv
ctr4ᵢ {quater} {zero} {zero} x x₁ = x
ctr4ᵢ {quater} {zero} {quater} x x₁ = x
ctr4ᵢ {quater} {zero} {half} x x₁ = x
ctr4ᵢ {quater} {zero} {one} x x₁ = x
ctr4ᵢ {quater} {quater} {zero} x x₁ = x₁
ctr4ᵢ {quater} {quater} {quater} x x₁ = triv
ctr4ᵢ {quater} {quater} {half} x x₁ = triv
ctr4ᵢ {quater} {quater} {one} x x₁ = triv
ctr4ᵢ {quater} {half} {zero} x x₁ = x₁
ctr4ᵢ {quater} {half} {quater} x x₁ = triv
ctr4ᵢ {quater} {half} {half} x x₁ = triv
ctr4ᵢ {quater} {half} {one} x x₁ = triv
ctr4ᵢ {quater} {one} {zero} x x₁ = x₁
ctr4ᵢ {quater} {one} {quater} x x₁ = triv
ctr4ᵢ {quater} {one} {half} x x₁ = triv
ctr4ᵢ {quater} {one} {one} x x₁ = triv
ctr4ᵢ {half} {zero} {zero} x x₁ = x
ctr4ᵢ {half} {zero} {quater} x x₁ = x
ctr4ᵢ {half} {zero} {half} x x₁ = x
ctr4ᵢ {half} {zero} {one} x x₁ = x
ctr4ᵢ {half} {quater} {zero} x x₁ = x
ctr4ᵢ {half} {quater} {quater} x x₁ = x
ctr4ᵢ {half} {quater} {half} x x₁ = x
ctr4ᵢ {half} {quater} {one} x x₁ = x
ctr4ᵢ {half} {half} {zero} x x₁ = x₁
ctr4ᵢ {half} {half} {quater} x x₁ = x₁
ctr4ᵢ {half} {half} {half} x x₁ = triv
ctr4ᵢ {half} {half} {one} x x₁ = triv
ctr4ᵢ {half} {one} {zero} x x₁ = x₁
ctr4ᵢ {half} {one} {quater} x x₁ = x₁
ctr4ᵢ {half} {one} {half} x x₁ = triv
ctr4ᵢ {half} {one} {one} x x₁ = triv
ctr4ᵢ {one} {zero} {zero} x x₁ = x
ctr4ᵢ {one} {zero} {quater} x x₁ = x
ctr4ᵢ {one} {zero} {half} x x₁ = x
ctr4ᵢ {one} {zero} {one} x x₁ = x
ctr4ᵢ {one} {quater} {zero} x x₁ = x
ctr4ᵢ {one} {quater} {quater} x x₁ = x
ctr4ᵢ {one} {quater} {half} x x₁ = x
ctr4ᵢ {one} {quater} {one} x x₁ = x
ctr4ᵢ {one} {half} {zero} x x₁ = x
ctr4ᵢ {one} {half} {quater} x x₁ = x
ctr4ᵢ {one} {half} {half} x x₁ = x
ctr4ᵢ {one} {half} {one} x x₁ = x
ctr4ᵢ {one} {one} {zero} x x₁ = x₁
ctr4ᵢ {one} {one} {quater} x x₁ = x₁
ctr4ᵢ {one} {one} {half} x x₁ = x₁
ctr4ᵢ {one} {one} {one} x x₁ = triv

