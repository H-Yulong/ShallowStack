module Model.Shallow where

{- Shallow embedding for CwF, using inductive-recursive universe hierarchy -}

import Lib.Basic as lib
open lib using (ℕ; _≡_)

open import Agda.Primitive
open import Model.Universe 

private variable
  m n : ℕ

infixl 5 _▹_
infixl 7 _[_]T
infixl 5 _▻_
infixr 6 _∘_
infixl 8 _[_]
infixl 5 _^_
infixr 6 _⇒_
infixl 7 _$_
-- infixl 6 _,_


{- Sorts -}

Con : Set₁
Con = Set

-- Γ → Type (suc n) since Type 0 is ⊥
Ty : Con → ℕ → Set
Ty Γ n = Γ → Type (lib.suc n)

Tm : (Γ : Con) → Ty Γ n → Set
Tm Γ A = ~Π Γ A

Sub : Con → Con → Set
Sub Γ Δ = Γ → Δ


{- Substitutions -}

✧ : ∀{Γ} → Sub Γ Γ
✧ = λ γ → γ

_∘_ : ∀{Θ Δ Γ} → Sub Θ Δ → Sub Γ Θ → Sub Γ Δ
σ ∘ δ = λ γ → σ (δ γ)

asso : ∀{Θ Δ Γ Ξ}{σ : Sub Θ Δ}{δ : Sub Γ Θ}{ν : Sub Ξ Γ} → 
  (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
asso = lib.refl

idl : ∀{Γ Δ}{σ : Sub Γ Δ} → ✧ ∘ σ ≡ σ
idl = lib.refl

idr : ∀{Γ Δ}{σ : Sub Γ Δ} → σ ∘ ✧ ≡ σ
idr = lib.refl


{- Substitution action -}

_[_]T : ∀{Γ Δ} → Ty Δ n → Sub Γ Δ → Ty Γ n
A [ σ ]T = λ γ → A (σ γ)

_[_] : ∀{Γ Δ}{A : Ty Δ n} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
t [ σ ] = ~λ (λ γ → t ~$ (σ γ))

[id]T : ∀{Γ}{A : Ty Γ n} → A [ ✧ ]T ≡ A
[id]T = lib.refl

[∘]T : ∀{Γ Δ Θ}{σ : Sub Θ Δ}{δ : Sub Γ Θ}{A : Ty Δ n} → 
  A [ σ ]T [ δ ]T ≡ A [ σ ∘ δ ]T
[∘]T = lib.refl

[id] : ∀{Γ}{A : Ty Γ n}{t : Tm Γ A} → t [ ✧ ] ≡ t
[id] {t = ~λ f} = lib.refl

[∘] : ∀{Γ Δ Θ}{σ : Sub Θ Δ}{δ : Sub Γ Θ}{A : Ty Δ n}{t : Tm Δ A} → 
  t [ σ ] [ δ ] ≡ t [ σ ∘ δ ]
[∘] = lib.refl


{- Contexts -}

-- Empty context

· : Con
· = lib.⊤

∅ : ·
∅ = lib.tt

ε : ∀{Γ} → Sub Γ ·
ε = λ γ → lib.tt

·η : ∀{Γ}{σ : Sub Γ ·} → σ ≡ ε
·η = lib.refl

-- Context extension

_▹_ : (Γ : Con) → Ty Γ n → Con
Γ ▹ A = ~Σ Γ A

_▸_ : ∀{Γ}{A : Ty Γ n} → Γ → Tm Γ A → Γ ▹ A
γ ▸ t = γ ~, (t ~$ γ)

_▻_ : ∀{Γ Δ}{A : Ty Δ n} → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T) → Sub Γ (Δ ▹ A)
σ ▻ t = λ γ → (σ γ) ~, (t ~$ γ)


{- Projections -}

p : ∀{Γ}{A : Ty Γ n} → Sub (Γ ▹ A) Γ
p = ~fst

q : ∀{Γ}{A : Ty Γ n} → Tm (Γ ▹ A) (A [ p ]T)
q = ~λ ~snd

-- p ∘ (σ ▻ t) = σ
-- Supplying the implicit argument {A = A} is unavoidable
▻β₁ : ∀{Γ Δ}{σ : Sub Γ Δ}{A : Ty Δ n}{t : Tm Γ (A [ σ ]T)} → 
  p ∘ (_▻_ {A = A} σ t) ≡ σ
▻β₁ = lib.refl

-- q [ σ ▻ t ] = t
▻β₂ : ∀{Γ Δ}{σ : Sub Γ Δ}{A : Ty Δ n}{t : Tm Γ (A [ σ ]T)} → 
  q [ (_▻_ {A = A} σ t) ] ≡ t
▻β₂ {t = ~λ f} = lib.refl

-- p ▻ q = ✧
▹η : ∀{Γ}{A : Ty Γ n} → (p ▻ q {A = A}) ≡ ✧
▹η = lib.refl

--   (σ ▻ t) ∘ δ ≡ (σ ∘ δ) ▻ (t [ δ ])
,∘ : ∀{Γ Δ Θ}{σ : Sub Γ Δ}{A : Ty Δ n}{t : Tm Γ (A [ σ ]T)}{δ : Sub Θ Γ} →
  (_▻_ {A = A} σ t) ∘ δ ≡ (σ ∘ δ) ▻ (t [ δ ])
,∘ = lib.refl

-- Abbreviations

p² :
  ∀ {m n Γ}
    {A : Ty Γ n}
    {B : Ty (Γ ▹ A) m} →
   Sub (Γ ▹ A ▹ B) Γ
p² = p ∘ p

p³ :
  ∀ {l m n Γ}
    {A : Ty Γ n}
    {B : Ty (Γ ▹ A) m}
    {C : Ty (Γ ▹ A ▹ B) l} →
   Sub (Γ ▹ A ▹ B ▹ C) Γ
p³ = p ∘ p ∘ p


p⁴ :
  ∀ {k l m n Γ}
    {A : Ty Γ n}
    {B : Ty (Γ ▹ A) m}
    {C : Ty (Γ ▹ A ▹ B) l} →
    {D : Ty (Γ ▹ A ▹ B ▹ C) k} →
   Sub (Γ ▹ A ▹ B ▹ C ▹ D) Γ
p⁴ = p ∘ p ∘ p ∘ p

p⁵ :
  ∀ {j k l m n Γ}
    {A : Ty Γ n}
    {B : Ty (Γ ▹ A) m}
    {C : Ty (Γ ▹ A ▹ B) l} →
    {D : Ty (Γ ▹ A ▹ B ▹ C) k} →
    {E : Ty (Γ ▹ A ▹ B ▹ C ▹ D) j} →
   Sub (Γ ▹ A ▹ B ▹ C ▹ D ▹ E) Γ
p⁵ = p ∘ p ∘ p ∘ p ∘ p


{- Variables -}

Var : (Γ : Con) → Ty Γ n → Set
Var Γ A = ~Π Γ A

𝟘 : ∀{Γ}{A : Ty Γ n} → Tm (Γ ▹ A) (A [ p ]T)
𝟘 = q

𝕤 : ∀{Γ}{A : Ty Γ n}{B : Ty Γ m} → 
   Var Γ A → Var (Γ ▹ B) (A [ p ]T)
𝕤 x = ~λ (λ γ → x ~$ (~fst γ))

_^_ : ∀{Γ Δ} → (σ : Sub Γ Δ) → (A : Ty Δ n) → Sub (Γ ▹ A [ σ ]T) (Δ ▹ A)
σ ^ A = σ ∘ p ▻ 𝟘

-- Abbreviations

𝟙 :
  ∀ {m n Γ}
    {A : Ty Γ n}
    {B : Ty (Γ ▹ A) m} →
   Tm (Γ ▹ A ▹ B) (A [ p² ]T)
𝟙 = 𝟘 [ p ]

𝟚 :
  ∀ {l m n Γ}
    {A : Ty Γ n}
    {B : Ty (Γ ▹ A) m}
    {C : Ty (Γ ▹ A ▹ B) l} →
  Tm (Γ ▹ A ▹ B ▹ C) (A [ p³ ]T)
𝟚 = 𝟘 [ p² ]


𝟛 :
  ∀ {k l m n Γ}
    {A : Ty Γ n}
    {B : Ty (Γ ▹ A) m}
    {C : Ty (Γ ▹ A ▹ B) l} →
    {D : Ty (Γ ▹ A ▹ B ▹ C) k} →
  Tm (Γ ▹ A ▹ B ▹ C ▹ D) (A [ p⁴ ]T)
𝟛 = 𝟘 [ p³ ]

{- Π type -}

Π : ∀{Γ} → (A : Ty Γ n) → (B : Ty (Γ ▹ A) n) → Ty Γ n
Π A B = λ γ → `Π (A γ) (λ a → B (γ ~, a))

lam : ∀{Γ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}(t : Tm (Γ ▹ A) B) → Tm Γ (Π A B)
lam t = ~λ (λ γ a → t ~$ (γ ~, a))

app : ∀{Γ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}(t : Tm Γ (Π A B)) → Tm (Γ ▹ A) B
app t = ~λ (λ γ → (t ~$ (~fst γ)) (~snd γ))

Πβ : ∀{Γ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}{t : Tm (Γ ▹ A) B} → app (lam t) ≡ t
Πβ {t = ~λ f} = lib.refl

Πη : ∀{Γ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}{t : Tm Γ (Π A B)} → lam (app t) ≡ t
Πη {t = ~λ f} = lib.refl

Π[] : ∀{Γ Δ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}{σ : Sub Δ Γ} →
  Π A B [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ^ A ]T)
Π[] = lib.refl

lam[] : ∀{Γ Δ}{A : Ty Δ n}{B : Ty (Δ ▹ A) n}{t : Tm (Δ ▹ A) B}{σ : Sub Γ Δ} →
  lam t [ σ ] ≡ lam (t [ σ ^ A ])
lam[] = lib.refl

-- Abbreviations

_⇒_ : ∀{Γ} → (A : Ty Γ n) → (B : Ty Γ n) → Ty Γ n
A ⇒ B = Π A (B [ p ]T)

_$_ : ∀{Γ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}(t : Tm Γ (Π A B))(u : Tm Γ A) → 
  Tm Γ (B [ ✧ ▻ u ]T)
t $ u = app t [ ✧ ▻ u ]


{- Σ types -}



{-
-- Σ

Σ : {i j k : Level}{Γ : Con i}(A : Ty Γ j)(B : Ty (Γ ▹ A) k) → Ty Γ (j ⊔ k)
Σ A B = λ γ → lib.Σ (A γ) λ α → B (γ lib., α)

_,_ : {i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▹ A) k}(u : Tm Γ A)(v : Tm Γ (B [ ✧ ▻ u ]T)) → Tm Γ (Σ A B)
u , v = λ γ → u γ lib., v γ

fst : {i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▹ A) k} → Tm Γ (Σ A B) → Tm Γ A
fst t = λ γ → lib.fst (t γ)

snd : {i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▹ A) k}(t : Tm Γ (Σ A B)) → Tm Γ (B [ ✧ , fst t ]T)
snd t = λ γ → lib.snd (t γ)

Σβ₁ : ∀{i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▹ A) k}{u : Tm Γ A}{v : Tm Γ (B [ ✧ , u ]T)} →
  fst (_,_ {A = A}{B = B} u v) ≡ u
Σβ₁ = lib.refl

Σβ₂ : ∀{i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▹ A) k}{u : Tm Γ A}{v : Tm Γ (B [ ✧ , u ]T)} →
  snd (_,_ {A = A}{B = B} u v) ≡ v
Σβ₂ = lib.refl

Ση : ∀{i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▹ A) k}{t : Tm Γ (Σ A B)} →
  fst t , snd t ≡ t
Ση = lib.refl

Σ[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}{k}{A : Ty Δ k}{l}{B : Ty (Δ ▹ A) l} →
  Σ A B [ σ ]T ≡ Σ (A [ σ ]T) (B [ σ ^ A ]T)
Σ[] = lib.refl

,[] : ∀{i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▹ A) k}{u : Tm Γ A}{v : Tm Γ (B [ _▻_ ✧ {A = A} u ]T)}{l}{Ω : Con l}{ν : Sub Ω Γ} →
  (_,_ {A = A}{B = B} u v) [ ν ] ≡ _,_ {A = A [ ν ]T}{B = B [ ν ^ A ]T} (u [ ν ]) (v [ ν ])
,[] = lib.refl

-- unit

⊥ : ∀{i}{Γ : Con i} → Ty Γ lzero
⊥ = λ _ → lib.⊥

⊤ : ∀{i}{Γ : Con i} → Ty Γ lzero
⊤ = λ _ → lib.⊤

tt : ∀{i}{Γ : Con i} → Tm Γ ⊤
tt = λ _ → lib.tt

⊤η : ∀{i}{Γ : Con i}{t : Tm Γ ⊤} → t ≡ tt
⊤η = lib.refl

⊤[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} → ⊤ [ σ ]T ≡ ⊤
⊤[] = lib.refl

tt[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} → tt [ σ ] ≡ tt
tt[] = lib.refl

-- U

U : ∀{i}{Γ : Con i} j → Ty Γ (lsuc j)
U j = λ γ → Set j

El : ∀{i}{Γ : Con i}{j}(a : Tm Γ (U j)) → Ty Γ j
El a = a

c : ∀{i}{Γ : Con i}{j}(A : Ty Γ j) → Tm Γ (U j)
c A = A

Uβ : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → El (c A) ≡ A
Uβ = lib.refl

Uη : ∀{i}{Γ : Con i}{j}{a : Tm Γ (U j)} → c (El a) ≡ a
Uη = lib.refl

U[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} {k} → U k [ σ ]T ≡ U k
U[] = lib.refl

El[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}{k}{a : Tm Δ (U k)}
       → El a [ σ ]T ≡ El (a [ σ ])
El[] = lib.refl

U0 : ∀{i}{Γ : Con i} → Ty Γ (lsuc lzero)
U0 = U lzero

-- extra equalities

Russell : ∀{i}{Γ : Con i}{j} → Tm Γ (U j) ≡ Ty Γ j
Russell = lib.refl

[]Tt : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{Θ : Con k}{σ : Sub Θ Γ} → A [ σ ]T ≡ A [ σ ]
[]Tt = lib.refl

-- Bool

Bool    : ∀{i}{Γ : Con i} → Ty Γ lzero
Bool = λ γ → lib.Bool

true    : ∀{i}{Γ : Con i} → Tm Γ Bool
true = λ γ → lib.true

false   : ∀{i}{Γ : Con i} → Tm Γ Bool
false = λ γ → lib.false

if : ∀{i}{Γ : Con i}{j}(C : Ty (Γ ▹ Bool) j)
  → Tm Γ (C [ (✧ , true) ]T)
  → Tm Γ (C [ (✧ , false) ]T)
  → (t : Tm Γ Bool)
  → Tm Γ (C [ (✧ , t) ]T)
if C u v t = λ γ → lib.if (λ b → C (γ lib., b)) (u γ) (v γ) (t γ)

Boolβ₁ : ∀{i}{Γ : Con i}{j}{C : Ty (Γ ▹ Bool) j}
  → {u : Tm Γ (C [ (✧ , true) ]T)}
  → {v : Tm Γ (C [ (✧ , false) ]T)}
  → if C u v true ≡ u
Boolβ₁ = lib.refl

Boolβ₂ : ∀{i}{Γ : Con i}{j}{C : Ty (Γ ▹ Bool) j}
  → {u : Tm Γ (C [ (✧ , true) ]T)}
  → {v : Tm Γ (C [ (✧ , false) ]T)}
  → if C u v false ≡ v
Boolβ₂ = lib.refl

Bool[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} → Bool [ σ ]T ≡ Bool
Bool[] = lib.refl

true[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} → true [ σ ] ≡ true
true[] = lib.refl

false[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} → false [ σ ] ≡ false
false[] = lib.refl

if[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}
  → {C  : Ty (Δ ▹ Bool) j}
  → {u : Tm Δ (C [ (✧ , true) ]T)}
  → {v : Tm Δ (C [ (✧ , false) ]T)}
  → {t  : Tm Δ Bool}
  → if C u v t [ σ ] ≡ if (C [ σ ^ Bool ]T) (u [ σ ]) (v [ σ ]) (t [ σ ])
if[] = lib.refl

-- Identity

Id : ∀{i}{Γ : Con i}{j}(A : Ty Γ j)(u v : Tm Γ A) → Ty Γ j
Id A u v = λ γ → u γ ≡ v γ

refl : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}(u : Tm Γ A) → Tm Γ (Id A u u)
refl u = λ γ → lib.refl

J :
  ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{u : Tm Γ A}
   {k}(C : Ty (Γ ▹ A ▹ Id (A [ p ]T) (u [ p ]) 𝟘) k)
   (w : Tm Γ (C [ ✧ , u , refl u ]T))
   {v : Tm Γ A}(t : Tm Γ (Id A u v)) → Tm Γ (C [ ✧ , v , t ]T)
J C w t = λ γ → lib.J (λ e → C (γ lib., _ lib., e)) (w γ) (t γ)
{-
Γ , (y : A) , p : u ≡A y ⊢ C : Type
Γ ⊢ w : C [ u / y, refl u / p ]
Γ ⊢ t : u ≡A v
-----------------------
Γ ⊢ J C w t : C [ v / y, t / p ]
-}

Idβ :
  ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{u : Tm Γ A}
   {k}{C : Ty (Γ ▹ A ▹ Id (A [ p ]T) (u [ p ]) 𝟘) k}
   {w : Tm Γ (C [ ✧ , u , refl u ]T)} →
   J C w (refl u) ≡ w
Idβ = lib.refl

Id[] : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{u v : Tm Γ A}{k}{Θ : Con k}{σ : Sub Θ Γ} →
  Id A u v [ σ ]T ≡ Id (A [ σ ]T) (u [ σ ]) (v [ σ ])
Id[] = lib.refl

refl[] : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{u : Tm Γ A}{k}{Θ : Con k}{σ : Sub Θ Γ} →
  refl u [ σ ] ≡ refl (u [ σ ])
refl[] = lib.refl

J[] :
  ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{u : Tm Γ A}
   {k}{C : Ty (Γ ▹ A ▹ Id (A [ p ]T) (u [ p ]) 𝟘) k}
   {w : Tm Γ (C [ ✧ , u , refl u ]T)}
   {v : Tm Γ A}{t : Tm Γ (Id A u v)}{l}{Θ : Con l}{σ : Sub Θ Γ} →
   J C w t [ σ ] ≡ J (C [ σ ^ A ^ Id (A [ p ]T) (u [ p ]) 𝟘 ]T) (w [ σ ]) (t [ σ ])
J[] = lib.refl

module hasFunext 
  (funext  : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
           → ((x : A) → f x ≡ g x) → f ≡ g)
  where

  Reflect : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}(t u : Tm Γ A) → Tm Γ (Id A t u)
            → t ≡ u
  Reflect {i}{Γ}{j}{A} t u p = funext p

-- abbreviations

tr :
  ∀{i}{Γ : Con i}{j}{A : Ty Γ j}
   {k}(C : Ty (Γ ▹ A) k)
   {u v : Tm Γ A}(t : Tm Γ (Id A u v))
   (w : Tm Γ (C [ ✧ , u ]T)) → Tm Γ (C [ ✧ , v ]T)
tr C t w = J (C [ p ]T) w t

-- constant types

K : ∀{i}{Γ : Con i}{j} → Con j → Ty Γ j
K Δ = λ γ → Δ

K[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{Θ : Con k}{σ : Sub Θ Γ} → K Δ [ σ ]T ≡ K Δ
K[] = lib.refl

mkK : ∀{i}{Γ : Con i}{j}{Δ : Con j}(σ : Sub Γ Δ) → Tm Γ (K Δ)
mkK σ = σ

mkK[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}{k}{Θ : Con k}{ν : Sub Θ Γ} → mkK σ [ ν ] ≡ mkK (σ ∘ ν)
mkK[] = lib.refl

unK : ∀{i}{Γ : Con i}{j}{Δ : Con j}(t : Tm Γ (K Δ)) → Sub Γ Δ
unK t = t

unK∘ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{t : Tm Γ (K Δ)}{k}{Θ : Con k}{ν : Sub Θ Γ} → unK t ∘ ν ≡ unK (t [ ν ])
unK∘ = lib.refl

Kβ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} → unK (mkK σ) ≡ σ
Kβ = lib.refl

Kη : ∀{i}{Γ : Con i}{j}{Δ : Con j}{t : Tm Γ (K Δ)} → mkK (unK t) ≡ t
Kη = lib.refl

-- Natural numbers

Nat : ∀{i}{Γ : Con i} → Ty Γ lzero
Nat = λ _ → lib.ℕ

zero : ∀{i}{Γ : Con i} → Tm Γ Nat
zero = λ _ → lib.zero

suc : ∀{i}{Γ : Con i} → Tm Γ Nat → Tm Γ Nat
suc i = λ γ → lib.suc (i γ)

iter : ∀{i}{Γ : Con i}{j} → (C : Ty (Γ ▹ Nat) j) → 
       Tm Γ (C [ ✧ , zero ]T) → 
       Tm (Γ ▹ Nat ▹ C) (C [ p² , (suc 𝟙) ]T) → 
       (n : Tm Γ Nat) → 
       Tm Γ (C [ (✧ , n) ]T) 
iter {i} {Γ} C z s n = λ γ → lib.iterN (λ x → C (γ lib., x)) (z γ) (λ {x} i → s (γ lib., x lib., i)) (n γ)
-}
 