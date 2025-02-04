{-# OPTIONS --safe #-}

module Shallow where

{- Shallow embedding for CwF, the standard model -}
{- Copied from "Shallow embedding of type theory is morally correct" (Kaposi et al., 2019) -}

open import Agda.Primitive
import Basic as lib
 
infixl 5 _▹_
infixl 7 _[_]T
infixl 5 _▻_
infixr 6 _∘_
infixl 8 _[_]
infixl 5 _^_
infixr 6 _⇒_
infixl 7 _$_
infixl 6 _,_

-- The five sorts

Con : (i : Level) → Set (lsuc i)
Con i = Set i

Ty : ∀{i}(Γ : Con i) →
      (j : Level) → Set (i ⊔ lsuc j)
Ty Γ j = Γ → Set j

Sub : ∀{i}(Γ : Con i) 
       {j}(Δ : Con j) → 
       Set (i ⊔ j)
Sub Γ Δ = Γ → Δ

Tm : ∀{i}(Γ : Con i)
      {j}(A : Ty Γ j) → 
      Set (i ⊔ j)
Tm Γ A = (γ : Γ) → A γ

-- ✧ 
✧ : ∀{i}{Γ : Con i} → Sub Γ Γ
✧ = λ γ → γ

_∘_ : ∀{i}{Θ : Con i}{j}{Δ : Con j}(σ : Sub Θ Δ){k}{Γ : Con k}(δ : Sub Γ Θ) →
  Sub Γ Δ
σ ∘ δ = λ γ → σ (δ γ)

ass : ∀{i}{Θ : Con i}{j}{Δ : Con j}{σ : Sub Θ Δ}{k}{Ξ : Con k}{δ : Sub Ξ Θ}{l}{Γ : Con l}{ν : Sub Γ Ξ} → (σ ∘ δ) ∘ ν lib.≡ σ ∘ (δ ∘ ν)
ass = lib.refl

idl : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} → ✧ ∘ σ lib.≡ σ
idl = lib.refl

idr : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} → σ ∘ ✧ lib.≡ σ
idr = lib.refl

_[_]T : ∀{i}{Δ : Con i}{j}(A : Ty Δ j){k}{Γ : Con k}(σ : Sub Γ Δ) → Ty Γ j
A [ σ ]T = λ γ → A (σ γ)

_[_] : ∀{i}{Δ : Con i}{j}{A : Ty Δ j}(t : Tm Δ A){k}{Γ : Con k}(σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
t [ σ ] = λ γ → t (σ γ)

[id]T : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → A [ ✧ ]T lib.≡ A
[id]T = lib.refl

[∘]T : ∀{i}{Θ : Con i}{j}{Δ : Con j}{σ : Sub Θ Δ}{k}{Γ : Con k}{δ : Sub Γ Θ}
  {l}{A : Ty Δ l} → A [ σ ]T [ δ ]T lib.≡ A [ σ ∘ δ ]T
[∘]T = lib.refl

[id] : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{t : Tm Γ A} → t [ ✧ ] lib.≡ t
[id] = lib.refl

[∘] : ∀{i}{Θ : Con i}{j}{Δ : Con j}{σ : Sub Θ Δ}{k}{Γ : Con k}{δ : Sub Γ Θ}
    {l}{A : Ty Δ l}{t : Tm Δ A} → t [ σ ] [ δ ] lib.≡ t [ σ ∘ δ ]
[∘] = lib.refl

· : Con lzero
· = lib.⊤

∅ : ·
∅ = lib.tt

ε : ∀{i}{Γ : Con i} → Sub Γ ·
ε = λ γ → lib.tt

·η : ∀{i}{Γ : Con i}{σ : Sub Γ ·} → σ lib.≡ ε
·η = lib.refl

_▹_ : ∀{i}(Γ : Con i){j}(A : Ty Γ j) → Con (i ⊔ j)
Γ ▹ A = lib.Σ Γ A

_▸_ : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Γ → Tm Γ A → Γ ▹ A
γ ▸ t = γ lib., t γ

_▻_ : ∀{i}{Γ : Con i}{j}{Δ : Con j}(σ : Sub Γ Δ){k}{A : Ty Δ k}(t : Tm Γ (A [ σ ]T)) → Sub Γ (Δ ▹ A)
σ ▻ t = λ γ → (σ γ lib., t γ)

p : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Sub (Γ ▹ A) Γ
p = lib.fst

q : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Tm (Γ ▹ A) (A [ p ]T)
q = lib.snd

▹β₁ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}{k}{A : Ty Δ k}{t : Tm Γ (A [ σ ]T)} → p ∘ (_▻_ σ {A = A} t) lib.≡ σ
▹β₁ = lib.refl

▹β₂ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}{k}{A : Ty Δ k}{t : Tm Γ (A [ σ ]T)} → q [ _▻_ σ {A = A} t ] lib.≡ t
▹β₂ = lib.refl

▹η : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → (p {A = A} ▻ q {A = A}) lib.≡ ✧
▹η = lib.refl

,∘ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}{k}{A : Ty Δ k}{t : Tm Γ (A [ σ ]T)}{l}{θ : Con l}{δ : Sub θ Γ} →
  (_▻_ σ {A = A} t) ∘ δ lib.≡ (σ ∘ δ) ▻ (t [ δ ])
,∘ = lib.refl

-- abbreviations

p² :
  ∀{i}{Γ : Con i}
   {j}{A : Ty Γ j}
   {k}{B : Ty (Γ ▹ A) k} →
   Sub (Γ ▹ A ▹ B) Γ
p² = p ∘ p

p³ :
  ∀{i}{Γ : Con i}
   {j}{A : Ty Γ j}
   {k}{B : Ty (Γ ▹ A) k}
   {l}{C : Ty (Γ ▹ A ▹ B) l} →
   Sub (Γ ▹ A ▹ B ▹ C) Γ
p³ = p ∘ p ∘ p

p⁴ :
  ∀{i}{Γ : Con i}
   {j}{A : Ty Γ j}
   {k}{B : Ty (Γ ▹ A) k}
   {l}{C : Ty (Γ ▹ A ▹ B) l}
   {m}{D : Ty (Γ ▹ A ▹ B ▹ C) m} →
   Sub (Γ ▹ A ▹ B ▹ C ▹ D) Γ
p⁴ = p ∘ p ∘ p ∘ p

p⁵ :
  ∀{i}{Γ : Con i}
   {j}{A : Ty Γ j}
   {k}{B : Ty (Γ ▹ A) k}
   {l}{C : Ty (Γ ▹ A ▹ B) l}
   {m}{D : Ty (Γ ▹ A ▹ B ▹ C) m}
   {n}{E : Ty (Γ ▹ A ▹ B ▹ C ▹ D) n} →
   Sub (Γ ▹ A ▹ B ▹ C ▹ D ▹ E) Γ
p⁵ = p ∘ p ∘ p ∘ p ∘ p

𝟘 : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → Tm (Γ ▹ A) (A [ p ]T)
𝟘 = q

𝟙 :
  ∀{i}{Γ : Con i}
   {j}{A : Ty Γ j}
   {k}{B : Ty (Γ ▹ A) k} →
   Tm (Γ ▹ A ▹ B) (A [ p² ]T)
𝟙 = 𝟘 [ p ]

𝟚 :
  ∀{i}{Γ : Con i}
   {j}{A : Ty Γ j}
   {k}{B : Ty (Γ ▹ A) k}
   {l}{C : Ty (Γ ▹ A ▹ B) l} →
   Tm (Γ ▹ A ▹ B ▹ C) (A [ p³ ]T)
𝟚 = 𝟘 [ p² ]

𝟛 :
  ∀{i}{Γ : Con i}
   {j}{A : Ty Γ j}
   {k}{B : Ty (Γ ▹ A) k}
   {l}{C : Ty (Γ ▹ A ▹ B) l}
   {m}{D : Ty (Γ ▹ A ▹ B ▹ C) m} →
   Tm (Γ ▹ A ▹ B ▹ C ▹ D) (A [ p⁴ ]T)
𝟛 = 𝟘 [ p³ ]

Var : 
  ∀{i}(Γ : Con i)
   {j}(A : Ty Γ j) → 
   Set (i ⊔ j)
Var Γ A = (γ : Γ) → A γ

_^_ : ∀{i}{Γ : Con i}{j}{Δ : Con j}(σ : Sub Γ Δ){k}(A : Ty Δ k) →
  Sub (Γ ▹ A [ σ ]T) (Δ ▹ A)
_^_ {i}{Γ}{j}{Δ} σ {k} A = σ ∘ p ▻ 𝟘 {i}{Γ}{_}{A [ σ ]T}

𝕤 : 
  ∀{i}{Γ : Con i}
   {j}{A : Ty Γ j}
   {k}{B : Ty Γ k} → 
   Var Γ A → Var (Γ ▹ B) (A [ p ]T)
𝕤 x = λ γ → x (lib.fst γ)

-- Π

Π : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){k}(B : Ty (Γ ▹ A) k) → Ty Γ (j ⊔ k)
Π A B = λ γ → (α : A γ) → B (γ lib., α)

lam : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▹ A) k}(t : Tm (Γ ▹ A) B) → Tm Γ (Π A B)
lam t = λ γ α → t (γ lib., α)

app : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▹ A) k}(t : Tm Γ (Π A B)) → Tm (Γ ▹ A) B
app t = λ γ → t (lib.fst γ) (lib.snd γ)

Πβ : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▹ A) k}{t : Tm (Γ ▹ A) B} → app (lam t) lib.≡ t
Πβ = lib.refl

Πη : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▹ A) k}{t : Tm Γ (Π A B)} → lam (app t) lib.≡ t
Πη = lib.refl

Π[] : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▹ A) k}{l}{Θ : Con l}{σ : Sub Θ Γ} →
  Π A B [ σ ]T lib.≡ Π (A [ σ ]T) (B [ σ ^ A ]T)
Π[] = lib.refl

lam[] :
  ∀{i}{Γ : Con i}{l}{Δ : Con l}{σ : Sub Γ Δ}{j}{A : Ty Δ j}{k}{B : Ty (Δ ▹ A) k}{t : Tm (Δ ▹ A) B} →
  lam t [ σ ] lib.≡ lam (t [ σ ^ A ])
lam[] = lib.refl

-- abbreviations

_⇒_ : ∀{i}{Γ : Con i}{j}(A : Ty Γ j){k}(B : Ty Γ k) → Ty Γ (j ⊔ k)
A ⇒ B = Π A (B [ p ]T)

_$_ : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{B : Ty (Γ ▹ A) k}(t : Tm Γ (Π A B))(u : Tm Γ A) → Tm Γ (B [ ✧ ▻ u ]T)
t $ u = app t [ ✧ ▻ u ]

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
  fst (_,_ {A = A}{B = B} u v) lib.≡ u
Σβ₁ = lib.refl

Σβ₂ : ∀{i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▹ A) k}{u : Tm Γ A}{v : Tm Γ (B [ ✧ , u ]T)} →
  snd (_,_ {A = A}{B = B} u v) lib.≡ v
Σβ₂ = lib.refl

Ση : ∀{i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▹ A) k}{t : Tm Γ (Σ A B)} →
  fst t , snd t lib.≡ t
Ση = lib.refl

Σ[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}{k}{A : Ty Δ k}{l}{B : Ty (Δ ▹ A) l} →
  Σ A B [ σ ]T lib.≡ Σ (A [ σ ]T) (B [ σ ^ A ]T)
Σ[] = lib.refl

,[] : ∀{i j k : Level}{Γ : Con i}{A : Ty Γ j}{B : Ty (Γ ▹ A) k}{u : Tm Γ A}{v : Tm Γ (B [ _▻_ ✧ {A = A} u ]T)}{l}{Ω : Con l}{ν : Sub Ω Γ} →
  (_,_ {A = A}{B = B} u v) [ ν ] lib.≡ _,_ {A = A [ ν ]T}{B = B [ ν ^ A ]T} (u [ ν ]) (v [ ν ])
,[] = lib.refl

-- unit

⊥ : ∀{i}{Γ : Con i} → Ty Γ lzero
⊥ = λ _ → lib.⊥

⊤ : ∀{i}{Γ : Con i} → Ty Γ lzero
⊤ = λ _ → lib.⊤

tt : ∀{i}{Γ : Con i} → Tm Γ ⊤
tt = λ _ → lib.tt

⊤η : ∀{i}{Γ : Con i}{t : Tm Γ ⊤} → t lib.≡ tt
⊤η = lib.refl

⊤[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} → ⊤ [ σ ]T lib.≡ ⊤
⊤[] = lib.refl

tt[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} → tt [ σ ] lib.≡ tt
tt[] = lib.refl

-- U

U : ∀{i}{Γ : Con i} j → Ty Γ (lsuc j)
U j = λ γ → Set j

El : ∀{i}{Γ : Con i}{j}(a : Tm Γ (U j)) → Ty Γ j
El a = a

c : ∀{i}{Γ : Con i}{j}(A : Ty Γ j) → Tm Γ (U j)
c A = A

Uβ : ∀{i}{Γ : Con i}{j}{A : Ty Γ j} → El (c A) lib.≡ A
Uβ = lib.refl

Uη : ∀{i}{Γ : Con i}{j}{a : Tm Γ (U j)} → c (El a) lib.≡ a
Uη = lib.refl

U[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} {k} → U k [ σ ]T lib.≡ U k
U[] = lib.refl

El[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}{k}{a : Tm Δ (U k)}
       → El a [ σ ]T lib.≡ El (a [ σ ])
El[] = lib.refl

U0 : ∀{i}{Γ : Con i} → Ty Γ (lsuc lzero)
U0 = U lzero

-- extra equalities

Russell : ∀{i}{Γ : Con i}{j} → Tm Γ (U j) lib.≡ Ty Γ j
Russell = lib.refl

[]Tt : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{k}{Θ : Con k}{σ : Sub Θ Γ} → A [ σ ]T lib.≡ A [ σ ]
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
  → if C u v true lib.≡ u
Boolβ₁ = lib.refl

Boolβ₂ : ∀{i}{Γ : Con i}{j}{C : Ty (Γ ▹ Bool) j}
  → {u : Tm Γ (C [ (✧ , true) ]T)}
  → {v : Tm Γ (C [ (✧ , false) ]T)}
  → if C u v false lib.≡ v
Boolβ₂ = lib.refl

Bool[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} → Bool [ σ ]T lib.≡ Bool
Bool[] = lib.refl

true[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} → true [ σ ] lib.≡ true
true[] = lib.refl

false[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} → false [ σ ] lib.≡ false
false[] = lib.refl

if[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}
  → {C  : Ty (Δ ▹ Bool) j}
  → {u : Tm Δ (C [ (✧ , true) ]T)}
  → {v : Tm Δ (C [ (✧ , false) ]T)}
  → {t  : Tm Δ Bool}
  → if C u v t [ σ ] lib.≡ if (C [ σ ^ Bool ]T) (u [ σ ]) (v [ σ ]) (t [ σ ])
if[] = lib.refl

-- Identity

Id : ∀{i}{Γ : Con i}{j}(A : Ty Γ j)(u v : Tm Γ A) → Ty Γ j
Id A u v = λ γ → u γ lib.≡ v γ

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
   J C w (refl u) lib.≡ w
Idβ = lib.refl

Id[] : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{u v : Tm Γ A}{k}{Θ : Con k}{σ : Sub Θ Γ} →
  Id A u v [ σ ]T lib.≡ Id (A [ σ ]T) (u [ σ ]) (v [ σ ])
Id[] = lib.refl

refl[] : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{u : Tm Γ A}{k}{Θ : Con k}{σ : Sub Θ Γ} →
  refl u [ σ ] lib.≡ refl (u [ σ ])
refl[] = lib.refl

J[] :
  ∀{i}{Γ : Con i}{j}{A : Ty Γ j}{u : Tm Γ A}
   {k}{C : Ty (Γ ▹ A ▹ Id (A [ p ]T) (u [ p ]) 𝟘) k}
   {w : Tm Γ (C [ ✧ , u , refl u ]T)}
   {v : Tm Γ A}{t : Tm Γ (Id A u v)}{l}{Θ : Con l}{σ : Sub Θ Γ} →
   J C w t [ σ ] lib.≡ J (C [ σ ^ A ^ Id (A [ p ]T) (u [ p ]) 𝟘 ]T) (w [ σ ]) (t [ σ ])
J[] = lib.refl

module hasFunext 
  (funext  : ∀{i j}{A : Set i}{B : A → Set j}{f g : (x : A) → B x}
           → ((x : A) → f x lib.≡ g x) → f lib.≡ g)
  where

  Reflect : ∀{i}{Γ : Con i}{j}{A : Ty Γ j}(t u : Tm Γ A) → Tm Γ (Id A t u)
            → t lib.≡ u
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

K[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{k}{Θ : Con k}{σ : Sub Θ Γ} → K Δ [ σ ]T lib.≡ K Δ
K[] = lib.refl

mkK : ∀{i}{Γ : Con i}{j}{Δ : Con j}(σ : Sub Γ Δ) → Tm Γ (K Δ)
mkK σ = σ

mkK[] : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ}{k}{Θ : Con k}{ν : Sub Θ Γ} → mkK σ [ ν ] lib.≡ mkK (σ ∘ ν)
mkK[] = lib.refl

unK : ∀{i}{Γ : Con i}{j}{Δ : Con j}(t : Tm Γ (K Δ)) → Sub Γ Δ
unK t = t

unK∘ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{t : Tm Γ (K Δ)}{k}{Θ : Con k}{ν : Sub Θ Γ} → unK t ∘ ν lib.≡ unK (t [ ν ])
unK∘ = lib.refl

Kβ : ∀{i}{Γ : Con i}{j}{Δ : Con j}{σ : Sub Γ Δ} → unK (mkK σ) lib.≡ σ
Kβ = lib.refl

Kη : ∀{i}{Γ : Con i}{j}{Δ : Con j}{t : Tm Γ (K Δ)} → mkK (unK t) lib.≡ t
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
