module Model.Shallow where

{- Shallow embedding for CwF, using inductive-recursive universe hierarchy -}

open import Agda.Primitive
import Lib.Basic as b
open b using (ℕ; _≡_)

open import Lib.Order
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
infixl 6 _,_

{- Sorts -}

Con : Set₁
Con = Set

-- Γ → Type (suc n) since Type 0 is ⊥
Ty : Con → ℕ → Set
Ty Γ n = Γ → Type (b.suc n)

Tm : (Γ : Con) → Ty Γ n → Set
Tm Γ A = ~Π Γ A

Sub : Con → Con → Set
Sub Γ Δ = Γ → Δ

-- Extensionality transport
Tm-subst : ∀{Γ}{A A' : Ty Γ n}(t : Tm Γ A)(eq : {γ : Γ} → A γ b.≡ A' γ) → Tm Γ A'
Tm-subst t pf = ~λ (λ γ → b.subst ⟦_⟧ pf (t ~$ γ))


{- Substitutions -}

✧ : ∀{Γ} → Sub Γ Γ
✧ = λ γ → γ

_∘_ : ∀{Θ Δ Γ} → Sub Θ Δ → Sub Γ Θ → Sub Γ Δ
σ ∘ δ = λ γ → σ (δ γ)

asso : ∀{Θ Δ Γ Ξ}{σ : Sub Θ Δ}{δ : Sub Γ Θ}{ν : Sub Ξ Γ} → 
  (σ ∘ δ) ∘ ν ≡ σ ∘ (δ ∘ ν)
asso = b.refl

idl : ∀{Γ Δ}{σ : Sub Γ Δ} → ✧ ∘ σ ≡ σ
idl = b.refl

idr : ∀{Γ Δ}{σ : Sub Γ Δ} → σ ∘ ✧ ≡ σ
idr = b.refl


{- Substitution action -}

_[_]T : ∀{Γ Δ} → Ty Δ n → Sub Γ Δ → Ty Γ n
A [ σ ]T = λ γ → A (σ γ)

_[_] : ∀{Γ Δ}{A : Ty Δ n} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]T)
t [ σ ] = ~λ (λ γ → t ~$ (σ γ))

[id]T : ∀{Γ}{A : Ty Γ n} → A [ ✧ ]T ≡ A
[id]T = b.refl

[∘]T : ∀{Γ Δ Θ}{σ : Sub Θ Δ}{δ : Sub Γ Θ}{A : Ty Δ n} → 
  A [ σ ]T [ δ ]T ≡ A [ σ ∘ δ ]T
[∘]T = b.refl

[id] : ∀{Γ}{A : Ty Γ n}{t : Tm Γ A} → t [ ✧ ] ≡ t
[id] = b.refl

[∘] : ∀{Γ Δ Θ}{σ : Sub Θ Δ}{δ : Sub Γ Θ}{A : Ty Δ n}{t : Tm Δ A} → 
  t [ σ ] [ δ ] ≡ t [ σ ∘ δ ]
[∘] = b.refl


{- Contexts -}

-- Empty context
· : Con
· = b.⊤

∅ : ·
∅ = b.tt

ε : ∀{Γ} → Sub Γ ·
ε = λ γ → b.tt

·η : ∀{Γ}{σ : Sub Γ ·} → σ ≡ ε
·η = b.refl

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
▻β₁ = b.refl

-- q [ σ ▻ t ] = t
▻β₂ : ∀{Γ Δ}{σ : Sub Γ Δ}{A : Ty Δ n}{t : Tm Γ (A [ σ ]T)} → 
  q [ (_▻_ {A = A} σ t) ] ≡ t
▻β₂ = b.refl

-- p ▻ q = ✧
▹η : ∀{Γ}{A : Ty Γ n} → (p ▻ q {A = A}) ≡ ✧
▹η = b.refl

-- (σ ▻ t) ∘ δ ≡ (σ ∘ δ) ▻ (t [ δ ])
,∘ : ∀{Γ Δ Θ}{σ : Sub Γ Δ}{A : Ty Δ n}{t : Tm Γ (A [ σ ]T)}{δ : Sub Θ Γ} →
  (_▻_ {A = A} σ t) ∘ δ ≡ (σ ∘ δ) ▻ (t [ δ ])
,∘ = b.refl

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
Πβ = b.refl

Πη : ∀{Γ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}{t : Tm Γ (Π A B)} → lam (app t) ≡ t
Πη = b.refl

Π[] : ∀{Γ Δ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}{σ : Sub Δ Γ} →
  Π A B [ σ ]T ≡ Π (A [ σ ]T) (B [ σ ^ A ]T)
Π[] = b.refl

lam[] : ∀{Γ Δ}{A : Ty Δ n}{B : Ty (Δ ▹ A) n}{t : Tm (Δ ▹ A) B}{σ : Sub Γ Δ} →
  lam t [ σ ] ≡ lam (t [ σ ^ A ])
lam[] = b.refl

-- Abbreviations
_⇒_ : ∀{Γ} → (A : Ty Γ n) → (B : Ty Γ n) → Ty Γ n
A ⇒ B = Π A (B [ p ]T)

_$_ : ∀{Γ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}(t : Tm Γ (Π A B))(u : Tm Γ A) → 
  Tm Γ (B [ ✧ ▻ u ]T)
t $ u = app t [ ✧ ▻ u ]


{- Σ types -}

Σ : ∀{Γ} → (A : Ty Γ n) → (B : Ty (Γ ▹ A) n) → Ty Γ n
Σ A B = λ γ → `Σ (A γ) (λ a → B (γ ~, a))

_,_ : ∀{Γ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → (u : Tm Γ A) → Tm Γ (B [ ✧ ▻ u ]T) → Tm Γ (Σ A B)
u , v = ~λ (λ γ → (u ~$ γ) b., (v ~$ γ))

fst : ∀{Γ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → Tm Γ (Σ A B) → Tm Γ A
fst t = ~λ (λ γ → b.fst (t ~$ γ))

snd : ∀{Γ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n} → (t : Tm Γ (Σ A B)) → Tm Γ (B [ ✧ ▻ (fst t) ]T)
snd t = ~λ (λ γ → b.snd (t ~$ γ))

Σβ₁ : ∀{Γ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}{u : Tm Γ A}{v : Tm Γ (B [ ✧ ▻ u ]T)} →
  fst {B = B} (u , v) ≡ u
Σβ₁ = b.refl

Σβ₂ : ∀{Γ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}{u : Tm Γ A}{v : Tm Γ (B [ ✧ ▻ u ]T)} →
  snd {B = B} (u , v) ≡ v
Σβ₂ = b.refl

Ση : ∀{Γ}{A : Ty Γ n}{B : Ty (Γ ▹ A) n}{t : Tm Γ (Σ A B)} →
  fst t , snd t ≡ t
Ση = b.refl

Σ[] : ∀{Γ Δ}{σ : Sub Γ Δ}{A : Ty Δ n}{B : Ty (Δ ▹ A) n} →
  Σ A B [ σ ]T ≡ Σ (A [ σ ]T) (B [ σ ^ A ]T)
Σ[] = b.refl

,[] : 
  ∀ {Γ Δ}{σ : Sub Γ Δ}{A : Ty Δ n}{B : Ty (Δ ▹ A) n}
    {u : Tm Δ A}{v : Tm Δ (B [ ✧ ▻ u ]T)} →
  (_,_ {B = B} u v) [ σ ] ≡ (u [ σ ]) , (v [ σ ])
,[] = b.refl

fst[] : 
  ∀{Γ Δ}{σ : Sub Γ Δ}{A : Ty Δ n}{B : Ty (Δ ▹ A) n}{t : Tm Δ (Σ A B)} → 
  (fst t) [ σ ] ≡ fst (t [ σ ])
fst[] = b.refl

snd[] : 
  ∀{Γ Δ}{σ : Sub Γ Δ}{A : Ty Δ n}{B : Ty (Δ ▹ A) n}{t : Tm Δ (Σ A B)} → 
  (snd t) [ σ ] ≡ snd (t [ σ ])
snd[] = b.refl


{- Empty and Unit -}

⊥ : ∀{Γ} → Ty Γ 0
⊥ = λ _ → `⊥

⊤n : ∀{Γ} → (n : ℕ) → Ty Γ n
⊤n n = λ _ → `⊤

⊤ : ∀{Γ} → Ty Γ 0
⊤ = ⊤n 0

tt : ∀{Γ} → Tm Γ ⊤
tt = ~λ (λ γ → b.tt)

ttn : ∀{Γ n} → Tm Γ (⊤n n)
ttn = ~λ (λ γ → b.tt)

⊤η : ∀{Γ}{t : Tm Γ ⊤} → t ≡ tt
⊤η = b.refl

T[] : ∀{Γ Δ}{σ : Sub Γ Δ} → ⊤ [ σ ]T ≡ ⊤ 
T[] = b.refl

tt[] : ∀{Γ Δ}{σ : Sub Γ Δ} → tt [ σ ] ≡ tt
tt[] = b.refl


{- Universe -}

U : ∀{Γ} → (n : ℕ) → Ty Γ (b.suc n)
U n = λ γ → `U

El : ∀{Γ} → Tm Γ (U n) → Ty Γ n
El (~λ f) = f

c : ∀{Γ}(A : Ty Γ n) → Tm Γ (U n)
c A = ~λ A

Uβ : ∀{Γ}{A : Ty Γ n} → El (c A) ≡ A
Uβ = b.refl

Uη : ∀{Γ}{a : Tm Γ (U n)} → c (El a) ≡ a
Uη = b.refl

U[] : ∀{n Γ Δ}{σ : Sub Γ Δ} → (U n) [ σ ]T ≡ U n
U[] = b.refl

El[] : ∀{Γ Δ}{σ : Sub Γ Δ}{a : Tm Δ (U n)}
       → El a [ σ ]T ≡ El (a [ σ ])
El[] = b.refl

U0 : ∀{Γ} → Ty Γ 1
U0 = U 0

↑T : ∀{Γ} → Ty Γ n → Ty Γ (b.suc n)
↑T A = λ γ → `↑ (A γ)

↑ : ∀{Γ}{A : Ty Γ n} → Tm Γ A → Tm Γ (↑T A)
↑ (~λ f) = ~λ f


{- Bool -}

Bool : ∀{Γ} → Ty Γ 0
Bool = λ γ → `B

true : ∀{Γ} → Tm Γ Bool
true = ~λ (λ γ → b.true)

false : ∀{Γ} → Tm Γ Bool
false = ~λ (λ γ → b.false)

if : 
  ∀   {Γ} →
    (C : Ty (Γ ▹ Bool) n) → 
    (c1 : Tm Γ (C [ (✧ ▻ true) ]T)) →
    (c2 : Tm Γ (C [ (✧ ▻ false) ]T)) → 
    (t : Tm Γ Bool) →
  -------------------------------
  Tm Γ (C [ ✧ ▻ t ]T)
if C c1 c2 t = ~λ (λ γ → b.if (λ b → ⟦ C (γ ~, b) ⟧) (c1 ~$ γ) (c2 ~$ γ) (t ~$ γ))

Boolβ₁ : 
  ∀ {Γ : Con}{C : Ty (Γ ▹ Bool) n} → 
    {c1 : Tm Γ (C [ (✧ ▻ true) ]T)}
    {c2 : Tm Γ (C [ (✧ ▻ false) ]T)} →
    if C c1 c2 true ≡ c1
Boolβ₁ = b.refl

Boolβ₂ : 
  ∀ {Γ : Con}{C : Ty (Γ ▹ Bool) n} → 
    {c1 : Tm Γ (C [ (✧ ▻ true) ]T)}
    {c2 : Tm Γ (C [ (✧ ▻ false) ]T)} →
    if C c1 c2 false ≡ c2
Boolβ₂ = b.refl

Bool[] : ∀{Γ Δ}{σ : Sub Γ Δ} → Bool [ σ ]T ≡ Bool
Bool[] = b.refl

true[] : ∀{Γ Δ}{σ : Sub Γ Δ} → true [ σ ] ≡ true
true[] = b.refl

false[] : ∀{Γ Δ}{σ : Sub Γ Δ} → false [ σ ] ≡ false
false[] = b.refl

if[] : 
  ∀   {Γ Δ}{σ : Sub Γ Δ}
    {C : Ty (Δ ▹ Bool) n} → 
    {c1 : Tm Δ (C [ (✧ ▻ true) ]T)} →
    {c2 : Tm Δ (C [ (✧ ▻ false) ]T)} → 
    {t : Tm Δ Bool} →
  -----------------------------------------
  (if C c1 c2 t) [ σ ] ≡ if (C [ σ ^ Bool ]T) (c1 [ σ ]) (c2 [ σ ]) (t [ σ ])
if[] = b.refl

bool : ∀{Γ} → b.Bool → Tm Γ Bool
bool b = ~λ (λ γ → b)


{- Identity -}

Id : ∀{Γ} → (A : Ty Γ n) → Tm Γ A → Tm Γ A → Ty Γ n
Id A x y = λ γ → `Id (A γ) (x ~$ γ) (y ~$ γ) 

refl : ∀{Γ}{A : Ty Γ n} → (t : Tm Γ A) → Tm Γ (Id A t t)
refl t = ~λ (λ γ → b.refl)

{-
  Γ , (y : A) , p : u ≡A y ⊢ C : Type
  Γ ⊢ w : C [ u / y, refl u / p ]
  Γ ⊢ t : u ≡A v
  -----------------------
  Γ ⊢ J C w t : C [ v / y, t / p ]
-}
J : 
  ∀   {Γ}{A : Ty Γ n}{u v : Tm Γ A} →
    (C : Ty (Γ ▹ A ▹ Id (A [ p ]T) (u [ p ]) 𝟘) m) → 
    (c : Tm Γ (C [ ✧ ▻ u ▻ refl u ]T)) → 
    (pf : Tm Γ (Id A u v)) →
  ------------------------------------------------------
  Tm Γ (C [ ✧ ▻ v ▻ pf ]T)
J C c pf = ~λ (λ γ → b.J ((λ p → ⟦ C (γ ~, _ ~, p) ⟧)) (c ~$ γ) (pf ~$ γ))

Idβ :
  ∀   {Γ}{A : Ty Γ n}{u : Tm Γ A}
   {C : Ty (Γ ▹ A ▹ Id (A [ p ]T) (u [ p ]) 𝟘) m}
   {c : Tm Γ (C [ ✧ ▻ u ▻ refl u ]T)} →
   J {u = u} {v = u} C c (refl u) ≡ c
Idβ = b.refl

Id[] : ∀{Γ Δ}{A : Ty Δ n}{σ : Sub Γ Δ}{u v : Tm Δ A} →
  Id A u v [ σ ]T ≡ Id (A [ σ ]T) (u [ σ ]) (v [ σ ])
Id[] = b.refl

refl[] : ∀{Γ Δ}{A : Ty Δ n}{σ : Sub Γ Δ}{u : Tm Δ A} →
  refl u [ σ ] ≡ refl (u [ σ ])
refl[] = b.refl

J[] :
  ∀ {Γ Δ}{A : Ty Δ n}{σ : Sub Γ Δ}{A : Ty Δ n}{u v : Tm Δ A}
    {C : Ty (Δ ▹ A ▹ Id (A [ p ]T) (u [ p ]) 𝟘) m}
    {c : Tm Δ (C [ ✧ ▻ u ▻ refl u ]T)}
    {t : Tm Δ (Id A u v)} →
  -----------------------------------------------------------------
    J {u = u} {v} C c t [ σ ] 
  ≡ J {u = u [ σ ]} {v = v [ σ ]} (C [ σ ^ A ^ Id (A [ p ]T) (u [ p ]) 𝟘 ]T) (c [ σ ]) (t [ σ ])
J[] = b.refl

-- transport
subst :
  ∀ {Γ}{A : Ty Γ n}{u v : Tm Γ A}
    (C : Ty (Γ ▹ A) m)
    (t : Tm Γ (Id A u v))
    (w : Tm Γ (C [ ✧ ▻ u ]T)) → Tm Γ (C [ ✧ ▻ v ]T)
subst {u = u} {v} C t w = J {u = u} {v} (C [ p ]T) w t


{- Natural numbers -}

Nat : ∀{Γ} → Ty Γ 0
Nat = λ _ → `N

zero : ∀{Γ} → Tm Γ Nat
zero = ~λ (λ _ → 0)

suc : ∀{Γ} → Tm Γ Nat → Tm Γ Nat
suc t = ~λ (λ γ → b.suc (t ~$ γ))

iter : 
  ∀ {Γ} → 
    (C : Ty (Γ ▹ Nat) n) → 
    (z : Tm Γ (C [ ✧ ▻ zero ]T)) → 
    (s : Tm (Γ ▹ Nat ▹ C) (C [ p² ▻ (suc 𝟙) ]T)) → 
    (t : Tm Γ Nat) →
  --------------------------------------------------
  Tm Γ (C [ (✧ ▻ t) ]T) 
iter C z s t = ~λ 
  (λ γ → b.iterN 
    (λ i → ⟦ C (γ ~, i) ⟧) 
    (z ~$ γ) 
    (λ {i} r → s ~$ (γ ~, i ~, r)) 
    (t ~$ γ)
  )

iter-Z : 
    ∀ {Γ} → 
    (P : Ty (Γ ▹ Nat) n) → 
    (z : Tm Γ (P [ ✧ ▻ zero ]T)) → 
    (s : Tm (Γ ▹ Nat ▹ P) (P [ p² ▻ (suc 𝟙) ]T)) → 
    (t : Tm Γ Nat) →  
  (eq : t b.≡ zero) → 
  iter P z s t b.≡ Tm-subst z (b.cong-app (b.cong (λ z → P [ ✧ ▻ z ]T) (b.sym eq))) 
iter-Z P z s t b.refl = b.refl

iter-S : 
  ∀ {Γ} → 
    (P : Ty (Γ ▹ Nat) n) → 
    (z : Tm Γ (P [ ✧ ▻ zero ]T)) → 
    (s : Tm (Γ ▹ Nat ▹ P) (P [ p² ▻ (suc 𝟙) ]T)) → 
    (t t' : Tm Γ Nat) →   
  (eq : t b.≡ suc t') → 
  iter P z s t b.≡ Tm-subst (s [ ✧ ▻ t' ▻ iter P z s t' ]) (b.cong-app (b.cong (λ z → P [ ✧ ▻ z ]T) (b.sym eq)))
iter-S P z s t t' b.refl = b.refl
 
-- Abbreviations

nat : ∀{Γ} → ℕ → Tm Γ Nat
nat n = ~λ (λ _ → n)

add : ∀{Γ} → (t t' : Tm Γ Nat) → Tm Γ Nat
add t t' = iter Nat t' (suc 𝟘) t

mult : ∀{Γ} → (t t' : Tm Γ Nat) → Tm Γ Nat
mult t t' = iter Nat zero (add (t' [ p² ]) 𝟘) t

{- Utility -}

-- Smart lifting!
↑T! : ∀{m n Γ} → ⦃ n ≤ m ⦄ → Ty Γ n → Ty Γ m
↑T! ⦃ refl≤ ⦄ A = A
↑T! ⦃ incr≤ ⦄ A = ↑T (↑T! A)

↑! : ∀{m n Γ}{A : Ty Γ n} → ⦃ pf : n ≤ m ⦄ → Tm Γ A → Tm Γ (↑T! ⦃ pf ⦄ A)
↑! ⦃ refl≤ ⦄ t  = t
↑! ⦃ incr≤ ⦄ t = ↑ (↑! t)

↓ : ∀{Γ}{A : Ty Γ n} → Tm Γ (↑T A) → Tm Γ A
↓ (~λ f) = ~λ f

↓! : ∀{m n Γ}{A : Ty Γ n} → ⦃ pf : n ≤ m ⦄ → Tm Γ (↑T! ⦃ pf ⦄ A) → Tm Γ A
↓! ⦃ pf = refl≤ ⦄ t = t
↓! ⦃ pf = incr≤ ⦄ t = ↓! (↓ t)

↑↓ : ∀{Γ}{A : Ty Γ n}{t : Tm Γ A} → ↓ (↑ t) ≡ t
↑↓ = b.refl 

{- Assorted lemmas -}

module Lemmas where

-- For the APP case in opsem
lemma-App1 : 
  ∀ {Δ : Con}{A : Ty Δ n}{δ : Sub · Δ}{a : Tm Δ A} → 
    {A' : Code (uni (Type n) ⟦_⟧)} →
  (pf : A' b.≡ A (δ b.tt)) → 
  b.subst (⟦_⟧ {n = b.suc n}) pf (b.subst (⟦_⟧ {n = b.suc n}) (b.sym pf) (a .~fun (δ b.tt))) b.≡ a .~fun (δ b.tt)
lemma-App1 {A = A} {δ} b.refl = b.refl

lemma-App2 : 
  ∀ {Δ : Con}{A : Ty Δ n}{B : Ty (Δ ▹ A) n}{δ : Sub · Δ}
    {f : Tm Δ (Π A B)}{a : Tm Δ A}
    {A' : Code (uni (Type n) ⟦_⟧)}
    {B' : ⟦ (uni (Type n) ⟦_⟧) ~~ A' ⟧ → Code (uni (Type n) ⟦_⟧)} →
    {f' : Tm · (λ _ → `Π A' B')}
    (pA : `Π A' B' b.≡ `Π (A (δ b.tt)) (λ x → B (δ b.tt ~, x))) →
    (ptf : f [ δ ] b.≡ Tm-subst f' pA) →     
    {t : Tm · (λ _ → B' (Tm-subst (a [ δ ]) (b.sym (inj₁ pA)) .~fun b.tt))} → 
    (eq : (f' $ Tm-subst (a [ δ ]) (b.sym (inj₁ pA))) b.≡ t) → 
    ((f $ a) [ δ ]) b.≡ 
      Tm-subst t 
        (b.cong-app {i = lzero} (b.ext-tt (inj₂ pA (lemma-App1 {Δ = Δ} {A} {δ} {a} (inj₁ pA)))))
lemma-App2 b.refl b.refl b.refl = b.refl

-- For the FST case in opsem
lemma-FST : 
  ∀ {Δ : Con}
    {A : Ty Δ m}
    {B : Ty (Δ ▹ A) m}
    {A+ : Code (uni (Type m) ⟦_⟧)}
    {B+ :  ⟦ (uni (Type m) ⟦_⟧) ~~ A+ ⟧ → Code (uni (Type m) ⟦_⟧)}
    (t : Tm Δ (Σ A B)) 
    (δ : Sub · Δ)
    (t' : Tm · (Σ (λ _ → A+) (λ γ → B+ (γ .~snd))))
    (pA :  `Σ A+ B+ b.≡ `Σ (A (δ b.tt)) (λ x → B (δ b.tt ~, x)))
    (ptf : t [ δ ] b.≡ Tm-subst t' pA) → 
  fst t [ δ ] b.≡ Tm-subst (fst t') (Σ-inj₁ pA)
lemma-FST t δ t' b.refl b.refl = b.refl

-- For the SND case in opsem
lemma-SND1 :   
  ∀ {Δ : Con}
    {A : Ty Δ m}
    {B : Ty (Δ ▹ A) m}
    {A+ : Code (uni (Type m) ⟦_⟧)}
    {B+ :  ⟦ (uni (Type m) ⟦_⟧) ~~ A+ ⟧ → Code (uni (Type m) ⟦_⟧)}
    (t : Tm Δ (Σ A B)) 
    (δ : Sub · Δ)
    (t' : Tm · (Σ (λ _ → A+) (λ γ → B+ (γ .~snd))))
    (pA :  `Σ A+ B+ b.≡ `Σ (A (δ b.tt)) (λ x → B (δ b.tt ~, x)))
    (ptf : t [ δ ] b.≡ Tm-subst t' pA) → 
  b.subst (⟦_~~_⟧ (uni (Type m) ⟦_⟧)) (Σ-inj₁ pA) (b.fst (t' .~fun b.tt))
  b.≡ b.fst (t .~fun (δ b.tt))
lemma-SND1 t δ t' b.refl b.refl = b.refl

lemma-SND2 : 
  ∀ {Δ : Con}
    {A : Ty Δ m}
    {B : Ty (Δ ▹ A) m}
    {A+ : Code (uni (Type m) ⟦_⟧)}
    {B+ :  ⟦ (uni (Type m) ⟦_⟧) ~~ A+ ⟧ → Code (uni (Type m) ⟦_⟧)}
    (t : Tm Δ (Σ A B)) 
    (δ : Sub · Δ)
    (t' : Tm · (Σ (λ _ → A+) (λ γ → B+ (γ .~snd))))
    (pA :  `Σ A+ B+ b.≡ `Σ (A (δ b.tt)) (λ x → B (δ b.tt ~, x)))
    (ptf : t [ δ ] b.≡ Tm-subst t' pA) → 
  snd t [ δ ] b.≡ Tm-subst (snd t') (Σ-inj₂ pA (lemma-SND1 t δ t' pA ptf))
lemma-SND2 t δ t' b.refl b.refl = b.refl
  