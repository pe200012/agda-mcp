module STLC where

-- Simply-typed lambda calculus, intrinsically typed, de Bruijn.
-- Self-contained: no standard library.

-- Types -----------------------------------------------------------------
data Type : Set where
  o   : Type                 -- a base type
  _⇒_ : Type → Type → Type

infixr 7 _⇒_

-- Contexts --------------------------------------------------------------
data Ctx : Set where
  ∅   : Ctx
  _,_ : Ctx → Type → Ctx

infixl 5 _,_

-- de Bruijn variables ---------------------------------------------------
data _∋_ : Ctx → Type → Set where
  Z  : ∀ {Γ A}             → Γ , A ∋ A
  S_ : ∀ {Γ A B} → Γ ∋ A   → Γ , B ∋ A

infix 4 _∋_
infix 9 S_

-- Intrinsically-typed terms ---------------------------------------------
data _⊢_ : Ctx → Type → Set where
  `_  : ∀ {Γ A}   → Γ ∋ A              → Γ ⊢ A
  ƛ_  : ∀ {Γ A B} → Γ , A ⊢ B          → Γ ⊢ A ⇒ B
  _·_ : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A  → Γ ⊢ B

infix 4 _⊢_
infix 5 ƛ_
infixl 7 _·_
infix 9 `_

-- Renaming --------------------------------------------------------------
ext : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
              → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z     = Z
ext ρ (S x) = S (ρ x)

rename : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ∋ A)
                 → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
rename ρ (` x)    = ` ρ x
rename ρ (ƛ M)    = ƛ rename (ext ρ) M
rename ρ (M · M₁) = rename ρ M · rename ρ M₁

-- Substitution ----------------------------------------------------------
exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A)
               → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ A)
exts σ Z     = ` Z
exts σ (S x) = rename S_ (σ x)

subst : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A)
                → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
subst σ (` x)   = σ x
subst σ (ƛ N)   = ƛ subst (exts σ) N
subst σ (L · M) = subst σ L · subst σ M

_[_] : ∀ {Γ A B} → Γ , B ⊢ A → Γ ⊢ B → Γ ⊢ A
_[_] {Γ} {A} {B} N M = subst {Γ , B} {Γ} σ N
  where
  σ : ∀ {C} → Γ , B ∋ C → Γ ⊢ C
  σ Z     = M
  σ (S x) = ` x

-- Values ----------------------------------------------------------------
data Value : ∀ {Γ A} → Γ ⊢ A → Set where
  V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} → Value (ƛ N)

-- Small-step reduction. Its very type says reduction preserves typing:
-- _—→_ : Γ ⊢ A → Γ ⊢ A → Set, so preservation holds by construction.
infix 2 _—→_

data _—→_ : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A → Set where
  ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
       → L —→ L′
       → L · M —→ L′ · M
  ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
       → Value V → M —→ M′
       → V · M —→ V · M′
  β-ƛ  : ∀ {Γ A B} {N : Γ , A ⊢ B} {W : Γ ⊢ A}
       → Value W
       → (ƛ N) · W —→ N [ W ]

-- Progress: a closed, well-typed term is a value or it steps. ----------
data Progress {A} (M : ∅ ⊢ A) : Set where
  step : ∀ {N : ∅ ⊢ A} → M —→ N → Progress M
  done : Value M                → Progress M

progress : ∀ {A} → (M : ∅ ⊢ A) → Progress M
progress (` ())
progress (ƛ N)                  = done V-ƛ
progress (L · M) with progress L
... | step L—→L′                = step (ξ-·₁ L—→L′)
... | done V-ƛ with progress M
...   | step M—→M′              = step (ξ-·₂ V-ƛ M—→M′)
...   | done VM                 = step (β-ƛ VM)
