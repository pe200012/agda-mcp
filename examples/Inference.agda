module Inference where

-- STLC type checking is decidable: a sound and complete bidirectional checker.
-- `yes` carries a typing derivation (soundness); `no` carries a refutation that
-- no derivation exists (completeness). Both hold by construction.

-- Self-contained prelude (the installed agda-stdlib 2.0 is incompatible with
-- this Agda 2.8: Data.Fin.Properties uses an option Agda 2.8 rejects).
data ⊥ : Set where

¬_ : Set → Set
¬ P = P → ⊥
infix 3 ¬_

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
infix 4 _≡_

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data Fin : ℕ → Set where
  zero : ∀ {n} → Fin (suc n)
  suc  : ∀ {n} → Fin n → Fin (suc n)

data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : ∀ {n} → A → Vec A n → Vec A (suc n)
infixr 6 _∷_

lookup : ∀ {A : Set} {n} → Vec A n → Fin n → A
lookup (x ∷ _)  zero    = x
lookup (_ ∷ xs) (suc i) = lookup xs i

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

∃-syntax : ∀ {A : Set} (B : A → Set) → Set
∃-syntax = Σ _
syntax ∃-syntax (λ x → B) = ∃[ x ] B

-- Types ----------------------------------------------------------------
data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty

infixr 7 _⇒_

-- Decidable equality on types.
_≟Ty_ : (A B : Ty) → Dec (A ≡ B)
ι       ≟Ty ι       = yes refl
ι       ≟Ty (_ ⇒ _) = no λ ()
(_ ⇒ _) ≟Ty ι       = no λ ()
(A ⇒ B) ≟Ty (C ⇒ D) with A ≟Ty C | B ≟Ty D
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no λ { refl → ¬p refl }
... | _        | no ¬q    = no λ { refl → ¬q refl }

Ctx : ℕ → Set
Ctx n = Vec Ty n

-- Bidirectional raw terms (well-scoped via Fin) -----------------------
data Syn (n : ℕ) : Set
data Chk (n : ℕ) : Set

data Syn n where
  `_  : Fin n → Syn n            -- variable      (synthesizes)
  _·_ : Syn n → Chk n → Syn n    -- application   (synthesizes)
  _⦂_ : Chk n → Ty → Syn n       -- annotation    (synthesizes)

data Chk n where
  ƛ_  : Chk (suc n) → Chk n      -- lambda        (checks)
  ⇑_  : Syn n → Chk n            -- mode switch   (checks)

infix 9 `_
infixl 7 _·_
infix 5 ƛ_

-- Bidirectional typing -------------------------------------------------
data _⊢_⇒_ {n} (Γ : Ctx n) : Syn n → Ty → Set
data _⊢_⇐_ {n} (Γ : Ctx n) : Chk n → Ty → Set

data _⊢_⇒_ {n} Γ where
  ⊢` : ∀ {x}            → Γ ⊢ ` x ⇒ lookup Γ x
  ⊢· : ∀ {L M A B}      → Γ ⊢ L ⇒ (A ⇒ B) → Γ ⊢ M ⇐ A → Γ ⊢ L · M ⇒ B
  ⊢⦂ : ∀ {M A}          → Γ ⊢ M ⇐ A → Γ ⊢ (M ⦂ A) ⇒ A

data _⊢_⇐_ {n} Γ where
  ⊢ƛ : ∀ {N A B}        → (A ∷ Γ) ⊢ N ⇐ B → Γ ⊢ ƛ N ⇐ (A ⇒ B)
  ⊢⇑ : ∀ {M A B}        → Γ ⊢ M ⇒ A → A ≡ B → Γ ⊢ ⇑ M ⇐ B

-- Synthesis yields a unique type (needed for the checker's refutations).
uniq⇒ : ∀ {n} {Γ : Ctx n} {M A B} → Γ ⊢ M ⇒ A → Γ ⊢ M ⇒ B → A ≡ B
uniq⇒ ⊢`         ⊢`         = refl
uniq⇒ (⊢· L _)   (⊢· L′ _)  with uniq⇒ L L′
... | refl = refl
uniq⇒ (⊢⦂ _)     (⊢⦂ _)     = refl

ι≢⇒ : ∀ {A B} → ι ≡ A ⇒ B → ⊥
ι≢⇒ ()

-- A synthesizing term whose head doesn't synthesize can't be applied.
¬arg : ∀ {n} {Γ : Ctx n} {L M}
     → ¬ (∃[ A ] (Γ ⊢ L ⇒ A)) → ¬ (∃[ C ] (Γ ⊢ L · M ⇒ C))
¬arg ¬L (_ , ⊢· L _) = ¬L (_ , L)

-- The checker -----------------------------------------------------------
synth : ∀ {n} (Γ : Ctx n) (M : Syn n) → Dec (∃[ A ] (Γ ⊢ M ⇒ A))
check : ∀ {n} (Γ : Ctx n) (M : Chk n) (A : Ty) → Dec (Γ ⊢ M ⇐ A)

synth Γ (` x) = yes (lookup Γ x , ⊢`)
synth Γ (L · M) with synth Γ L
... | no ¬L = no (¬arg ¬L)
... | yes (ι , ⊢L) = no helper
  where
  helper : ¬ (∃[ C ] (Γ ⊢ L · M ⇒ C))
  helper (_ , ⊢· ⊢L′ _) = ι≢⇒ (uniq⇒ ⊢L ⊢L′)
... | yes ((A ⇒ B) , ⊢L) with check Γ M A
...   | yes ⊢M = yes (B , ⊢· ⊢L ⊢M)
...   | no ¬M  = no helper
  where
  helper : ¬ (∃[ C ] (Γ ⊢ L · M ⇒ C))
  helper (_ , ⊢· ⊢L′ ⊢M′) with uniq⇒ ⊢L ⊢L′
  ... | refl = ¬M ⊢M′
synth Γ (M ⦂ A) with check Γ M A
... | yes ⊢M = yes (A , ⊢⦂ ⊢M)
... | no ¬M  = no λ { (_ , ⊢⦂ ⊢M) → ¬M ⊢M }

check Γ (ƛ N) ι       = no λ ()
check Γ (ƛ N) (A ⇒ B) with check (A ∷ Γ) N B
... | yes ⊢N = yes (⊢ƛ ⊢N)
... | no ¬N  = no λ { (⊢ƛ ⊢N) → ¬N ⊢N }
check Γ (⇑ M) B with synth Γ M
... | no ¬M = no λ { (⊢⇑ ⊢M _) → ¬M (_ , ⊢M) }
... | yes (A , ⊢M) with A ≟Ty B
...   | yes A≡B = yes (⊢⇑ ⊢M A≡B)
...   | no ¬eq  = no λ { (⊢⇑ ⊢M′ A′≡B) → ¬eq (trans (uniq⇒ ⊢M ⊢M′) A′≡B) }
