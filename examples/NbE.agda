module NbE where

-- Normalization by Evaluation for STLC, reusing the intrinsic syntax of STLC.
-- Delivers, with no reduction relation and no substitution lemmas:
--   * nf       : every well-typed term has a β-normal form   (normalization)
--   * sound    : ∅ ⊢ A → A holds in every Kripke world        (Curry-Howard)
--   * complete : A holds in every Kripke world → ∅ ⊢ A         (completeness)

open import STLC using (Type; o; _⇒_; Ctx; ∅; _,_; _∋_; Z; S_; _⊢_; `_; ƛ_; _·_)

-- Order-preserving embeddings (thinnings) Γ ↦ Δ -------------------------
data Ren : Ctx → Ctx → Set where
  ε    : Ren ∅ ∅
  keep : ∀ {Γ Δ A} → Ren Γ Δ → Ren (Γ , A) (Δ , A)
  skip : ∀ {Γ Δ A} → Ren Γ Δ → Ren Γ (Δ , A)

idRen : ∀ {Γ} → Ren Γ Γ
idRen {∅}     = ε
idRen {Γ , A} = keep idRen

-- composition: (Ren Δ Θ) after (Ren Γ Δ) gives Ren Γ Θ
_∘_ : ∀ {Γ Δ Θ} → Ren Δ Θ → Ren Γ Δ → Ren Γ Θ
skip ρ ∘ σ      = skip (ρ ∘ σ)
keep ρ ∘ keep σ = keep (ρ ∘ σ)
keep ρ ∘ skip σ = skip (ρ ∘ σ)
ε      ∘ ε      = ε

renVar : ∀ {Γ Δ A} → Ren Γ Δ → Γ ∋ A → Δ ∋ A
renVar (keep ρ) Z     = Z
renVar (keep ρ) (S x) = S (renVar ρ x)
renVar (skip ρ) x     = S (renVar ρ x)

-- Normal and neutral forms --------------------------------------------
data Nf : Ctx → Type → Set
data Ne : Ctx → Type → Set

data Ne where
  var : ∀ {Γ A}   → Γ ∋ A → Ne Γ A
  app : ∀ {Γ A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

data Nf where
  lam : ∀ {Γ A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)
  neu : ∀ {Γ}     → Ne Γ o → Nf Γ o

renNe : ∀ {Γ Δ A} → Ren Γ Δ → Ne Γ A → Ne Δ A
renNf : ∀ {Γ Δ A} → Ren Γ Δ → Nf Γ A → Nf Δ A
renNe ρ (var x)   = var (renVar ρ x)
renNe ρ (app n m) = app (renNe ρ n) (renNf ρ m)
renNf ρ (lam n)   = lam (renNf (keep ρ) n)
renNf ρ (neu n)   = neu (renNe ρ n)

-- Embed normal/neutral forms back into terms --------------------------
⌜_⌝ne : ∀ {Γ A} → Ne Γ A → Γ ⊢ A
⌜_⌝nf : ∀ {Γ A} → Nf Γ A → Γ ⊢ A
⌜ var x   ⌝ne = ` x
⌜ app n m ⌝ne = ⌜ n ⌝ne · ⌜ m ⌝nf
⌜ lam n   ⌝nf = ƛ ⌜ n ⌝nf
⌜ neu n   ⌝nf = ⌜ n ⌝ne

-- The Kripke model: types as monotone predicates over contexts --------
⟦_⟧ : Type → Ctx → Set
⟦ o ⟧     Γ = Nf Γ o
⟦ A ⇒ B ⟧ Γ = ∀ {Δ} → Ren Γ Δ → ⟦ A ⟧ Δ → ⟦ B ⟧ Δ

mon : ∀ {A Γ Δ} → Ren Γ Δ → ⟦ A ⟧ Γ → ⟦ A ⟧ Δ
mon {o}     ρ v = renNf ρ v
mon {A ⇒ B} ρ f = λ ρ′ a → f (ρ′ ∘ ρ) a

-- reflect/reify between neutral terms, the model, and normal forms ----
reflect : ∀ {A Γ} → Ne Γ A → ⟦ A ⟧ Γ
reify   : ∀ {A Γ} → ⟦ A ⟧ Γ → Nf Γ A
reflect {o}     n = neu n
reflect {A ⇒ B} n = λ ρ a → reflect (app (renNe ρ n) (reify a))
reify {o}     v = v
reify {A ⇒ B} f = lam (reify (f (skip idRen) (reflect (var Z))))

-- Environments and evaluation -----------------------------------------
Env : Ctx → Ctx → Set
Env Γ Δ = ∀ {A} → Γ ∋ A → ⟦ A ⟧ Δ

extEnv : ∀ {Γ Δ A} → Env Γ Δ → ⟦ A ⟧ Δ → Env (Γ , A) Δ
extEnv η v Z     = v
extEnv η v (S x) = η x

monEnv : ∀ {Γ Δ Θ} → Ren Δ Θ → Env Γ Δ → Env Γ Θ
monEnv ρ η = λ x → mon ρ (η x)

eval : ∀ {Γ Δ A} → Γ ⊢ A → Env Γ Δ → ⟦ A ⟧ Δ
eval (` x)   η = η x
eval (ƛ N)   η = λ ρ a → eval N (extEnv (monEnv ρ η) a)
eval (L · M) η = eval L η idRen (eval M η)

idEnv : ∀ {Γ} → Env Γ Γ
idEnv x = reflect (var x)

-- Normalization: every well-typed term has a normal form -------------
nf : ∀ {Γ A} → Γ ⊢ A → Nf Γ A
nf t = reify (eval t idEnv)

normalize : ∀ {Γ A} → Γ ⊢ A → Γ ⊢ A
normalize t = ⌜ nf t ⌝nf

-- Curry-Howard: STLC types as intuitionistic implicational formulas.
-- "Valid" = forced in every Kripke world (the model at every context).
Valid : Type → Set
Valid A = ∀ {Γ} → ⟦ A ⟧ Γ

soundness : ∀ {A} → ∅ ⊢ A → Valid A
soundness t = eval t (λ ())          -- a closed term needs no environment

completeness : ∀ {A} → Valid A → ∅ ⊢ A
completeness v = ⌜ reify (v {∅}) ⌝nf
