
module Lambda where
  open import Data.Nat

  -- Initial Segment of Natural Numbers

  data Fin : ℕ → Set where
    fz : ∀ {n} → Fin (suc n)
    fs : ∀ {n} → Fin n → Fin (suc n)

-- Lambda Terms in De Bruijn notation
-- a variable var i is bound by the i-th closest abstraction if any
-- lam (app (var 0) (var 1)) : Trm 2 (var 0 is bound while var 1 is free)                                                                    or λ ¬eq → inr λ s=s → ¬eq (fs-inj s=s)

  data Trm : ℕ → Set where
    var : ∀ {n} → Fin n → Trm n
    lam : ∀ {n} → Trm (suc n) → Trm n
    app : ∀ {n} → Trm n → Trm n → Trm n

  -- context extension
  rename : ∀ {n m} → Trm n → (Fin n → Fin m) → Trm m
  rename (var x) f = var (f x)
  rename (lam M) f = lam (rename M λ{ fz → fz ; (fs i) → fs (f i) })
  rename (app M N) f = app (rename M f) (rename N f)

  ext : ∀ {n} → Trm n → Trm (suc n)
  ext M = rename M fs

  -- substitutes all variables in a term
  subst-all : ∀ {n m} → Trm n → (Fin n → Trm m) → Trm m
  subst-all (var x) f = f x
  subst-all (lam M) f =  lam (subst-all M λ{ fz → var fz ; (fs i) → ext (f i) })
  subst-all (app M N) f = app (subst-all M f) (subst-all N f)

  subst-0 : ∀ {n} → Trm (suc n) → Trm n → Trm n
  subst-0 M N = subst-all M (λ{ fz → N ; (fs x) → var x  })

  -- dafine the reduction relation
  -- data _⟶_ {n : Nat} : Trm n → Trm n → Set
  -- define its reflexive and transitive closure
  -- data _⟶⋆_ {n : Nat} : Trm n → Trm n → Set
  -- prove ⟶⋆ is reflexive and transitive
  -- prove the Church-Rosser Theorem

  -- simple types
  module STL (A : Set) where
    data Ty : Set where
      atm : A → Ty
      _⇒_ : Ty → Ty → Ty

    data Ctx : Set where
      [] : Ctx
      _∷_ : Ty → Ctx → Ctx

    len : Ctx → ℕ
    len [] = zero
    len (T ∷ Γ) = suc (len Γ)

    data _∋_∶_ : (Γ : Ctx) → Fin (len Γ) → Ty → Set where
      here  : ∀ {T Γ} → (T ∷ Γ) ∋ fz ∶ T
      there : ∀ {T S Γ i} → Γ ∋ i ∶ T → (S ∷ Γ) ∋ (fs i) ∶ T

    data _⊢_∈_ : (Γ : Ctx) → Trm (len Γ) → Ty → Set where
      t-var : ∀ {T Γ i} → Γ ∋ i ∶ T → Γ ⊢ var i ∈ T
      t-abs : ∀ {Γ T S M} → (T ∷ Γ) ⊢ M ∈ S → Γ ⊢ lam M ∈ (T ⇒ S)
      t-app : ∀ {Γ T S M N} → Γ ⊢ M ∈ (T ⇒ S) → Γ ⊢ N ∈ T → Γ ⊢ app M N ∈ S 








-- end file
