
module simpleTT (A : Set) where
  open import Basic-Inductives
  open import Lambda-Calculus public

  ----------------
  -- Simple Types
  ----------------

  infixr 30 _⇒_
  data Ty : Set where
    atm : A → Ty
    _⇒_ : Ty → Ty → Ty

  Ctx : Set
  Ctx = List Ty

  -- Γ ∋ i ∶ T inhabited if T occurs in Γ in the i-th position
  infix 10 _∋_∶_
  data _∋_∶_ : (Γ : Ctx) → Fin (len Γ) → Ty → Set where
    here  : ∀ {T Γ} → T ∣ Γ ∋ fz ∶ T
    there : ∀ {T S Γ i} → Γ ∋ i ∶ T → S ∣ Γ ∋ fs i ∶ T

  -- typing judgements
  infix 10 _⊢_∶_
  data _⊢_∶_ : (Γ : Ctx) → Trm (len Γ) → Ty → Set where
    ⊢-var : ∀ {T Γ i} → Γ ∋ i ∶ T → Γ ⊢ var i ∶ T
    ⊢-abs : ∀ {Γ T S M} → T ∣ Γ ⊢ M ∶ S → Γ ⊢ lam M ∶ T ⇒ S
    ⊢-app : ∀ {Γ T S M N} → Γ ⊢ M ∶ T ⇒ S → Γ ⊢ N ∶ T → Γ ⊢ app M N ∶ S




-- end file
