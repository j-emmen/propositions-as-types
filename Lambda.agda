

module Lambda where
  open import Agda.Builtin.Nat renaming (Nat to ℕ)

  -- Binary products and Σ-types

  infix 3 _,_ _×_ _,,_

  data _×_ (A : Set) (B : Set) : Set where
    _,_ : A → B → A × B
  prj1 : {A : Set} → {B : Set}  → A × B → A
  prj1 (a , b) = a
  prj2 : {A : Set} → {B : Set}  → A × B → B
  prj2 (a , b) = b

  data Σ (A : Set) (B : A → Set) : Set where
    _,,_ : (a : A) → B a → Σ A B
  pj1 : {A : Set} → {B : A → Set} → Σ A B → A
  pj1 (a ,, b) = a
  pj2 : {A : Set} → {B : A → Set}  → (u : Σ A B) → (B (pj1 u))
  pj2 (a ,, b) = b


  -- Initial Segment of Natural Numbers

  data Fin : ℕ → Set where
    fz : ∀ {n} → Fin (suc n)
    fs : ∀ {n} → Fin n → Fin (suc n)

  liftFin :  ∀ {n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
  liftFin f fz = fz
  liftFin f (fs i) = fs (f i)

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
  rename (lam M) f = lam (rename M (liftFin f))
  rename (app M N) f = app (rename M f) (rename N f)

  ext : ∀ {n} → Trm n → Trm (suc n)
  ext M = rename M fs

  lift : ∀ {n m} → (Fin n → Trm m) → Fin (suc n) → Trm (suc m)
  lift f fz = var fz
  lift f (fs i) = ext (f i)

  -- substitutes all variables in a term
  subst-all : ∀ {n m} → Trm n → (Fin n → Trm m) → Trm m
  subst-all (var x) f = f x
  subst-all (lam M) f =  lam (subst-all M (lift f))
  subst-all (app M N) f = app (subst-all M f) (subst-all N f)

  subst-0 : ∀ {n} → Trm (suc n) → Trm n → Trm n
  subst-0 M N = subst-all M (λ{ fz → N ; (fs x) → var x  })

  subst : ∀ {n} → Trm (suc n) → Trm n → Trm n
  subst (var x) N = N
  subst (lam M) N = lam (subst M (ext N))
  subst (app M₁ M₂) N = app (subst M₁ N) (subst M₂ N) 

  weaken : ∀ {n m} → Trm n → (Fin n → Fin m) → Trm m
  weaken M f = subst-all M (λ i → var (f i))


  -- the reduction relation
  infix 10 _⟶_ _⟶⋆_ _≡>_
  data _⟶_ {n : ℕ} : Trm n → Trm n → Set where
    β :  ∀ {M} {N} → (app (lam M) N) ⟶ (subst-0 M N)
    βlam : ∀ {M} {N} → M ⟶ N → (lam M) ⟶ (lam N)
    βappₗ : ∀ {M} {P} {N} → M ⟶ P → (app M N) ⟶ (app P N)
    βappᵣ : ∀ {M} {N} {P} → N ⟶ P → (app M N) ⟶ (app M P)

  -- its reflexive and transitive closure
  data _⟶⋆_ {n : ℕ} : Trm n → Trm n → Set where
    ⟶⋆rfl : ∀ {M} → M ⟶⋆ M
    ⟶⋆tr : ∀ {M} {N} {L} → M ⟶⋆ N → N ⟶ L → M ⟶⋆ L
  -- ⟶⋆ is transitive
  ⟶⋆-trans : {n : ℕ}{M N L : Trm n} → M ⟶⋆ N → N ⟶⋆ L → M ⟶⋆ L
  ⟶⋆-trans {n} {M} {N} {.N} red₁ ⟶⋆rfl = red₁
  ⟶⋆-trans {n} {M} {N} {L} red₁ (⟶⋆tr red₂ step) = ⟶⋆tr (⟶⋆-trans red₁ red₂) step  

  -- the auxiliary relation in between
  data _≡>_ {n : ℕ} : Trm n → Trm n → Set where
    ≡>rfl : ∀ {M} → M ≡> M
    ≡>red :  ∀ {M} {N} {M'} {N'} → M ≡> M' → N ≡> N' → (app (lam M) N) ≡> (subst-0 M' N')
    ≡>lam : ∀ {M} {M'} → M ≡> M' → (lam M) ≡> (lam M')
    ≡>app : ∀ {M} {N} {M'} {N'} → M ≡> M' → N ≡> N' → (app M N) ≡> (app M' N')

  ≡>-liftFin : {n m : ℕ}(f : Fin n → Fin m){i j : Fin (suc n)}
                  → var i ≡> var j → var (liftFin f i) ≡> var (liftFin f j)
  ≡>-liftFin f ≡>rfl = ≡>rfl

  ≡>-subst-all : {n m : ℕ}{M M' : Trm n}(f f' : Fin n → Trm m)
                    → M ≡> M' → (∀ {i j} → var i ≡> var j → f i ≡> f' j)
                      → (subst-all M f) ≡> (subst-all M' f')
  ≡>-subst-all {M = M} f f' ≡>rfl redf = {!!}
  ≡>-subst-all {M = app (lam M₁) M₂} f f' (≡>red redM₁ redM₂) redf = {!!}
  ≡>-subst-all {M = lam M} f f' (≡>lam redM) redf = {!!}
  ≡>-subst-all {M = app M₁ M₂} f f' (≡>app redM₁ redM₂) redf = {!!}

  ≡>-subst-0 : {n : ℕ}{M M' : Trm (suc n)}{N N' : Trm n}
                  → M ≡> M' → N ≡> N'
                      → subst-0 M N ≡> subst-0 M' N'
  ≡>-subst-0 {_} {M} ≡>rfl redN = {!!}
  ≡>-subst-0 {_} {app (lam M₁) M₂} (≡>red redM₁ redM₂) redN = {!!}
  ≡>-subst-0 {_} {lam M} (≡>lam redM) redN = {!!}
  ≡>-subst-0 {_} {app M₁ M₂} (≡>app redM₁ redM₂) redN = {!!}

  -- diamond property
  diamond-prop : (R : {n : ℕ} → Trm n → Trm n → Set) → Set
  diamond-prop R = ∀ {n} {M} {N} {L} → R M N → R M L → Σ (Trm n) (λ x → R N x × R L x)
  ⋄trm : {R : {n : ℕ} → Trm n → Trm n → Set}
         {n : ℕ}{M N L : Trm n}{red₁ : R M N}{red₂ : R M L}
            → Σ (Trm n) (λ x → R N x × R L x) → Trm n
  ⋄trm = pj1
  ⋄red₁ : {R : {n : ℕ} → Trm n → Trm n → Set}
          {n : ℕ}{M N L : Trm n}{red₁ : R M N}{red₂ : R M L}(diam : Σ (Trm n) (λ x → R N x × R L x))
              → R N (⋄trm {R} {_} {M} {N} {L} {red₁} {red₂} diam)
  ⋄red₁ diam = prj1 (pj2 diam)
  ⋄red₂ : {R : {n : ℕ} → Trm n → Trm n → Set}
          {n : ℕ}{M N L : Trm n}{red₁ : R M N}{red₂ : R M L}(diam : Σ (Trm n) (λ x → R N x × R L x))
              → R L (⋄trm {R} {_} {M} {N} {L} {red₁} {red₂} diam)
  ⋄red₂ diam = prj2 (pj2 diam)


  ≡>-has-diamond : diamond-prop _≡>_
  ≡>-has-diamond {n} {M} {_} {L}  ≡>rfl red = L ,, (red , ≡>rfl)
  ≡>-has-diamond {n} {app (lam M₁) M₂} {_} (≡>red red₁₁ red₁₂) ≡>rfl =
    subst-0 _ _ ,, (≡>rfl , ≡>red red₁₁ red₁₂)
  ≡>-has-diamond {n} {app (lam M₁) M₂} (≡>red red₁₁ red₁₂) (≡>red red₂₁ red₂₂) =
    subst-0 (⋄trm (≡>-has-diamond red₁₁ red₂₁)) (⋄trm (≡>-has-diamond red₁₂ red₂₂))
    ,, {!!}
  ≡>-has-diamond {n} {app (lam M₁) M₂} {_} {.(app _ _)} (≡>red red₁₁ red₁₂) (≡>app red₂ red₃) = {!!}
  ≡>-has-diamond {n} {.(lam _)} (≡>lam x) red₂ = {!!}
  ≡>-has-diamond {n} {.(app _ _)} (≡>app x x₁) red₂ = {!!}

  ≡>CR : {n : ℕ}{M N L : Trm n}(red₁ : M ≡> N)(red₂ : M ≡> L)
                        → Σ (Trm n) (λ x → N ≡> x × L ≡> x)
  ≡>CR = {!!}


  CR-aux : {n : ℕ}{M N L : Trm n} → M ⟶⋆ N → M ⟶ L
              → Σ (Trm n) (λ x → N ⟶ x × L ⟶⋆ x)
  CR-aux {n} {M} {_} {L} red step = {!!}


  -- Church-Rosser Theorem

  Church-Rosser :  {n : ℕ}{M N L : Trm n}(red₁ : M ⟶⋆ N)(red₂ : M ⟶⋆ L)
                        → Σ (Trm n) (λ x → N ⟶⋆ x × L ⟶⋆ x)
  Church-Rosser = {!!}

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
