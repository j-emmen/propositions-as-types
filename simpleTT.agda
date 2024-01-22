{-# OPTIONS --without-K #-}

module simpleTT (A : Set) where
  open import Nat-and-Fin public
  open import Lambda-Calculus public

  ----------------
  -- Simple Types
  ----------------

  infixr 30 _⇒_
  data Ty : Set where
    atm : A → Ty
    _⇒_ : Ty → Ty → Ty

  -- contexts are (finite) lists of types
  Ctx : Set
  Ctx = List Ty
  len : Ctx → Nat
  len = lenList {A = Ty}
  pr : (Γ : Ctx) → Fin (len Γ) → Ty
  pr = prList {A = Ty}
  
  fnc2Ctx : ∀ {n} → (Fin n → Ty) → Σ[ Ctx ] (λ x → n == len x)
  fnc2Ctx = fnct-to-List {A = Ty}
  

  -- Γ ∋ i ∶ T inhabited if T occurs in Γ in the i-th position
  infix 10 _∋_∶_
  data _∋_∶_ : (Γ : Ctx) → Fin (len Γ) → Ty → Set where
    here  : ∀ {T Γ} → T ∣ Γ ∋ fz ∶ T
    there : ∀ {T S Γ i} → Γ ∋ i ∶ T → S ∣ Γ ∋ fs i ∶ T

  varty : ∀ Γ i → Γ ∋ i ∶ pr Γ i
  varty (R ∣ Γ) fz = here
  varty (R ∣ Γ) (fs i) = there (varty Γ i)
  vartypr : ∀ {Γ i T} → Γ ∋ i ∶ T → pr Γ i == T
  vartypr here = =rf
  vartypr (there inc) = vartypr inc

  -- typing judgements
  infix 10 _⊢_∶_
  data _⊢_∶_ : (Γ : Ctx) → Trm (len Γ) → Ty → Set where
    ⊢-var : ∀ {T Γ i} → Γ ∋ i ∶ T → Γ ⊢ var i ∶ T
    ⊢-abs : ∀ {Γ T S M} → T ∣ Γ ⊢ M ∶ S → Γ ⊢ lam M ∶ T ⇒ S
    ⊢-app : ∀ {Γ T S M N} → Γ ⊢ M ∶ T ⇒ S → Γ ⊢ N ∶ T → Γ ⊢ app M N ∶ S

  ⊢-var-prem : ∀ {T Γ i} → Γ ⊢ var i ∶ T → Γ ∋ i ∶ T
  ⊢-var-prem (⊢-var inc) = inc
  ⊢-abs-prem : ∀ {Γ T S M} → Γ ⊢ lam M ∶ T ⇒ S → T ∣ Γ ⊢ M ∶ S
  ⊢-abs-prem (⊢-abs der) = der
  -- this one gives back the two premises at once
  ⊢-app-prem : ∀ {Γ S M N} → Γ ⊢ app M N ∶ S → Σ[ Ty ] (λ x → Γ ⊢ M ∶ x ⇒ S × Γ ⊢ N ∶ x)
  ⊢-app-prem (⊢-app {T = T} der₁ der₂) = T ,, (der₁ , der₂)
  ⊢-app-premₜ : ∀ {Γ S M N} → Γ ⊢ app M N ∶ S → Ty
  ⊢-app-premₜ der = pj1 (⊢-app-prem der)
  ⊢-app-premₗ : ∀ {Γ S M N} → (der : Γ ⊢ app M N ∶ S) → Γ ⊢ M ∶ (⊢-app-premₜ der) ⇒ S
  ⊢-app-premₗ der = prj1 (pj2 (⊢-app-prem der))
  ⊢-app-premᵣ : ∀ {Γ S M N} → (der : Γ ⊢ app M N ∶ S) → Γ ⊢ N ∶ (⊢-app-premₜ der)
  ⊢-app-premᵣ der = prj2 (pj2 (⊢-app-prem der))

  -- some useful properties of derivations
  ⊢∶-= : ∀ {Γ T M M'} → M == M' → Γ ⊢ M ∶ T → Γ ⊢ M' ∶ T
  ⊢∶-= {Γ} {T} = =transp (λ x → Γ ⊢ x ∶ T)
  ⊢v∶-∋∶ : ∀ {Γ T i} → Γ ⊢ var i ∶ T → Γ ∋ i ∶ T
  ⊢v∶-∋∶ (⊢-var inc) = inc
  ⊢∶-∋∶ : ∀ {Γ T M} → Γ ⊢ M ∶ T → ∀ {i} → M == var i → Γ ∋ i ∶ T
  ⊢∶-∋∶ der eq = ⊢v∶-∋∶ (⊢∶-= eq der)

  -- the only values of function types are lambdas
  ⊢-val-is-lam : ∀ {Γ T S M} → Γ ⊢ M ∶ T ⇒ S → is-value M
                   → Σ[ Trm (suc (len Γ)) ] (λ x → lam x == M)
  ⊢-val-is-lam der (val-lam {M'} nrm') = M' ,, =rf

  -- context morphisms
  isCtxMor : ∀ Γ Γ' → (f : Fin (len Γ) → Fin (len Γ')) → Set
  isCtxMor Γ Γ' f = ∀ {T i} → Γ ∋ i ∶ T → Γ' ∋ (f i) ∶ T

  CtxMor-ext : ∀ {Γ Δ p q} → (∀ i → p i == q i) → isCtxMor Γ Δ p → isCtxMor Γ Δ q
  CtxMor-ext {Γ} {Δ} eq cm {T} {i} inc = ((λ x → Δ ∋ x ∶ T) ● eq i) (cm inc)
  id-CtxMor : ∀ {Γ} → isCtxMor Γ Γ id
  id-CtxMor {Γ} {_} {_} = id
  =id-CtxMor : ∀ Γ {p} → (∀ i → p i == i) → isCtxMor Γ Γ p
  =id-CtxMor Γ isid = CtxMor-ext (λ i → isid i ⁻¹) id-CtxMor
  ∅-CtxMor : ∀ {p} → isCtxMor [] [] p
  ∅-CtxMor {p} {_} {i} _ = N₀rec i
  !-CtxMor : ∀ Γ p → isCtxMor [] Γ p
  !-CtxMor Γ p {_} {i} _ = N₀rec i
  CtxMor-cmp-rf : ∀ {Γ Δ Θ p q} → isCtxMor Γ Δ p → isCtxMor Δ Θ q → isCtxMor Γ Θ (q ∘ p)
  CtxMor-cmp-rf pcm qcm {T} {i} = qcm ∘ pcm
  CtxMor-cmp : ∀ {Γ Δ Θ p q r} → (∀ i → r i == q (p i))
                 → isCtxMor Γ Δ p → isCtxMor Δ Θ q → isCtxMor Γ Θ r
  CtxMor-cmp tr pcm qcm {T} {i} = CtxMor-ext (λ i → tr i ⁻¹) (qcm ∘ pcm)
  fs-cm :  ∀ {Γ R} → isCtxMor Γ (R ∣ Γ) fs
  fs-cm {Γ} {R} = there
  liftFinCtxMor : ∀ {Γ Δ} R {f} → isCtxMor Γ Δ f → isCtxMor (R ∣ Γ) (R ∣ Δ) (liftFin f)
  liftFinCtxMor R cm {R} {fz} here = here
  liftFinCtxMor R cm {T} {fs i} (there inc) = there (cm inc)
  swapFinCtxMor : ∀ {Γ' Γ p } R S → isCtxMor (R ∣ S ∣ Γ') Γ p → isCtxMor (S ∣ R ∣ Γ') Γ (p ∘ swapFin id)
  swapFinCtxMor R S cm {S} here = cm (there here)
  swapFinCtxMor R S cm {R} (there here) = cm here
  swapFinCtxMor R S cm {T} (there (there inc)) = cm (there (there inc))
    
  
  -- the context projections are those context morphisms whose function is injective 
  infix 10 _◂_∶_
  _◂_∶_ :  (Γ' Γ : Ctx) → (Fin (len Γ') → Fin (len Γ)) → Set
  Γ' ◂ Γ ∶ p = is-injective p × isCtxMor Γ' Γ p
  ◂∶ij : ∀ {Γ' Γ p} → Γ' ◂ Γ ∶ p → is-injective p
  ◂∶ij = prj1
  ◂∶cm : ∀ {Γ' Γ p} → Γ' ◂ Γ ∶ p → isCtxMor Γ' Γ p
  ◂∶cm = prj2

  π-id : ∀ {Γ p} → (∀ i → p i == i) → Γ ◂ Γ ∶ p
  π-id isid = isid-is-injective isid
              , =id-CtxMor _ isid
  π-∅ : ∀ {p} → [] ◂ [] ∶ p
  π-∅ {p} = π-id N₀ind
  π-! : ∀ {Γ} p → [] ◂ Γ ∶ p
  π-! p = (λ {i} {j} _ → N₀ind {i ==_} j)
          , !-CtxMor _ p
  π-dsp : ∀ {Γ} R → Γ ◂ R ∣ Γ ∶ fs
  π-dsp R = fs-inj , there
  π-cmp-rf : ∀ {Γ Δ Θ p q} → Γ ◂ Δ ∶ p → Δ ◂ Θ ∶ q → Γ ◂ Θ ∶ (q ∘ p)
  π-cmp-rf πp πq = injective-cmp (◂∶ij πp) (◂∶ij πq)
                   , CtxMor-cmp-rf (◂∶cm πp) (◂∶cm πq)
  π-ext : ∀ {Γ' Γ p p'} → (∀ i → p i == p' i) → Γ' ◂ Γ ∶ p → Γ' ◂ Γ ∶ p'
  π-ext eq πp = injective-ext eq (◂∶ij πp)
                , CtxMor-ext eq (◂∶cm πp)
  π-frg-rf : ∀ {Γ' Γ p} R → R ∣ Γ' ◂ Γ ∶ p → Γ' ◂ Γ ∶ (p ∘ fs)
  π-frg-rf R πp = (fs-inj ∘ prj1 πp)
                  , CtxMor-cmp-rf fs-cm (◂∶cm πp)
  π-cnc-rf : ∀ {Γ' Γ p } R → Γ' ◂ Γ ∶ p → (R ∣ Γ') ◂ (R ∣ Γ) ∶ (liftFin p)
  π-cnc-rf R πp = liftFin-inj (prj1 πp)
               , liftFinCtxMor R (◂∶cm πp)
  π-swp-rf : ∀ {Γ' Γ p } R S → R ∣ S ∣ Γ' ◂ Γ ∶ p → S ∣ R ∣ Γ' ◂ Γ ∶ (p ∘ swapFin id)
  π-swp-rf R S πp = (λ e → swapFin-inj id (prj1 πp e))
                    , swapFinCtxMor R S (◂∶cm πp)
  π-cmp : ∀ {Γ Δ Θ p q r} → (∀ i → q (p i) == r i)
             → Γ ◂ Δ ∶ p → Δ ◂ Θ ∶ q → Γ ◂ Θ ∶ r
  π-cmp tr πp πq = π-ext tr (π-cmp-rf πp πq)
  π-frg : ∀ {Γ' Γ p p'} R → (∀ i → p (fs i) == p' i)
             → R ∣ Γ' ◂ Γ ∶ p → Γ' ◂ Γ ∶ p'
  π-frg R eq πp =
    π-ext eq (π-frg-rf R πp)

  -- projections forget variables
  π-≤ : ∀ {Γ' Γ p} → Γ' ◂ Γ ∶ p → len Γ' ≤N len Γ
  π-≤ {[]} {Γ} πp =
    0₁
  π-≤ {R ∣ Γ'} {[]} {p} πp =
    p fz
  π-≤ {R ∣ Γ'} {S ∣ Γ} {p} πp =
    Fin-finj-≤ {f = faceFin-restr (p ∘ fs) (p fz) λ _ ps=pz → PA4-Fin (prj1 πp ps=pz ⁻¹)}
               (faceFin-restr-inj {f = p ∘ fs} {p fz} (λ _ ps=pz → PA4-Fin (prj1 πp ps=pz ⁻¹))
                                  (injective-cmp fs-inj (prj1 πp)))


  -- the context bijections are bijections and context morphisms (i.e. preserve the typing of variables)

  infix 2 _≡_∶_
  _≡_∶_ : (Γ Γ' : Ctx) → (Fin (len Γ) → Fin (len Γ')) → Set
  Γ ≡ Γ' ∶ f = is-invrt f × isCtxMor Γ Γ' f
  ≡∶iv : ∀ {Γ Γ' f} → Γ ≡ Γ' ∶ f → is-invrt f
  ≡∶iv = prj1
  ≡∶cm : ∀ {Γ Γ' f} → Γ ≡ Γ' ∶ f → isCtxMor Γ Γ' f
  ≡∶cm = prj2

  ≡∶ext : ∀ {Γ Γ' f f'} → (∀ i → f i == f' i) → Γ' ≡ Γ ∶ f → Γ' ≡ Γ ∶ f'
  ≡∶ext {Γ} {Γ'} {f} {f'} eq bj = =invrt-is-invrt (λ i → eq i ⁻¹) (≡∶iv bj)
                                  , λ {T i} inc → ((λ x → Γ ∋ x ∶ T) ● eq i) (≡∶cm bj inc)
  ≡∶id : ∀ {Γ} → Γ ≡ Γ ∶ id
  ≡∶id {Γ} = id-is-invrt {Fin (len Γ)}
             , id
  ≡∶rfl : ∀ {Γ f} → (∀ i → i == f i) → Γ ≡ Γ ∶ f
  ≡∶rfl =id = ≡∶ext =id ≡∶id
  ≡∶cmp : ∀ {Γ Δ Θ f g h} → (∀ i → h i == g (f i))
             → Γ ≡ Δ ∶ f → Δ ≡ Θ ∶ g → Γ ≡ Θ ∶ h
  ≡∶cmp {Γ} {Δ} {Θ} {f} {g} {h} tr fbj gbj = invrt-cmp tr (≡∶iv fbj) (≡∶iv gbj)
                                             , CtxMor-cmp tr (≡∶cm fbj) (≡∶cm gbj)
  ≡∶cnc-rf : ∀ {Γ Γ' f} R → Γ' ≡ Γ ∶ f → (R ∣ Γ') ≡ (R ∣ Γ) ∶ (liftFin f)
  ≡∶cnc-rf {Γ'} {Γ} {f} R  bj = liftFin-invrt (≡∶iv bj)
                                , liftFinCtxMor R (≡∶cm bj)
  ≡∶swp-rf : ∀ {Γ' Γ p } R S → R ∣ S ∣ Γ' ≡ Γ ∶ p → S ∣ R ∣ Γ' ≡ Γ ∶ (p ∘ swapFin id)
  ≡∶swp-rf R S bj = invrt-cmp-rf (swapFin-invrt id-is-invrt) (≡∶iv bj)
                    , swapFinCtxMor R S (≡∶cm bj)
  
  -- the bijections are the projections between contexts of the same length
  -- (the following three probably provide an equivalence
  -- between `Γ' ≡ Γ ∶ f` and `len Γ' == len Γ` × Γ' ◂ Γ ∶ f)
  ≡∶-same-len : ∀ {Γ Γ' f} → Γ' ≡ Γ ∶ f → len Γ' == len Γ
  ≡∶-same-len bj = Fin-invrt-=len (≡∶iv bj)
  ≡∶to◂∶ : ∀ {Γ Γ' f} → Γ' ≡ Γ ∶ f → Γ' ◂ Γ ∶ f
  ≡∶to◂∶ {Γ} {Γ'} {f} bj = invrt-is-injective (≡∶iv bj)
                            , ≡∶cm bj
  ◂∶to≡∶ : ∀ {Γ Γ' p} → len Γ' == len Γ → Γ' ◂ Γ ∶ p → Γ' ≡ Γ ∶ p
  ◂∶to≡∶ {Γ} {Γ'} {p} eq πp = inj+surj-is-invrt (◂∶ij πp) (Fin-pgnhl eq (◂∶ij πp))
                               , ◂∶cm πp


  -- the order of premises in a derivation does not matter,
  -- up to renaming the variables accordingly
  ≡∶-⊢ : ∀ {Γ Γ' f M T} → Γ' ≡ Γ ∶ f
                → Γ' ⊢ M ∶ T → Γ ⊢ rename M f ∶ T
  ≡∶-⊢ bij (⊢-var inc) = ⊢-var (≡∶cm bij inc)
  ≡∶-⊢ bij (⊢-abs {T = T} der) = ⊢-abs (≡∶-⊢ (≡∶cnc-rf T bij) der)
  ≡∶-⊢ bij (⊢-app der₁ der₂) = ⊢-app (≡∶-⊢ bij der₁) (≡∶-⊢ bij der₂)


  -- if a type occurs in a context, WLOG it occurs in the first position
  ≡∶-mv-fst : ∀ {Γ T i} → Γ ∋ i ∶ T
               → Σ[ Ctx ] (λ x →
                   Σ[ (Fin (suc (len x)) → Fin (len Γ)) ] ((T ∣ x) ≡ Γ ∶_))
  ≡∶-mv-fst {T ∣ Γ} {T} {fz} here =
    Γ
    ,, id
    ,, ≡∶id
  ≡∶-mv-fst {R ∣ Γ} {T} {fs i} (there inc) =
    (R ∣ pj1 ih)
    ,, ( liftFin (pj1 (pj2 ih)) ∘ swapFin id )
    ,, ≡∶swp-rf {p = liftFin (pj1 (pj2 ih))} R T (≡∶cnc-rf R (pj2 (pj2 ih)))
    where ih : Σ[ Ctx ] (λ x →
                   Σ[ (Fin (suc (len x)) → Fin (len Γ)) ] ((T ∣ x) ≡ Γ ∶_))
          ih = ≡∶-mv-fst inc


  ---------------------------
  -- weakening is admissible
  ---------------------------
  
  wkn-π : ∀ {Γ Γ' p M T} → Γ' ◂ Γ ∶ p → Γ' ⊢ M ∶ T → Γ ⊢ rename M p ∶ T
  wkn-π πp (⊢-var inc) = ⊢-var (◂∶cm πp inc)
  wkn-π πp (⊢-abs {T = T} der) = ⊢-abs (wkn-π (π-cnc-rf T πp) der)
  wkn-π πp (⊢-app der₁ der₂) = ⊢-app (wkn-π πp der₁) (wkn-π πp der₂)

  wkn-0 : ∀ {Γ M T} R → Γ ⊢ M ∶ T → R ∣ Γ ⊢ (ext M) ∶ T
  wkn-0 R der = wkn-π (π-dsp R) der


  -----------------------
  -- typed substitutions
  -----------------------
  infix 10 _←_∶_
  data _←_∶_ : (Γ Γ' : Ctx) → (Fin (len Γ) → Trm (len Γ')) → Set where
    σ-! : ∀ {Γ' s} → [] ← Γ' ∶ s
    σ-trm : ∀ {Γ Γ' s s' T M} → (M == s' fz) → (∀ i → s i == s' (fs i))
                 → Γ ← Γ' ∶ s → Γ' ⊢ M ∶ T → T ∣ Γ ← Γ' ∶ s'


  -- substitutions have lengths
  -- which we never use since it is equal to len Γ
  σ-len : ∀ {Γ Γ' s} → Γ ← Γ' ∶ s → Nat
  σ-len σ-! = zero
  σ-len (σ-trm _ _ σs _) = suc (σ-len σs)


  -- if T occurs in the i-th position in Γ' and Γ' ← Γ ∶ s,
  -- then the term s i has type T
  σ-∋∶ : ∀ {Γ Γ' s} → Γ ← Γ' ∶ s → ∀ {T i} → Γ ∋ i ∶ T → Γ' ⊢ s i ∶ T
  σ-∋∶ (σ-trm eqz eqs σs der) here = ⊢∶-= eqz  der
  σ-∋∶ (σ-trm eqz eqs σs der) {_} {fs i} (there inc) = ⊢∶-= (eqs i) (σ-∋∶ σs inc)

  σ-∋∶' : ∀ {Γ Γ' s} → Γ ← Γ' ∶ s → ∀ i → Γ' ⊢ s i ∶ pr Γ i
  σ-∋∶' σs i = σ-∋∶ σs (varty _ i)

  -- extensions of substitution are substitutions
  σ-frg : ∀ {Γ Γ' s s'} T → (∀ i → ext (s i) == s' i)
            → Γ ← Γ' ∶ s → Γ ← T ∣ Γ' ∶ s'
  σ-frg T eq σ-! =
    σ-!
  σ-frg T eq (σ-trm eqz eqs σs der) =
    σ-trm (=ap ext eqz • eq fz) (λ i → =ap ext (eqs i) • eq (fs i))
          (σ-frg T (λ i → =rf) σs)
          (wkn-0 T der) 
  
  σ-wlift : ∀ {Γ Γ' s s'} T → (∀ i → wlift s i == s' i)
              → Γ ← Γ' ∶ s → T ∣ Γ ← T ∣ Γ' ∶ s'
  σ-wlift T eq σ-! =
    σ-trm (eq fz) (λ i → eq (fs i)) σ-! (⊢-var here)
  σ-wlift T eq (σ-trm eqz eqs σs der) =
    σ-trm (eq fz) (λ i → eq (fs i))
          (σ-trm (=ap ext eqz) (λ i → =ap ext (eqs i))
          (σ-frg T (λ _ → =rf) σs) (wkn-0 T der))
          (⊢-var here)

  -- projections, and bijections, are substitutions
  ◂∶to← : ∀ {Γ Γ' p s} → (∀ i → var (p i) == s i) → Γ ◂ Γ' ∶ p → Γ ← Γ' ∶ s
  ◂∶to← {[]} {Γ'} {p} {s} eq πp = σ-!
  ◂∶to← {R ∣ Γ} {Γ'} {p} {s} eq πp = σ-trm {s = var ∘ p ∘ fs} (eq fz) (λ x → eq (fs x))
                                           (◂∶to← (λ _ → =rf) (fs-inj ∘ ◂∶ij πp , CtxMor-cmp-rf there (◂∶cm πp)))
                                           (⊢-var (◂∶cm πp here))
  ≡∶to← : ∀ {Γ Γ' f s} → (∀ i → var (f i) == s i) → Γ ≡ Γ' ∶ f → Γ ← Γ' ∶ s
  ≡∶to← eq = ◂∶to← eq ∘ ≡∶to◂∶

  -- substitutions of variables are context morphisms
  σ-isCtxMor : ∀ {Γ Γ' f s} → (∀ i → var (f i) == s i) → Γ ← Γ' ∶ s → isCtxMor Γ Γ' f
  σ-isCtxMor {R ∣ Γ} {Γ'} {f} {s} vf=s (σ-trm eqM eqs σs' derM) {R} {fz} here =
    ⊢∶-∋∶ derM (eqM • vf=s fz ⁻¹)
  σ-isCtxMor {R ∣ Γ} {Γ'} {f} {s} vf=s (σ-trm eqM eqs σs' derM) {T} {fs i} (there inc) =
    ih inc
    where ih : isCtxMor Γ Γ' (f ∘ fs)
          ih = σ-isCtxMor (λ x → vf=s (fs x) • eqs x ⁻¹) σs'

  σtoπ : ∀ {Γ Γ' p s} → (∀ {i j} → p i == p j → i == j)
           → (∀ i → var (p i) == s i) → Γ ← Γ' ∶ s → Γ ◂ Γ' ∶ p
  σtoπ inj eq σs = inj , σ-isCtxMor eq σs

  σ-id : ∀ {Γ} → Γ ← Γ ∶ var
  σ-id {Γ} = ◂∶to← (λ i → =rf) (π-id (λ _ → =rf))

  σ-rfl : ∀ {Γ s} → (∀ i → var i == s i) → Γ ← Γ ∶ s
  σ-rfl {Γ} eq = ◂∶to← eq (π-id (λ _ → =rf))

  ←∶v-∋∶ : ∀ {Γ Γ' s} → Γ ← Γ' ∶ s → ∀ {i j} → s i == var j → Γ' ∋ j ∶ pr Γ i
  ←∶v-∋∶ σs {i} eq = ⊢∶-∋∶ (σ-∋∶' σs i) eq

  -- the substitution var ∘ pr₁₁ where (pr₁₁ : 0₂, 1₂ ⊢> 0₁)
  pr₁₁ : Fin two → Fin one
  pr₁₁ = Fin-diag {zero}
  σdiag : ∀ {T s} → (∀ i → var fz == s i) → (T ∣ T ∣ []) ← (T ∣ []) ∶ s
  σdiag {T} {s} eqv = σ-trm (eqv fz) aux σ-id (⊢-var here)
    where aux : (i : Fin one) → var i == s (fs i)
          aux fz = eqv (fs fz)

  -- term sections are substitutions
  σ-trmsect : ∀ {Γ T M} → Γ ⊢ M ∶ T → T ∣ Γ ← Γ ∶ trmsect M
  σ-trmsect der = σ-trm =rf (λ _ → =rf) σ-id der

  ------------------------------
  -- substitution is admissible
  ------------------------------

  σ-subst-all : ∀ {Γ Γ' s T M} → Γ ← Γ' ∶ s → Γ ⊢ M ∶ T → Γ' ⊢ subst-all M s ∶ T
  σ-subst-all σs (⊢-var inc) = σ-∋∶ σs inc
  σ-subst-all σs (⊢-abs der) = ⊢-abs (σ-subst-all (σ-wlift _ (λ _ → =rf) σs) der)
  σ-subst-all σs (⊢-app der₁ der₂) = ⊢-app (σ-subst-all σs der₁) (σ-subst-all σs der₂)

  σ-subst-0 : ∀ {Γ R T M N} → Γ ⊢ N ∶ R → R ∣ Γ ⊢ M ∶ T → Γ ⊢ subst-0 M N ∶ T
  σ-subst-0 der₁ der₂ = σ-subst-all (σ-trmsect der₁) der₂


  ---------------------
  -- subject reduction
  ---------------------
  subj-red : ∀ {Γ T M N} → M ⟶ N → Γ ⊢ M ∶ T → Γ ⊢ N ∶ T
  subj-red (β M N) der =
    σ-subst-0 (⊢-app-premᵣ der) (⊢-abs-prem (⊢-app-premₗ der))
  subj-red (βlam stp) (⊢-abs der) =          ⊢-abs (subj-red stp der)
  subj-red (βappₗ stp) (⊢-app der₁ der₂) =    ⊢-app (subj-red stp der₁) der₂
  subj-red (βappᵣ stp) (⊢-app der₁ der₂) =    ⊢-app der₁ (subj-red stp der₂)
  -- it is possible to make the term `M` explicit everywhere,
  -- BUT in the third clause:
  -- doing so makes the last two clauses light grey
  -- meaning that they do NOT hold definitionally
  -- this also happens in `⟶-subst-all` and `⟶<≡>` (LambdaCalculus.agda)


  ------------
  -- progress
  ------------
  
  progr : ∀ {T M} → [] ⊢ M ∶ T → is-normal M → is-value M
  progr (⊢-abs der) nrm = val-lam (nrm-lam nrm)
  progr {T} (⊢-app {M = M} {N} der₁ der₂) nrm = N₀ind (nrm (subst-0 M' N) stp')
    where nrmM : is-normal M
          nrmM = nrm-appₗ nrm
          M' : Trm one
          M' = pj1 (⊢-val-is-lam der₁ (progr der₁ nrmM))
          λ=M : lam M' == M
          λ=M = pj2 (⊢-val-is-lam der₁ (progr der₁ nrmM))
          stp' : app M N ⟶ subst-0 M' N
          stp' = =transp (λ x → app x N ⟶ subst-0 M' N) λ=M (β M' N)


  ------------------
  -- neutral terms
  ------------------
  
  data is-neutral {n} : Trm n → Set where
    ntr-var : ∀ {i} → is-neutral (var i)
    ntr-app : ∀ {M N} → is-neutral M → is-neutral (app M N)

  var-is-neutral : ∀ {n M} → Trm-is-var {n} M → is-neutral M
  var-is-neutral {n} {M} Mvar = (is-neutral ● (pj2 Mvar)) (ntr-var {i = pj1 Mvar})
  neutral-is-var+app : ∀ {n M} → is-neutral {n} M → Trm-is-var M + Trm-is-app M
  neutral-is-var+app (ntr-var {i = i}) = inl (i ,, =rf) 
  neutral-is-var+app (ntr-app {M₁} {M₂} _) = inr ((M₁ , M₂) ,, =rf)
  -- and `M₁` is app+var as well, and so on
  neutral≠lam : ∀ {n M} → is-neutral M → ¬ (Σ[ Trm (suc n) ] (λ x → lam x == M))
  neutral≠lam ntr-var islam = lam≠var _ (pj1 islam) (pj2 islam)
  neutral≠lam (ntr-app ntr) islam = lam≠app (pj1 islam) _ _ (pj2 islam)
  neutral-rename : ∀ {n m} (f : Fin n → Fin m) {M}
                        → is-neutral M → is-neutral (rename M f)
  neutral-rename f {var _} ntr-var = ntr-var
  neutral-rename f {app _ _} (ntr-app Mntr) = ntr-app (neutral-rename f Mntr)
  neutral-ext : ∀ {n M} → is-neutral {n} M → is-neutral (ext M)
  neutral-ext = neutral-rename fs
  neutral-extk : ∀ k {n M} → is-neutral {n} M → is-neutral (ext[ k ] M)
  neutral-extk zero = id
  neutral-extk (suc k) = neutral-ext ∘ neutral-extk k


  ---------------------------
  -- reducibility candidates
  ---------------------------
{-
  -- the following inductive definition of `red-cand` is NOT strictly positive

  data red-cand {n} (M : Trm n) : (T : Ty) → Set where
    rc-atm : ∀ {a} → isStrNrm {n} M → red-cand M (atm a)
    rc-⇒ : ∀ {T S} → (∀ {N} → red-cand {n} N T → red-cand (app M N) S)
                   → red-cand M (T ⇒ S)

  -- so define it by recursion into `Set`
-}
  red-cand : ∀ {n} (M : Trm n) (T : Ty) → Set
  red-cand {n} M (atm a) = isStrNrm M
  red-cand {n} M (T ⇒ S) = ∀ k {N} → red-cand N T → red-cand (app (ext[ k ] M) N) S
  -- the second clause quantifies over all `k : Nat` and `N : Trm (k +N n)`
  -- as I am not able to prove that red-cand is invariant under weakening otherwise

  -- the three fundamental properties of reducibility candidates
  red-candStrNrm : ∀ {n} → Trm n → Ty → Set
  red-candStrNrm M T = red-cand M T → isStrNrm M
  red-candDwnCl : ∀ {n} → Trm n → Ty → Set
  red-candDwnCl M T = red-cand M T → ∀ {N} → M ⟶ N → red-cand N T
  red-candUpCl : ∀ {n} → Trm n → Ty → Set
  red-candUpCl M T = is-neutral M → (∀ {N} → M ⟶ N → red-cand N T) → red-cand M T

  red-cand-props : ∀ {n} M T → red-candStrNrm M T × red-candDwnCl M T × red-candUpCl M T
  red-cand-props {n} M (atm a) =
      id
    , (λ nrm {N} → strnrm-⟶ {N = N} nrm)
    , λ _ → strnrm-stp-any {n} {M}
  red-cand-props {n} M (T ⇒ S) =
    RC1
    , RC2
    , RC3
    where rc1 : ∀ {k} P R → red-candStrNrm {k} P R
          rc1 P R = prj1 (red-cand-props P R)
          rc2 : ∀ {k} P R → red-candDwnCl {k} P R
          rc2 P R = prj1 (prj2 (red-cand-props P R))
          rc3 : ∀ {k} P R → red-candUpCl {k} P R
          rc3 P R = prj2 (prj2 (red-cand-props P R))
          nrmaux : ∀ {N} → red-candStrNrm (app M N) S --red-cand (app M N) S → isStrNrm (app M N)
          nrmaux {N} = rc1 (app M N) S
          strnrmₗₑᵥ-appvar : ∀ {k} → isStrNrmₗₑᵥ k (app (ext M) (var fz)) → isStrNrmₗₑᵥ k M
          strnrmₗₑᵥ-appvar snw = strnrmₗₑᵥ-ext (strnrmₗₑᵥ-appₗ snw)
          strnrm-appvar : isStrNrm (app (ext M) (var fz)) → isStrNrm M
          strnrm-appvar snw = pj1 snw ,, strnrmₗₑᵥ-appvar (pj2 snw)
          varz-red-cand : ∀ {n} i → red-cand (var {n} i) T
          varz-red-cand i = rc3 (var i) T ntr-var (λ s → N₀ind (nrm-var _ s))
          RC1 : (fnc : ∀ k {N} → red-cand N T → red-cand (app (ext[ k ] M) N) S)
                      → isStrNrm M
          RC1 fnc = strnrm-appvar (rc1 (app (ext M) (var fz)) S (fnc one (varz-red-cand fz)))

          RC2 : (fnc : ∀ k {N} → red-cand N T → red-cand (app (ext[ k ] M) N) S)
                     → {M' : Trm n} → M ⟶ M'
                       → ∀ k {N} → red-cand N T → red-cand (app (ext[ k ] M') N) S
          RC2 fnc {M'} stp k {N} rc = rc2 (app (ext[ k ] M) N) S (fnc k rc) (βappₗ (⟶-extk k stp))

          -- use the fact that a reduction `app M N ⟶ P` is either `β`, `βappₗ`, or `βappᵣ`,
          -- and it cannot be `β` when `M` is neutral
          Mβapp-inv : ∀ k N → is-invrt (βapp-stp {k +N n} {ext[ k ] M} {N})
          Mβapp-inv k N = equiv-is-invrt (βapp-eqv {k +N n} {ext[ k ] M} {N})
          RC3-auxₗ : (∀ {M'} → M ⟶ M' → red-cand M' (T ⇒ S))
                      → ∀ k {N} → red-cand N T
                      → (MM : Σ[ Trm (k +N n) ] (ext[ k ] M ⟶_))
                        → red-cand (app (pj1 MM) N) S
          RC3-auxₗ fnc k {N} rc MM =
            =transp (λ x → red-cand x S)
                    (=ap (λ x → app x N) (prj1 (pj2 (⟶-extk⁻¹g k  (pj2 MM)))))
                    (fnc (prj2 (pj2 (⟶-extk⁻¹g k  (pj2 MM)))) k rc)

          RC3-aux : is-neutral M → (∀ {M'} → M ⟶ M' → red-cand M' (T ⇒ S))
                    → ∀ {l} k {N} → isStrNrmₗₑᵥ l N → red-cand N T
                      → ∀ {P} → app (ext[ k ] M) N ⟶ P → red-cand P S
          RC3-aux Mntr fnc {zero} k {N} (strnrm-nrm Nnrm) Nrc {P} stp =
            ((λ x → red-cand x S) ● (=pj1 (prj2 (pj2 (Mβapp-inv k N)) (P ,, stp))))
              (+ind3 (λ x → red-cand (pj1 (βapp-stp x)) S)
                     (λ islam → N₀ind (neutral≠lam (neutral-extk k Mntr) islam))
                     (RC3-auxₗ fnc k Nrc)
                     (λ NN → N₀ind (Nnrm (pj1 NN) (pj2 NN)))
                     (pj1 (Mβapp-inv k N) (P ,, stp)))
          RC3-aux Mntr fnc {suc l} k {N} (strnrm-stp Nsns) Nrc {P} stp =
            ((λ x → red-cand x S) ● (=pj1 (prj2 (pj2 (Mβapp-inv k N)) (P ,, stp))))
              (+ind3 (λ x → red-cand (pj1 (βapp-stp x)) S)
                     (λ islam → N₀ind (neutral≠lam (neutral-extk k Mntr) islam))
                     (RC3-auxₗ fnc k Nrc)
                     (λ NN → rc3 (app (ext[ k ] M) (pj1 NN)) S
                                  (ntr-app (neutral-extk k Mntr))
                     -- because of this recursive call...
                                  (RC3-aux Mntr fnc {l} k (Nsns (pj2 NN))
                                           (rc2 N T Nrc (pj2 NN))) )
                     -- ...it seems hard to do induction only on the right-hand side
                     (pj1 (Mβapp-inv k N) (P ,, stp)))

          RC3 : is-neutral M
                  → (∀ {M'} → M ⟶ M' → red-cand M' (T ⇒ S))
                    → ∀ k {N} → red-cand N T → red-cand (app (ext[ k ] M) N) S
          RC3 Mntr fnc k {N} Nrc =
            rc3 (app (ext[ k ] M) N) S
                (ntr-app (neutral-extk k Mntr))
                (RC3-aux Mntr fnc k (pj2 (rc1 N T Nrc)) Nrc)
  -- end red-cand-props

  red-cand-lam : ∀ {n M R S} → (∀ {N} → red-cand {n} N R → red-cand (subst-0 M N) S)
                      → red-cand (lam M) (R ⇒ S)
  red-cand-lam {n} {M} {R} {S} pf k {N} Nrc = {!!}
    where

  -- the fundamental lemma

  red-cand-⊢ : ∀ {Γ T M f} → Γ ⊢ M ∶ T → (∀ i → red-cand {len Γ} (f i) (pr Γ i))
                    → red-cand (subst-all M f) T
  red-cand-⊢ {Γ} {T} {var i} {f} (⊢-var inc) pf =
    (red-cand (f i) ● vartypr inc) (pf i)
  red-cand-⊢ {Γ} {R ⇒ S} {lam M} {f} (⊢-abs der) pf =
    {!!}
    where ih : ∀ {g} → (∀ i → red-cand {len Γ} (g i) (pr (R ∣ Γ) i))
                 → red-cand (subst-all M g) S
          ih = {!!} --red-cand-⊢ der
          ih0 : ∀ {N} → red-cand {len Γ} N R → red-cand (subst-0 M N) S
          ih0 {N} rc = {!ih!}
  red-cand-⊢ {Γ} {T} {app M N} {f} (⊢-app der₁ der₂) pf = {!!}

-- end file
