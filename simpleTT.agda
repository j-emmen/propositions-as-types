{-# OPTIONS --without-K #-}

module simpleTT (Atm : Set) where
  open import Nat-and-Fin public
  open import Lambda-Calculus public

  ----------------
  -- Simple Types
  ----------------

  infixr 30 _⇒_
  data Ty : Set where
    atm : Atm → Ty
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
  neutral≠lam ntr-var islam = lam≠var (pj2 islam)
  neutral≠lam (ntr-app ntr) islam = lam≠app (pj2 islam)
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

  -- renaming along bijections preserve reducibility candidates
  red-cand-invrt : ∀ {n m M T} {f : Fin n → Fin m} → is-invrt f
                     → red-cand {n} M T → red-cand {m} (rename M f) T
  red-cand-invrt {n} {m} {M} {atm A} {f} invf Msn = strnrm-rename⁻¹ f Msn
  red-cand-invrt {n} {m} {M} {T ⇒ S} {f} invf Mrc⇒ k {N} Nrc =
    ((λ x → red-cand x S) ● Peq) Prc
    where kf : Fin (k +N n) → Fin (k +N m)
          kf = Fin[ Fin+N-inl ∣ Fin+N-inr ∘ f ]
          invkf : is-invrt kf
          invkf = Fin+N-fnc-invrt id-is-invrt invf
          N' : Trm (k +N n)
          N' = rename N (pj1 invkf)
          N'rc : red-cand N' T
          N'rc = red-cand-invrt (inv-is-invrt invkf) Nrc
          P : Trm (k +N m)
          P = rename (app (ext[ k ] M) N') kf
          Prc : red-cand P S
          Prc = red-cand-invrt invkf (Mrc⇒ k N'rc)
          Peq : P == app (ext[ k ] (rename M f)) N
          Peq = =ap₂ app
            (=proof
            rename (ext[ k ] M) kf                 ==[ =ap (λ x → rename x kf) (ext[ k ]-is-rename M) ] /
            rename (rename M (Fin+N-inr {k})) kf   ==[ rename-sqg M (Fin+N-trr (Fin+N-inl {k}) _) ] /
            rename (rename M f) (Fin+N-inr {k})    ==[ ext[ k ]-is-rename⁻¹ (rename M f) ]∎
            ext[ k ] (rename M f) ∎)
            (=proof
            rename N' kf               ==[ rename-act N (pj1 invkf) kf ] /
            rename N (kf ∘ pj1 invkf)  ==[ rename-id N (prj2 (pj2 invkf)) ]∎
            N ∎)

  red-cand-sucswap : ∀ {n m M T} → red-cand {n +N suc m} M T
                       → red-cand {suc n +N m} (Trm-sucswap M) T
  red-cand-sucswap {n} {m} Mrc = red-cand-invrt (sucswap-invrt {n} {m}) Mrc
  red-cand-sucswap⁻¹ : ∀ {n m M T} → red-cand {suc n +N m} M T
                       → red-cand {n +N suc m} (Trm-sucswap⁻¹ M) T
  red-cand-sucswap⁻¹ {n} {m} Mrc = red-cand-invrt (inv-is-invrt (sucswap-invrt {n} {m})) Mrc

  -- weakening preserves reducibility candidates
  red-cand-ext : ∀ {n M T} → red-cand {n} M T → red-cand {suc n} (ext M) T
  red-cand-ext {n} {M} {atm A} Msn = strnrm-ext⁻¹ Msn
  red-cand-ext {n} {M} {T ⇒ S} Mrc⇒ k {N} Nrc =
    ((λ x → red-cand x S) ● Peq) Prc
    where N' : Trm (suc k +N n)
          N' = Trm-sucswap N
          Neq : rename N' sucswap-fnc⁻¹ == N
          Neq = prj1 (pj2 Trm-sucswap-invrt) N
          N'rc : red-cand N' T
          N'rc = red-cand-invrt (sucswap-invrt {k} {n}) Nrc
          P : Trm (k +N suc n)
          P = Trm-sucswap⁻¹ (app (ext[ suc k ] M) N')
          Peq : P == app (ext[ k ] (ext M)) N
          Peq = =ap₂ app (ext[ k ]ext-inv⁻¹ M) Neq
          Prc : red-cand P S
          Prc = red-cand-invrt (inv-is-invrt (sucswap-invrt {k} {n})) (Mrc⇒ (suc k) N'rc)

  red-cand-ext[_] : ∀ k {n M T} → red-cand {n} M T → red-cand {k +N n} (ext[ k ] M) T
  red-cand-ext[ zero ] {n} {M} {T} Mrc = Mrc
  red-cand-ext[ suc k ] {n} {M} {T} Mrc = red-cand-ext (red-cand-ext[ k ] Mrc)


  -- the three fundamental properties of reducibility candidates
  red-candStrNrm : ∀ {n} → Trm n → Ty → Set
  red-candStrNrm M T = red-cand M T → isStrNrm M
  red-candDwnCl : ∀ {n} → Trm n → Ty → Set
  red-candDwnCl M T = red-cand M T → ∀ {N} → M ⟶ N → red-cand N T
  red-candUpCl red-candUpCl' : ∀ {n} → Trm n → Ty → Set
  red-candUpCl M T = is-neutral M → (∀ {N} → M ⟶ N → red-cand N T) → red-cand M T
  red-candUpCl' M T = ¬ (Trm-is-lam M) → (∀ {N} → M ⟶ N → red-cand N T) → red-cand M T

  red-cand-props : ∀ {n} M T → red-candStrNrm M T × red-candDwnCl M T × red-candUpCl M T
  red-cand-props {n} M (atm a) =
      id
    , (λ nrm {N} → strnrm-⟶ {N = N} nrm)
    , (λ _ → strnrm-stp-any {n} {M})
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
          RC2 fnc {M'} stp k {N} rc = rc2 (app (ext[ k ] M) N) S (fnc k rc) (βappₗ (⟶-ext[ k ] stp))

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
                    (=ap (λ x → app x N) (prj1 (pj2 (⟶-ext[ k ]⁻¹g  (pj2 MM)))))
                    (fnc (prj2 (pj2 (⟶-ext[ k ]⁻¹g  (pj2 MM)))) k rc)

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

  red-cand-strnrm : ∀ {n} M T → red-candStrNrm {n} M T
  red-cand-strnrm M T = prj1 (red-cand-props M T)
  red-cand-dwncl : ∀ {n} M T → red-candDwnCl {n} M T
  red-cand-dwncl M T = prj1 (prj2 (red-cand-props M T))
  red-cand-upcl : ∀ {n} M T → red-candUpCl {n} M T
  red-cand-upcl M T = prj2 (prj2 (red-cand-props M T))

  red-cand-var : ∀ {n} i T → red-cand {n} (var i) T
  red-cand-var i T = red-cand-upcl (var i) T ntr-var (λ varred → N₀rec (¬var⟶ varred))

  -- To have up-ward closure it is in fact enough to assume that the term is not `lam`
  red-cand-upcl' : ∀ {n} M T → red-candUpCl' {n} M T
  red-cand-upcl' {n} M (atm A) M≠lam fnc =
    strnrm-stp-any {n} {M} fnc
  red-cand-upcl' {n} M (T ⇒ S) M≠lam fnc k {P} Prc =
    rc3' (app (ext[ k ] M) P) S
         (λ z → lam≠app (pj2 z))
         (RC3-aux fnc k (pj2 (red-cand-strnrm P T Prc)) Prc )
    where rc3' : ∀ {k} P R → red-candUpCl' {k} P R
          rc3' P R = red-cand-upcl' P R          
          -- use the fact that a reduction `app M N ⟶ P` is either `β`, `βappₗ`, or `βappᵣ`,
          -- and it cannot be `β` when `M` is not `lam`
          Mβapp-inv : ∀ k N → is-invrt (βapp-stp {k +N n} {ext[ k ] M} {N})
          Mβapp-inv k N = equiv-is-invrt (βapp-eqv {k +N n} {ext[ k ] M} {N})
          RC3-auxₗ : (∀ {M'} → M ⟶ M' → red-cand M' (T ⇒ S))
                      → ∀ k {N} → red-cand N T
                      → (MM : Σ[ Trm (k +N n) ] (ext[ k ] M ⟶_))
                        → red-cand (app (pj1 MM) N) S
          RC3-auxₗ fnc k {N} rc MM =
            =transp (λ x → red-cand x S)
                    (=ap (λ x → app x N) (prj1 (pj2 (⟶-ext[ k ]⁻¹g  (pj2 MM)))))
                    (fnc (prj2 (pj2 (⟶-ext[ k ]⁻¹g  (pj2 MM)))) k rc)

          RC3-aux : (∀ {M'} → M ⟶ M' → red-cand M' (T ⇒ S))
                    → ∀ {l} k {N} → isStrNrmₗₑᵥ l N → red-cand N T
                      → ∀ {P} → app (ext[ k ] M) N ⟶ P → red-cand P S
          RC3-aux fnc {zero} k {N} (strnrm-nrm Nnrm) Nrc {P} stp =
            ((λ x → red-cand x S) ● (=pj1 (prj2 (pj2 (Mβapp-inv k N)) (P ,, stp))))
              (+ind3 (λ x → red-cand (pj1 (βapp-stp x)) S)
                     (λ islam → N₀ind (M≠lam (ext[ k ]-lam-is-lam⁻¹ islam)))
                     (RC3-auxₗ fnc k Nrc)
                     (λ NN → N₀ind (Nnrm (pj1 NN) (pj2 NN)))
                     (pj1 (Mβapp-inv k N) (P ,, stp)))
          RC3-aux fnc {suc l} k {N} (strnrm-stp Nsns) Nrc {P} stp =
            ((λ x → red-cand x S) ● (=pj1 (prj2 (pj2 (Mβapp-inv k N)) (P ,, stp))))
              (+ind3 (λ x → red-cand (pj1 (βapp-stp x)) S)
                     (λ islam → N₀ind (M≠lam (ext[ k ]-lam-is-lam⁻¹ islam)))
                     (RC3-auxₗ fnc k Nrc)
                     (λ NN → rc3' (app (ext[ k ] M) (pj1 NN)) S
                                   (λ z → lam≠app (pj2 z))
                     -- because of this recursive call...
                                   (RC3-aux fnc {l} k (Nsns (pj2 NN))
                                            (red-cand-dwncl N T Nrc (pj2 NN))))
                     -- ...it seems hard to do induction only on the right-hand side
                     (pj1 (Mβapp-inv k N) (P ,, stp)))


{- unlikely that it holds
  red-cand-rename : ∀ {n m M T} f → red-cand {n} M T → red-cand {m} (rename M f) T
  red-cand-rename {M = M} {atm A} f Msn =
    strnrm-rename⁻¹ f Msn
  red-cand-rename {M = M} {T ⇒ S} f Mrc⇒ k {N} Nrc = {!!}
    where rcrnm : ∀ {P} (Prc : red-cand P T) → red-cand (rename (app (ext[ k ] M) P) (liftFin[ k ] f)) S
          rcrnm {P} Prc = red-cand-rename {T = S} (liftFin[ k ] f) (Mrc⇒ k Prc)
          aim : ∀ {P} (Prc : red-cand P T) → red-cand (app (rename (ext[ k ] M) (liftFin[ k ] f)) P) S
          aim = {!!}
-}


  red-cand-abs-lam : ∀ {n M S T}
              → (∀ h {Q} → red-cand {h +N n} Q S
                     → red-cand (subst-all M (Fin[ (λ (_ : N₁) → Q) ∣ ext[ h ] ∘ var ])) T)
                → ∀ k {N} → red-cand {k +N n} N S → (islam : Trm-is-lam (ext[ k ] (lam M)))
                  → red-cand (subst-0 (pj1 islam) N) T
  red-cand-abs-lam {n} {M} {S} {T} fnc k {N} Nrc islam =
    ((λ x → red-cand x T) ● eqaux islam) (fnc k Nrc)
    where extlam : Trm-is-lam (ext[ k ] (lam M))
          extlam = ext[ k ]-lam-is-lam (M ,, =rf)
          Meq : (islam : Trm-is-lam (ext[ k ] (lam M))) → Trm-sucswap (ext[ k ] M) == pj1 islam
          Meq islam = =proof
            Trm-sucswap (ext[ k ] M)    ==[ ext[ k ]-lam-swap M ⁻¹ ] /
            pj1 extlam              ==[ lam-inj (pj2 extlam • pj2 islam ⁻¹) ]∎
            pj1 islam ∎
          fnc-eq : ∀ i → Fin[ (λ _ → N) ∣ ext[ k ] ∘ var ] i == (trmsect N ∘ sucswap-fnc {k} {n} ∘ Fin+N-inr {k}) i
          fnc-eq fz = =ap (trmsect N) (sucswap-inrz⁻¹ {k})
          fnc-eq (fs i) = =proof
            Fin[ (λ _ → N) ∣ ext[ k ] ∘ var ] (fs i)      ==[ ext[ k ]var i ] /
            var (Fin+N-inr {k} i)                         ==[ =ap (trmsect N) (sucswap-inrr⁻¹ i) ]∎
            (trmsect N ∘ sucswap-fnc ∘ Fin+N-inr {k}) (fs i) ∎
          eqaux : (islam : Trm-is-lam (ext[ k ] (lam M)))
                    → subst-all M Fin[ (λ _ → N) ∣ ext[ k ] ∘ var ] == subst-0 (pj1 islam) N
          eqaux islam = =proof
            subst-all M Fin[ (λ _ → N) ∣ ext[ k ] ∘ var ]                 ==[ subst-all-ptw M fnc-eq ] /
            subst-all M (trmsect N ∘ sucswap-fnc {k} {n} ∘ Fin+N-inr {k})  ==[ subst-all-rename M _ _ ⁻¹ ] /
            subst-0 (rename M (sucswap-fnc {k} {n} ∘ Fin+N-inr {k})) N     ==[ =ap (λ x → subst-0 x N) (=proof
              rename M (sucswap-fnc {k} {n} ∘ Fin+N-inr {k})               ==[ rename-act⁻¹ M _ _ ] /
              Trm-sucswap (rename M (Fin+N-inr {k}))                       ==[ =ap Trm-sucswap (ext[ k ]-is-rename⁻¹ M) ] /
              Trm-sucswap (ext[ k ] M)                                     ==[ Meq islam ]∎
              pj1 islam ∎) ]∎
            subst-0 (pj1 islam) N ∎


  -- towards the fundamental lemma

  red-cand-abs-aux-deq-zero : ∀ {n} M {S T} → (∀ k {N} → red-cand {k +N n} N S
                                    → red-cand (subst-all M (Fin[ (λ (_ : N₁) → N) ∣ ext[ k ] ∘ var ])) T)
                              → ∀ {lM lN} → lM +N lN ≤N zero → isStrNrmₗₑᵥ lM M → ∀ k {N} → isStrNrmₗₑᵥ lN N
                                → red-cand {k +N n} N S → red-cand (app (ext[ k ] (lam M)) N) T
  red-cand-abs-aux-deq-zero {n} M {S} {T} fnc {lM} {lN} deq Msn k {N} Nsn Nrc =
    red-cand-upcl' _ T
                   (λ z → lam≠app (pj2 z))
                   ( λ {Q} stp →
                       ((λ x → red-cand x T) ● =pj1 (prj2 (pj2 βapp-invMN) (Q ,, stp)))
                                              (upward (pj1 βapp-invMN (Q ,, stp))) )
    where lMz : zero == lM
          lNz : zero == lN
          lMz = sum-0-is-0 (≤Nz deq)
          lNz = sum-0-is-0' {lM} (≤Nz deq)
          Mnrm : is-normal M
          Nnrm : is-normal N
          Mnrm = (strnrm-zero ∘ (λ x → isStrNrmₗₑᵥ x M) ● lMz ⁻¹) Msn
          Nnrm = (strnrm-zero ∘ (λ x → isStrNrmₗₑᵥ x N) ● lNz ⁻¹) Nsn
          βapp-invMN : is-invrt (βapp-stp {k +N n} {ext[ k ] (lam M)} {N})
          βapp-invMN = equiv-is-invrt (βapp-eqv {k +N n} {ext[ k ] (lam M)} {N})
          upward : (z : Trm-is-lam (ext[ k ] (lam {n} M)) + Σ[ Trm _ ] (ext[ k ] (lam M) ⟶_) + Σ[ Trm _ ] (N ⟶_))
                   → red-cand (pj1 (βapp-stp z)) T
          upward = +ind3 (λ z → red-cand (pj1 (βapp-stp z)) T)
                         (red-cand-abs-lam fnc k Nrc)
                         (λ lMstp → N₀rec (Mnrm _ (βlam-inv-stp (prj2 (pj2 (⟶-ext[ k ]⁻¹g (pj2 lMstp)))))))
                         (λ Nstp → N₀rec (Nnrm _ (pj2 Nstp)))

  red-cand-abs-aux-deq-indstp : ∀ ll ( ih : ∀ {l} → l ≤N ll → ∀ {n} (M : Trm (suc n)) {S} {T}
                                            → (∀ k {N} → red-cand {k +N n} N S
                                                 → red-cand (subst-all M Fin[ (λ _ → N) ∣ (λ x → ext[ k ] (var x)) ]) T)
                                            → ∀ {lM} {lN} → lM +N lN ≤N l → isStrNrmₗₑᵥ lM M
                                            → ∀ k {N} → isStrNrmₗₑᵥ lN N → red-cand N S
                                              → red-cand (app (ext[ k ] (lam M)) N) T )
                                {n} M {S T} → (∀ k {N} → red-cand {k +N n} N S
                                    → red-cand (subst-all M (Fin[ (λ (_ : N₁) → N) ∣ ext[ k ] ∘ var ])) T)
                           → ∀ {lM lN} → lM +N lN ≤N suc ll → isStrNrmₗₑᵥ lM M
                           → ∀ k {N} → isStrNrmₗₑᵥ lN N → red-cand {k +N n} N S
                             → red-cand (app (ext[ k ] (lam M)) N) T
  red-cand-abs-aux-deq-indstp ll ih {n} M {S} {T} fnc {lM} {lN} deq Msn k {N} Nsn Nrc =
    red-cand-upcl' _ T (λ z → lam≠app (pj2 z))
                   (λ {P} s → ((λ y → red-cand y T) ● =pj1 (prj2 (pj2 βapp-invMN) (P ,, s)))
                                      (upward (pj1 βapp-invMN (P ,, s))))
    where βapp-invMN : is-invrt (βapp-stp {k +N n} {ext[ k ] (lam M)} {N})
          βapp-invMN = equiv-is-invrt (βapp-eqv {k +N n} {ext[ k ] (lam M)} {N})
          upward-r : (Nstp : Σ[ Trm _ ] (N ⟶_)) → red-cand (app (ext[ k ] (lam M)) (pj1 Nstp)) T
          upward-r Nstp = ih (≤N-rfl {ll}) M fnc
                             deqr
                             Msn k
                             (pj2 (strnrm-⟶ (lN ,, Nsn) (pj2 Nstp)))
                             (red-cand-dwncl N S Nrc (pj2 Nstp))
            where deqr-aux : lM +N lN == suc (lM +N pj1 (strnrm-⟶ₗₑᵥ Nsn (pj2 Nstp)))
                  deqr-aux = =ap (lM +N_) (prj2 (pj2 (strnrm-⟶ₗₑᵥ Nsn (pj2 Nstp)))) • +N-sucswap lM _
                  deqr : lM +N pj1 (strnrm-⟶ₗₑᵥ Nsn (pj2 Nstp)) ≤N ll
                  deqr = ((_≤N suc ll) ● deqr-aux) deq

          upward-l : (lMstp : Σ[ Trm _ ] (ext[ k ] (lam M) ⟶_)) → red-cand (app (pj1 lMstp) N) T
          upward-l lMstp = ((λ y → red-cand y T) ● =ap (λ x → app x N) lMeq)
                               (ih (≤N-rfl {ll}) M' fnc' deq' (prj1 (pj2 M'sn)) k Nsn Nrc)
            where lamM : Σ[ Trm n ] (λ x → (ext[ k ] x == pj1 lMstp) × lam M ⟶ x)
                  lamM = ⟶-ext[ k ]⁻¹g (pj2 lMstp)
                  M' : Trm (suc n)
                  M' = pj1 (βlam-inv (prj2 (pj2 lamM)))
                  lamM' : lam M' == pj1 lamM
                  lamM' = prj2 (pj1 (pj2 (βlam-inv (prj2 (pj2 lamM)))))
                  lMeq : ext[ k ] (lam M') == pj1 lMstp
                  lMeq = =ap ext[ k ] lamM' • prj1 (pj2 lamM)
                  Mstp : M ⟶ M'
                  Mstp = prj1 (pj1 (pj2 (βlam-inv (prj2 (pj2 lamM)))))
                  M'sn : Σ[ Nat ] (λ x → isStrNrmₗₑᵥ x M' × (lM == suc x))
                  M'sn = strnrm-⟶ₗₑᵥ Msn Mstp
                  fnc' : ∀ h {Q} → red-cand {h +N n} Q S
                           → red-cand (subst-all M' Fin[ (λ _ → Q) ∣ (λ x → ext[ h ] (var x)) ]) T
                  fnc' h {Q} Qrc = red-cand-dwncl (subst-all M _) T (fnc h Qrc)
                                                  (⟶-subst-all Fin[ (λ _ → Q) ∣ (λ x → ext[ h ] (var x)) ] Mstp)
                  deq' : pj1 M'sn +N lN ≤N ll
                  deq' = ((_≤N suc ll) ● =ap (_+N lN) (prj2 (pj2 M'sn))) deq

          upward : (z : Trm-is-lam (ext[ k ] (lam {n} M)) + Σ[ Trm _ ] (ext[ k ] (lam M) ⟶_) + Σ[ Trm _ ] (N ⟶_))
                        → red-cand (pj1 (βapp-stp z)) T
          upward = +ind3 (λ z → red-cand (pj1 (βapp-stp z)) T)
                         (red-cand-abs-lam fnc k Nrc)
                         upward-l
                         upward-r


  red-cand-abs-aux-deq : ∀ ll {n} M {S T} → (∀ k {N} → red-cand {k +N n} N S
                                    → red-cand (subst-all M (Fin[ (λ (_ : N₁) → N) ∣ ext[ k ] ∘ var ])) T)
                           → ∀ {lM lN} → lM +N lN ≤N ll → isStrNrmₗₑᵥ lM M → ∀ k {N} → isStrNrmₗₑᵥ lN N
                             → red-cand {k +N n} N S → red-cand (app (ext[ k ] (lam M)) N) T
  red-cand-abs-aux-deq =
    ≤N-ind' (λ x → ∀ {n} M {S T} → (∀ k {N} → red-cand {k +N n} N S
                                        → red-cand (subst-all M (Fin[ (λ (_ : N₁) → N) ∣ ext[ k ] ∘ var ])) T)
                         → ∀ {lM lN} → lM +N lN ≤N x → isStrNrmₗₑᵥ lM M → ∀ k {N} → isStrNrmₗₑᵥ lN N
                           → red-cand {k +N n} N S → red-cand (app (ext[ k ] (lam M)) N) T)
            red-cand-abs-aux-deq-zero
            red-cand-abs-aux-deq-indstp

  -- the fundamental lemma

  red-cand-⊢ : ∀ {Γ T M n} (f : Fin (len Γ) → Trm n)
                 → Γ ⊢ M ∶ T → (∀ i → red-cand {n} (f i) (pr Γ i))
                    → red-cand {n} (subst-all M f) T
  red-cand-⊢ {Γ} {T} {var i} f (⊢-var inc) pf =
    (red-cand (f i) ● vartypr inc) (pf i)
    -- doing induction on `inc` above makes the clause below propositional

  red-cand-⊢ {Γ} {R ⇒ S} {lam M} {n} f (⊢-abs der) pf k {N} Nrc =
    red-cand-abs-aux-deq (pj1 Mfsn +N pj1 Nsn)
                         (subst-all M (wlift f))
                         fnc
                         (≤N-rfl {pj1 Mfsn +N pj1 Nsn})
                         (pj2 Mfsn)
                         k
                         (pj2 Nsn)
                         Nrc

    where Mfrc-aux : ∀ i → red-cand (wlift f i) (pr (R ∣ Γ) i)
          Mfrc-aux fz = red-cand-var fz R
          Mfrc-aux (fs i) = red-cand-ext (pf i)
          Mfrc : red-cand (subst-all M (wlift f)) S
          Mfrc = red-cand-⊢ (wlift f) der Mfrc-aux
          Mfsn : isStrNrm (subst-all M (wlift f))
          Mfsn = red-cand-strnrm _ S Mfrc
          Nsn : isStrNrm N
          Nsn = red-cand-strnrm N R Nrc
          subeq-aux-fs : ∀ h {Q} i → ext[ h ] (f i)
                           == subst-all (ext (f i)) Fin[ (λ _ → Q) ∣ ext[ h ] ∘ var ]
          subeq-aux-fs h {Q} i = =proof
            ext[ h ] (f i)                      ==[ subst-all-ext-var-is-ext[ h ] (f i) ⁻¹ ] /
            subst-all (f i) (ext[ h ] ∘ var)    ==[ subst-all-extg⁻¹ (f i) _ ]∎
            subst-all (ext (f i)) Fin[ (λ _ → Q) ∣ ext[ h ] ∘ var ] ∎
          subeq-aux : ∀ h {Q} i → Fin[ (λ _ → Q) ∣ ext[ h ] ∘ f ] i
                                 == subst-all (wlift f i) Fin[ (λ _ → Q) ∣ ext[ h ] ∘ var ]
          subeq-aux h fz = =rf
          subeq-aux h (fs i) = subeq-aux-fs h i
          subeq : ∀ h {Q} → subst-all M Fin[ (λ _ → Q) ∣ ext[ h ] ∘ f ]
                            == subst-all (subst-all M (wlift f)) Fin[ (λ _ → Q) ∣ ext[ h ] ∘ var ]
          subeq h {Q} = =proof
            subst-all M Fin[ (λ _ → Q) ∣ ext[ h ] ∘ f ]
                      ==[ subst-all-ptw M (subeq-aux h) ] /
            subst-all M (λ i → subst-all (wlift f i) Fin[ (λ _ → Q) ∣ ext[ h ] ∘ var ])
                      ==[ subst-all-dist M (wlift f) _ ⁻¹ ]∎
            subst-all (subst-all M (wlift f)) Fin[ (λ _ → Q) ∣ ext[ h ] ∘ var ] ∎
          fNrc : ∀ h {Q} i → red-cand {h +N n} Q R
                   → red-cand (subst-all (wlift f i) Fin[ (λ _ → Q) ∣ ext[ h ] ∘ var ]) (pr (R ∣ Γ) i)
          fNrc _ fz Qrc = Qrc
          fNrc h (fs i) _ = ((λ x → red-cand x (pr Γ i)) ● subeq-aux-fs h i) (red-cand-ext[ h ] (pf i))
          fnc-aux : ∀ h {Q} → red-cand {h +N n} Q R
                      → ∀ i → red-cand (Fin[ (λ _ → Q) ∣ ext[ h ] ∘ f ] i) (pr (R ∣ Γ) i)
          fnc-aux _ Qrc fz = Qrc
          fnc-aux h _ (fs i) = red-cand-ext[ h ] (pf i)
          fnc : ∀ h {Q} → red-cand {h +N n} Q R
                   → red-cand (subst-all (subst-all M (wlift f)) Fin[ (λ _ → Q) ∣ ext[ h ] ∘ var ]) S
          fnc h {Q} Qrc = ((λ x → red-cand x S) ● subeq h) (red-cand-⊢ Fin[ (λ _ → Q) ∣ ext[ h ] ∘ f ] der (fnc-aux h Qrc))


  -- typable terms are reducibility candidates
  red-cand-⊢ {Γ} {T} {app M N} f (⊢-app {_} {S} der₁ der₂) pf =
    red-cand-⊢ f der₁ pf zero (red-cand-⊢ f der₂ pf)

  ⊢-is-red-cand : ∀ {Γ M T} → Γ ⊢ M ∶ T → red-cand M T
  ⊢-is-red-cand {Γ} {M} {T} der =
    ((λ x → red-cand x T) ● subst-all-var M)
            (red-cand-⊢ var der (λ i → red-cand-var i (pr Γ i)))


  -- typable terms are stron normalising
  ⊢-is-strnrm : ∀ {Γ M T} → Γ ⊢ M ∶ T → isStrNrm M
  ⊢-is-strnrm {_} {M} {T} der = red-cand-strnrm M T (⊢-is-red-cand der)


-- end file
