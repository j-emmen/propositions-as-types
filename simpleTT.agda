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
  {-π-cnc : ∀ {Γ' Γ p p'} R → fz == p' fz → (∀ i → fs (p i) == p' (fs i))
                → Γ' ◂ Γ ∶ p → (R ∣ Γ') ◂ (R ∣ Γ) ∶ p'
  π-cnc R eqz eqs πp =
    π-ext {R ∣ _} {R ∣ _} (liftFin-ptw eqz eqs) (π-cnc-rf R πp)
  π-swp : ∀ {Γ' Γ p p'} R S → (p (fs fz) == p' fz) → (p fz == p' (fs fz))
             → (∀ i → p (fs (fs i)) == p' (fs (fs i)))
                   → R ∣ S ∣ Γ' ◂ Γ ∶ p → S ∣ R ∣ Γ' ◂ Γ ∶ p'
  π-swp {p = p} R S eqz eqsz eqss πp =
    π-ext {S ∣ R ∣ _} (swapFin-pcmp {f = p} eqz eqsz eqss) (π-swp-rf R S πp)-}

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


{-
  -- inductive attempt
  infix 10 _◂ᵢ_∶_
  data _◂ᵢ_∶_ : (Γ' Γ : Ctx) → (Fin (len Γ') → Fin (len Γ)) → Set where
    πᵢ-∅ : ∀ {p} → [] ◂ᵢ [] ∶ p
    πᵢ-frg : ∀ {Γ' Γ p p'} R → (∀ i → fs (p i) == p' i)
               → Γ' ◂ᵢ Γ ∶ p → Γ' ◂ᵢ R ∣ Γ ∶ p'
               -- might need to turn this into a destructor
    πᵢ-cnc : ∀ {Γ' Γ p p'} R → fz == p' fz → (∀ i → fs (p i) == p' (fs i))
               → Γ' ◂ᵢ Γ ∶ p → (R ∣ Γ') ◂ᵢ (R ∣ Γ) ∶ p'
    πᵢ-swp : ∀ {Γ' Γ p p'} R S → (p (fs fz) == p' fz) → (p fz == p' (fs fz))
                  → (∀ i → p (fs (fs i)) == p' (fs (fs i)))
                    → R ∣ S ∣ Γ' ◂ᵢ Γ ∶ p → S ∣ R ∣ Γ' ◂ᵢ Γ ∶ p'

  πᵢ-id : ∀ {Γ} → Γ ◂ᵢ Γ ∶ id
  πᵢ-id {[]} = πᵢ-∅
  πᵢ-id {R ∣ Γ} = πᵢ-cnc R =rf (λ _ → =rf) πᵢ-id
  πᵢ-rfl : ∀ {Γ p} → (∀ i → i == p i) → Γ ◂ᵢ Γ ∶ p
  πᵢ-rfl {[]} eqp = πᵢ-∅
  πᵢ-rfl {R ∣ Γ} eqp = πᵢ-cnc R (eqp fz) (λ i → eqp (fs i)) πᵢ-id
  πᵢ-! : ∀ {Γ} p → [] ◂ᵢ Γ ∶ p
  πᵢ-! {[]} p = πᵢ-∅
  πᵢ-! {R ∣ Γ} p = πᵢ-frg {p = N₀ind} R N₀ind (πᵢ-! {Γ} _)
  πᵢ-dsp : ∀ {Γ R} → Γ ◂ᵢ R ∣ Γ ∶ fs
  πᵢ-dsp {Γ} {R} = πᵢ-frg R (λ _ → =rf) πᵢ-id
  πᵢ-frg-rf : ∀ {Γ' Γ p} R → Γ' ◂ᵢ Γ ∶ p → Γ' ◂ᵢ R ∣ Γ ∶ (fs ∘ p)
  πᵢ-frg-rf R = πᵢ-frg R (λ _ → =rf)
  πᵢ-cnc-rf : ∀ {Γ' Γ p } R → Γ' ◂ᵢ Γ ∶ p → (R ∣ Γ') ◂ᵢ (R ∣ Γ) ∶ (liftFin p)
  πᵢ-cnc-rf R = πᵢ-cnc R =rf (λ _ → =rf)
  πᵢ-swp-rf : ∀ {Γ' Γ p } R S → R ∣ S ∣ Γ' ◂ᵢ Γ ∶ p → S ∣ R ∣ Γ' ◂ᵢ Γ ∶ (p ∘ swapFin id)
  πᵢ-swp-rf R S = πᵢ-swp R S =rf =rf (λ _ → =rf)
  πᵢ-swp-lft : ∀ {Γ' Γ p p'} R S → (fs fz == p' fz) → (fz == p' (fs fz))
                  → (∀ i → fs (fs (p i)) == p' (fs (fs i)))
                    → Γ' ◂ᵢ Γ ∶ p → R ∣ S ∣ Γ' ◂ᵢ S ∣ R ∣ Γ ∶ p'
  πᵢ-swp-lft {Γ'} {Γ} {p} {p'} R S eqz eqsz eqss πᵢp = 
    πᵢ-swp {Γ = S ∣ R ∣ Γ} S R eqz eqsz eqss (πᵢ-cnc-rf S (πᵢ-cnc-rf R πᵢp))
  πᵢ-swp-lft-rf : ∀ {Γ' Γ p} R S → Γ' ◂ᵢ Γ ∶ p → R ∣ S ∣ Γ' ◂ᵢ S ∣ R ∣ Γ ∶ (swapFin p)
  πᵢ-swp-lft-rf R S = πᵢ-swp-lft R S =rf =rf (λ _ → =rf)

  -- inductive projections forget variables
  πᵢ-≤ : ∀ {Γ' Γ p} → Γ' ◂ᵢ Γ ∶ p → len Γ' ≤N len Γ
  πᵢ-≤ πᵢ-∅                              = 0₁
  πᵢ-≤ {Γ'} {R ∣ Γ} (πᵢ-frg R _ πp)       = ≤+N' {len Γ'} {len Γ} (πᵢ-≤ πp) one
  πᵢ-≤ (πᵢ-cnc R _ _ πp)                 = πᵢ-≤ πp
  πᵢ-≤ (πᵢ-swp R S _ _ _ πp)             = πᵢ-≤ πp

  -- indeed the underlying function of an inductive projection is injective
  πᵢ-inj : ∀ {Γ' Γ p} → Γ' ◂ᵢ Γ ∶ p → ∀ {i j} → p i == p j → i == j
  πᵢ-inj {p = p} (πᵢ-frg {p = p₀} R eqp₀ πp₀) {i} {j} eq =
    πᵢ-inj πp₀ (fs-inj (eqp₀ i • eq • eqp₀ j ⁻¹))
  πᵢ-inj {p = p} (πᵢ-cnc {p = p₀} R eqzp₀ eqsp₀ πp₀) {fz} {fz} eq =
    =rf
  πᵢ-inj {p = p} (πᵢ-cnc {p = p₀} R eqzp₀ eqsp₀ πp₀) {fz} {fs j} eq =
    N₀ind (PA4-Fin (=proof fz           ==[ eqzp₀ ] /
                           p fz         ==[ eq ] /
                           p (fs j)     ==[ eqsp₀ j ⁻¹ ]∎
                           fs (p₀ j) ∎))
  πᵢ-inj {p = p} (πᵢ-cnc {p = p₀} R eqzp₀ eqsp₀ πp₀) {fs i} {fz} eq =
    N₀ind (PA4-Fin (=proof fz           ==[ eqzp₀ ] /
                           p fz         ==[ eq ⁻¹ ] /
                           p (fs i)     ==[ eqsp₀ i ⁻¹ ]∎
                           fs (p₀ i) ∎))
  πᵢ-inj {p = p} (πᵢ-cnc {p = p₀} R eqzp₀ eqsp₀ πp₀) {fs i} {fs j} eq =
    =ap fs (πᵢ-inj πp₀ (fs-inj (eqsp₀ i • eq • eqsp₀ j ⁻¹)))
  πᵢ-inj {p = p} (πᵢ-swp {p = p₀} R S eqzp₀ eqszp₀ eqssp₀ πp₀) {fz} {fz} eq =
    =rf
  πᵢ-inj {p = p} (πᵢ-swp {p = p₀} R S eqzp₀ eqszp₀ eqssp₀ πp₀) {fz} {fs fz} eq =
    πᵢ-inj πp₀ (=proof p₀ fz ==[ eqszp₀ ] /
                      p (fs fz) ==[ eq ⁻¹ ] /
                      p fz  ==[ eqzp₀ ⁻¹ ]∎
                      p₀ (fs fz) ∎)
  πᵢ-inj {p = p} (πᵢ-swp {p = p₀} R S eqzp₀ eqszp₀ eqssp₀ πp₀) {fz} {fs (fs j)} eq =
     N₀ind (PA4-Fin (fs-inj (πᵢ-inj πp₀ (=proof p₀ (fs fz)          ==[ eqzp₀ ] /
                                               p fz                ==[ eq ] /
                                               p (fs (fs j))       ==[ eqssp₀ j ⁻¹ ]∎
                                               p₀ (fs (fs j)) ∎))))
  πᵢ-inj {p = p} (πᵢ-swp {p = p₀} R S eqzp₀ eqszp₀ eqssp₀ πp₀) {fs fz} {fz} eq =
    πᵢ-inj πp₀ (=proof p₀ (fs fz)   ==[ eqzp₀ ] /
                      p fz         ==[ eq ⁻¹ ] /
                      p (fs fz)    ==[ eqszp₀ ⁻¹ ]∎
                      p₀ fz ∎)
  πᵢ-inj {p = p} (πᵢ-swp {p = p₀} R S eqzp₀ eqszp₀ eqssp₀ πp₀) {fs (fs i)} {fz} eq =
    N₀ind (PA4-Fin (fs-inj (πᵢ-inj πp₀ (=proof p₀ (fs fz)          ==[ eqzp₀ ] /
                                              p fz                ==[ eq ⁻¹ ] /
                                              p (fs (fs i))       ==[ eqssp₀ i ⁻¹ ]∎
                                              p₀ (fs (fs i)) ∎))))
  πᵢ-inj {p = p} (πᵢ-swp {p = p₀} R S eqzp₀ eqszp₀ eqssp₀ πp₀) {fs fz} {fs fz} eq =
    =rf
  πᵢ-inj {p = p} (πᵢ-swp {p = p₀} R S eqzp₀ eqszp₀ eqssp₀ πp₀) {fs fz} {fs (fs j)} eq =
    N₀ind (PA4-Fin (πᵢ-inj πp₀ (=proof p₀ fz          ==[ eqszp₀ ] /
                                      p (fs fz)                ==[ eq ] /
                                      p (fs (fs j))       ==[ eqssp₀ j ⁻¹ ]∎
                                      p₀ (fs (fs j)) ∎)))
  πᵢ-inj {p = p} (πᵢ-swp {p = p₀} R S eqzp₀ eqszp₀ eqssp₀ πp₀) {fs (fs i)} {fs fz} eq =
    N₀ind (PA4-Fin (πᵢ-inj πp₀ (=proof p₀ fz          ==[ eqszp₀ ] /
                                      p (fs fz)                ==[ eq ⁻¹ ] /
                                      p (fs (fs i))       ==[ eqssp₀ i ⁻¹ ]∎
                                      p₀ (fs (fs i)) ∎)))
  πᵢ-inj {p = p} (πᵢ-swp {p = p₀} R S eqzp₀ eqszp₀ eqssp₀ πp₀) {fs (fs i)} {fs (fs j)} eq =
    πᵢ-inj πp₀ (=proof p₀ (fs (fs i))      ==[ eqssp₀ i ] /
                      p (fs (fs i))       ==[ eq ] /
                      p (fs (fs j))       ==[ eqssp₀ j ⁻¹ ]∎
                      p₀ (fs (fs j)) ∎)


  -- inductive version
  data _≡ᵢ_∶_ : (Γ Γ' : Ctx) → (Fin (len Γ) → Fin (len Γ')) → Set where
    ≡ᵢ∶∅ : ∀ {f} → [] ≡ᵢ [] ∶ f
    ≡ᵢ∶cnc : ∀ {Γ Γ' f f'} R → (fz == f' fz) → (∀ i → fs (f i) == f' (fs i))
               → Γ' ≡ᵢ Γ ∶ f → (R ∣ Γ') ≡ᵢ (R ∣ Γ) ∶ f'
    ≡ᵢ∶swp : ∀ {Γ Γ' f f'} R S → (fs fz == f' fz) → (fz == f' (fs fz))
               → (∀ i → fs (fs (f i)) == f' (fs (fs i)))
                 → Γ' ≡ᵢ Γ ∶ f → (S ∣ R ∣ Γ') ≡ᵢ (R ∣ S ∣ Γ) ∶ f'

  ≡ᵢ∶id : ∀ {Γ} → Γ ≡ᵢ Γ ∶ id
  ≡ᵢ∶id {[]} = ≡ᵢ∶∅
  ≡ᵢ∶id {R ∣ Γ} = ≡ᵢ∶cnc R =rf (λ _ → =rf) ≡ᵢ∶id
  ≡ᵢ∶rfl : ∀ {Γ f} → (∀ i → i == f i) → Γ ≡ᵢ Γ ∶ f
  ≡ᵢ∶rfl {[]} eqf = ≡ᵢ∶∅
  ≡ᵢ∶rfl {R ∣ Γ} eqf = ≡ᵢ∶cnc R (eqf fz) (λ i → eqf (fs i)) ≡ᵢ∶id
  ≡ᵢ∶cnc-rf : ∀ {Γ Γ' f} R → Γ' ≡ᵢ Γ ∶ f → (R ∣ Γ') ≡ᵢ (R ∣ Γ) ∶ (liftFin f)
  ≡ᵢ∶cnc-rf {Γ'} {Γ} {f} R = ≡ᵢ∶cnc R =rf (λ _ → =rf)
  ≡ᵢ∶swp-rf : ∀ {Γ Γ' f} R S → Γ' ≡ᵢ Γ ∶ f → (S ∣ R ∣ Γ') ≡ᵢ (R ∣ S ∣ Γ) ∶ (swapFin f)
  ≡ᵢ∶swp-rf {Γ'} {Γ} {f} R S = ≡ᵢ∶swp R S =rf =rf (λ _ → =rf)
  ≡ᵢ∶-= : ∀ {Γ Γ' f f'} → (∀ i → f i == f' i) → Γ' ≡ᵢ Γ ∶ f → Γ' ≡ᵢ Γ ∶ f'
  ≡ᵢ∶-= eqf ≡ᵢ∶∅ = ≡ᵢ∶∅
  ≡ᵢ∶-= eqf (≡ᵢ∶cnc P eqz eqs bij) = ≡ᵢ∶cnc P (eqz • eqf fz) (λ i → eqs i • eqf (fs i)) bij
  ≡ᵢ∶-= {f = f} {f'} eqf (≡ᵢ∶swp {f = g} P Q eqsz eqz eqss bij) =
    ≡ᵢ∶swp P Q (fs fz                  ==[ eqsz • eqf fz ]              f' fz         )
              (fz                     ==[ eqz • eqf (fs fz) ]          f' (fs fz)    )
              (λ i → fs (fs (g i))   ==[ eqss i • eqf (fs (fs i)) ]   f' (fs (fs i)))
              bij


  -- the following three probably provide an equivalence
  -- between `Γ' ≡ᵢ Γ ∶ f` and `len Γ' == len Γ`
  ≡ᵢ∶-same-len : ∀ {Γ Γ' f} → Γ' ≡ᵢ Γ ∶ f → len Γ' == len Γ
  ≡ᵢ∶-same-len {[]} {[]} {f} ∅ =
    =rf
  ≡ᵢ∶-same-len {(R ∣ Γ')} {(R ∣ Γ)} {f} (≡ᵢ∶cnc R eqz eqs bij) =
    =ap suc (≡ᵢ∶-same-len bij)
  ≡ᵢ∶-same-len {(R ∣ S ∣ Γ')} {(S ∣ R ∣ Γ)} {f} (≡ᵢ∶swp R S eqz eqsz eqss bij) =
    =ap (suc ∘ suc) (≡ᵢ∶-same-len bij)

  -- the bijections are the projections between contexts of the same length
  ≡ᵢ∶to◂∶ : ∀ {Γ Γ' f} → Γ' ≡ᵢ Γ ∶ f → Γ' ◂ Γ ∶ f
  ≡ᵢ∶to◂∶ ≡ᵢ∶∅ =
    π-∅
  ≡ᵢ∶to◂∶ (≡ᵢ∶cnc R eqz eqs bij) =
    π-cnc R eqz eqs (≡ᵢ∶to◂∶ bij)
  ≡ᵢ∶to◂∶ {R ∣ S ∣ Γ} {S ∣ R ∣ Γ'} (≡ᵢ∶swp {f = f} {f'} R S eqz eqsz eqss bij) =
    π-swp {Γ = R ∣ S ∣ Γ} {p = liftFin (liftFin f)} R S eqz eqsz eqss
          (π-cnc {S ∣ Γ'} {S ∣ Γ} R =rf (λ _ → =rf)
                 (π-cnc S =rf (λ _ → =rf) (≡ᵢ∶to◂∶ bij)))

  ◂∶to≡ᵢ∶ : ∀ {Γ Γ' p} → len Γ == len Γ' → Γ' ◂ Γ ∶ p → Γ' ≡ᵢ Γ ∶ p
  ◂∶to≡ᵢ∶ {[]} {[]} {p} eq πp = ≡ᵢ∶∅
  ◂∶to≡ᵢ∶ {R ∣ Γ} {S ∣ Γ'} {p} eq πp = {!◂∶to≡ᵢ∶ {p = p'} leneq !}
    where leneq : len Γ == len Γ'
          leneq = suc-inj eq
          p' : Fin (len Γ') → Fin (len Γ)
          p' = faceFin-restr (p ∘ fs) (p fz) (λ _ ps=pz → PA4-Fin (prj1 πp ps=pz ⁻¹))

{-
  ◂∶to≡ᵢ∶ eq π-∅ =
    ∅
  ◂∶to≡ᵢ∶ eq (π-frg {Γ'} {Γ} R eqp πp) =
    N₀ind (suc-non-decr (len Γ) (=transp (λ x → x ≤N len Γ) (eq ⁻¹) (π-≤ πp)))
  ◂∶to≡ᵢ∶ eq (π-cnc R eqz eqs πp) =
    ≡ᵢ∶cnc R eqz eqs (◂∶to≡ᵢ∶ (suc-inj eq) πp)
  ◂∶to≡ᵢ∶ eq (π-swp R S eqz eqsz eqss πp) =
    {!!} -- might use composition of projections?
    -- ≡ᵢ∶swp R S eqz eqsz eqss (◂∶to≡ᵢ∶ (suc-inj (suc-inj eq)) πp)
  -- these two probably form an equivalence of types
  -- between Γ' ≡ᵢ Γ ∶ p and (len Γ == len Γ') × (Γ' ◂ Γ ∶ p)
-}

  ≡ᵢ∶-cmp : ∀ {Γ Δ Θ f g h} → (∀ i → g (f i) == h i)
             → Γ ≡ᵢ Δ ∶ f → Δ ≡ᵢ Θ ∶ g → Γ ≡ᵢ Θ ∶ h
  ≡ᵢ∶-cmp {[]} {[]} {Θ} {f} {g} {h} tr ∅ qvg =
    ≡ᵢ∶-= N₀ind qvg
  ≡ᵢ∶-cmp {R ∣ Γ} {R ∣ Δ} {R ∣ Θ} {f} {g} {h} tr
         (≡ᵢ∶cnc {f = f₀} R eqzf₀ eqsf₀ qvf₀) (≡ᵢ∶cnc {f = g₀} R eqzg₀ eqsg₀ qvg₀) =
    ≡ᵢ∶cnc R
          (=proof fz           ==[ eqzg₀ ] /
                  g fz         ==[ =ap g eqzf₀ ] /
                  g (f fz)     ==[ tr fz ]∎
                  h fz ∎)
          (λ i → =proof fs (g₀ (f₀ i))       ==[ eqsg₀ (f₀ i) ] /
                         g (fs (f₀ i))        ==[ =ap g (eqsf₀ i) ] /
                         g (f (fs i))         ==[ tr (fs i) ]∎
                         h (fs i) ∎)
          (≡ᵢ∶-cmp (λ _ → =rf) qvf₀ qvg₀)
  ≡ᵢ∶-cmp {R ∣ Γ} {R ∣ S ∣ Δ} {S ∣ R ∣ Θ} {f} {g} {h} tr
         (≡ᵢ∶cnc {f = f₀} R eqzf₀ eqsf₀ qvf₀) (≡ᵢ∶swp {f = g₀} S R eqzg₀ eqszg₀ eqssg₀ qvg₀) =
    {!!}
  ≡ᵢ∶-cmp {S ∣ R ∣ Γ} {R ∣ S ∣ Δ} {R ∣ Θ} {f} {g} {h} tr
         (≡ᵢ∶swp R S eqzf₀ eqszf₀ eqssf₀ qvf₀) (≡ᵢ∶cnc R eqzg₀ eqsg₀ qvg) =
    {!!}
  ≡ᵢ∶-cmp {S ∣ R ∣ Γ} {R ∣ S ∣ Δ} {S ∣ R ∣ Θ} {f} {g} {h} tr
         (≡ᵢ∶swp R S eqzf₀ eqszf₀ eqssf₀ qvf₀) (≡ᵢ∶swp S R eqzg₀ eqszg₀ eqssg₀ qvg) =
    {!!}


  ∋v∶-= : ∀ {Γ T x x'} → x == x' → Γ ∋ x ∶ T → Γ ∋ x' ∶ T
  ∋v∶-= {Γ} {T} = =transp (λ x → Γ ∋ x ∶ T)

  -- if T occurs in the i-th position in Γ' and Γ' ≡ᵢ Γ ∶ f,
  -- then T occurs in the (f i)-th position in Γ
  -- (this could also be proven from π-∋∶)
  ≡ᵢ∶-∋∶ : ∀ {Γ Γ' f T} → Γ' ≡ᵢ Γ ∶ f → ∀ {i} → Γ' ∋ i ∶ T → Γ ∋ (f i) ∶ T
  ≡ᵢ∶-∋∶ (≡ᵢ∶cnc R eqz eqs bij) here =
    ∋v∶-= eqz here
  ≡ᵢ∶-∋∶ (≡ᵢ∶cnc R eqz eqs bij) {fs i} (there inc) =
    ∋v∶-= (eqs i) (there (≡ᵢ∶-∋∶ bij inc))
  ≡ᵢ∶-∋∶ (≡ᵢ∶swp R S eqz eqsz eqss bij) here =
    ∋v∶-= eqz (there here)
  ≡ᵢ∶-∋∶ (≡ᵢ∶swp R S eqz eqsz eqss bij) (there here) =
    ∋v∶-= eqsz here
  ≡ᵢ∶-∋∶ (≡ᵢ∶swp R S eqz eqsz eqss bij) {fs (fs i)} (there (there inc)) =
    ∋v∶-= (eqss i) (there (there (≡ᵢ∶-∋∶ bij inc)))


  -- the order of premises in a derivation does not matter,
  -- up to renaming the variables accordingly
  ≡ᵢ∶-congr-⊢ : ∀ {Γ Γ' f M T} → Γ' ≡ᵢ Γ ∶ f
                → Γ' ⊢ M ∶ T → Γ ⊢ rename M f ∶ T
  ≡ᵢ∶-congr-⊢ bij (⊢-var inc) = ⊢-var (≡ᵢ∶-∋∶ bij inc)
  ≡ᵢ∶-congr-⊢ bij (⊢-abs {T = T} der) = ⊢-abs (≡ᵢ∶-congr-⊢ (≡ᵢ∶cnc T =rf (λ _ → =rf) bij) der)
  ≡ᵢ∶-congr-⊢ bij (⊢-app der₁ der₂) = ⊢-app (≡ᵢ∶-congr-⊢ bij der₁) (≡ᵢ∶-congr-⊢ bij der₂)

  -- if a type occurs in a context, WLOG it occurs in the first position
  ≡ᵢ∶-occur : ∀ {Γ T i} → Γ ∋ i ∶ T
               → Σ[ Ctx ] (λ x →
                   Σ[ (Fin (suc (len x)) → Fin (len Γ)) ] ((T ∣ x) ≡ᵢ Γ ∶_))
  ≡ᵢ∶-occur {T ∣ Γ} {T} {fz} here =
    Γ
    ,, (id
    ,, ≡ᵢ∶id)
  ≡ᵢ∶-occur {R ∣ Γ} {T} {fs i} (there pf) =
    (R ∣ pj1 (≡ᵢ∶-occur pf))
    ,, ( (liftFin (pj1 (pj2 (≡ᵢ∶-occur pf))) ∘ swapFin id)
    ,, {!≡ᵢ∶cnc-rf R (pj2 (pj2 (≡ᵢ∶-occur pf)))!} )


  -- three useful properties of projections
  π-= : ∀ {Γ Γ' p p'} → (∀ i → p i == p' i) → Γ' ◂ Γ ∶ p → Γ' ◂ Γ ∶ p'
  π-= eqp πp = (λ {i} {j} eq → prj1 πp (eqp i • eq • eqp j ⁻¹)) , {!!}

  -- if T occurs in the i-th position in Γ' and Γ' ◂ Γ ∶ f,
  -- then T occurs in the (f i)-th position in Γ
  π-∋∶ : ∀ {Γ Γ' p} → Γ' ◂ Γ ∶ p → ∀ {i T} → Γ' ∋ i ∶ T → Γ ∋ (p i) ∶ T
  π-∋∶ {Γ} {Γ'} {p} πp {i} {T} inc = {!!}

{-
(π-frg R eq πp) here =
    ∋v∶-= (eq fz) (there (π-∋∶ πp here)) 
  π-∋∶ (π-frg R eq πp) {i} (there inc) =
    ∋v∶-= (eq i) (there (π-∋∶ πp (there inc)))
  π-∋∶ (π-cnc R eqz eqs πp) here =
    ∋v∶-= eqz here
  π-∋∶ (π-cnc R eqz eqs πp) {fs i} (there inc) =
    ∋v∶-= (eqs i) (there (π-∋∶ πp inc))
  π-∋∶ (π-swp R S eqz eqsz eqss πp) here =
    ∋v∶-= eqz (there here)
  π-∋∶ (π-swp R S eqz eqsz eqss πp) (there here) =
    ∋v∶-= eqsz here
  π-∋∶ (π-swp R S eqz eqsz eqss πp) {fs (fs i)} (there (there inc)) =
    ∋v∶-= (eqss i) (there (there (π-∋∶ πp inc)))
-}

  -- used only to prove `←to◂`, which is not used anywhere
  π-∋∶-inv : ∀ {Γ Γ' p} → (∀ {i j} → p i == p j → i == j)
               → (∀ {i T} → Γ' ∋ i ∶ T → Γ ∋ (p i) ∶ T) → Γ' ◂ Γ ∶ p
  π-∋∶-inv = {!!}

-}


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
  -- doing so makes the last two clause light grey
  -- meaning that they do NOT hold definitionally


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

  -- quite useless functions
  rc-atm : ∀ {n M} {a : A} → isStrNrm {n} M → red-cand M (atm a)
  rc-atm nrm = nrm
  rc-⇒ : ∀ {n M T S} → (∀ k {N} → red-cand N T → red-cand (app (ext[ k ] {n} M) N) S)
              → red-cand M (T ⇒ S)
  rc-⇒ rcapp = rcapp
  rc-ind : (C : ∀ {n M T} → red-cand {n} M T → Set)
              → (∀ {n M a} → (nrm : red-cand {n} M (atm a)) → C (rc-atm {a = a} nrm))
              → (∀ {n M T S} → (fnc : red-cand {n} M (T ⇒ S)) → C {T = T ⇒ S} (rc-⇒ fnc))
                → ∀ {n M T} → (rc : red-cand {n} M T) → C rc
  rc-ind C Catm Cfnc {T = atm a} = Catm {a = a}
  rc-ind C Catm Cfnc {T = T ⇒ S} = Cfnc
  rc-rec : (C : Set)
              → (∀ {n M a} → (nrm : red-cand {n} M (atm a)) → C)
              → (∀ {n M T S} → (fnc : red-cand {n} M (T ⇒ S)) → C)
                → ∀ {n M T} → (rc : red-cand {n} M T) → C
  rc-rec C = rc-ind (λ _ → C)


  -- the three main properties of reducibility candidates
  
  red-cand-Props : ∀ {n} → Trm n → Ty → Set
  red-cand-Props M T = (red-cand M T → isStrNrm M)
                       × (red-cand M T → ∀ {N} → M ⟶ N → red-cand N T)
                       × (is-neutral M → (∀ {N} → M ⟶ N → red-cand N T) → red-cand M T)

  red-cand-props : ∀ {n} M T → red-cand-Props {n} M T

  red-cand-props {n} M (atm a) =
      id
    , (λ nrm {N} → strnrm-⟶ {N = N} nrm)
    , λ _ → strnrm-stp-any {n} {M}

  red-cand-props {n} M (T ⇒ S) =
    CR1
    , CR2
    , CR3
    where nrmaux : ∀ {N} → red-cand (app M N) S → isStrNrm (app M N)
          nrmaux {N} = prj1 (red-cand-props (app M N) S)          
          strnrmₗₑᵥ-appvar : ∀ {k} → isStrNrmₗₑᵥ k (app (ext M) (var fz)) → isStrNrmₗₑᵥ k M
          strnrmₗₑᵥ-appvar snw = strnrmₗₑᵥ-ext (strnrmₗₑᵥ-appₗ snw)
          strnrm-appvar : isStrNrm (app (ext M) (var fz)) → isStrNrm M
          strnrm-appvar snw = pj1 snw ,, strnrmₗₑᵥ-appvar (pj2 snw)
          varz-red-cand : ∀ {n} i → red-cand (var {n} i) T
          varz-red-cand i = prj2 (prj2 (red-cand-props (var i) T)) ntr-var (λ s → N₀ind (nrm-var _ s))
          CR1 : (fnc : ∀ k {N} → red-cand N T → red-cand (app (ext[ k ] M) N) S)
                      → isStrNrm M
          CR1 fnc = strnrm-appvar (prj1 (red-cand-props (app (ext M) (var fz)) S)
                                        (fnc one (varz-red-cand fz)))

          CR2 : (fnc : ∀ k {N} → red-cand N T → red-cand (app (ext[ k ] M) N) S)
                     → {M' : Trm n} → M ⟶ M'
                       → ∀ k {N} → red-cand N T → red-cand (app (ext[ k ] M') N) S
          CR2 fnc {M'} stp k {N} rc = prj1 (prj2 (red-cand-props (app (ext[ k ] M) N) S)) (fnc k rc) (βappₗ (⟶-extk k stp))

          -- use the fact that a reduction `app M N ⟶ P` is either `β`, `βappₗ`, or `βappᵣ`,
          -- and it cannot be `β` when `M` is neutral
          Mβapp-inv : ∀ k N → is-invrt (βapp-stp {k +N n} {ext[ k ] M} {N})
          Mβapp-inv k N = eqv-is-invrt (βapp-eqv {k +N n} {ext[ k ] M} {N})
          CR3-auxₗ : is-neutral M → (∀ {M'} → M ⟶ M' → red-cand M' (T ⇒ S))
                      → ∀ k {N} → red-cand N T
                      → (MM : Σ[ Trm (k +N n) ] _⟶_ (ext[ k ] M))
                        → red-cand (app (pj1 MM) N) S
          CR3-auxₗ Mntr fnc k {N} rc MM =
            =transp (λ x → red-cand x S)
                    (=ap (λ x → app x N) (prj1 (pj2 (⟶-extk⁻¹g k  (pj2 MM)))))
                    (fnc (prj2 (pj2 (⟶-extk⁻¹g k  (pj2 MM)))) k rc)
{-
          CR3-auxᵣ : is-neutral M → (∀ {M'} → M ⟶ M' → red-cand M' (T ⇒ S))
                      → ∀ l k {N} → isStrNrmₗₑᵥ l N → red-cand N T
                      → (NN : Σ[ Trm (k +N n) ] (N ⟶_))
                        → red-cand (app (ext[ k ] M) (pj1 NN)) S
          CR3-auxᵣ Mntr fnc zero k (strnrm-nrm Nnrm) Nrc NN =
            N₀ind (Nnrm (pj1 NN) (pj2 NN))
          CR3-auxᵣ Mntr fnc (suc l) k (strnrm-stp Nsns) Nrc NN = {!!}
-}

          CR3-aux : is-neutral M → (∀ {M'} → M ⟶ M' → red-cand M' (T ⇒ S))
                    → ∀ {l} k {N} → isStrNrmₗₑᵥ l N → red-cand N T
                      → ∀ {P} → app (ext[ k ] M) N ⟶ P → red-cand P S
          CR3-aux Mntr fnc {zero} k {N} (strnrm-nrm Nnrm) Nrc {P} stp =
            ((λ x → red-cand x S) ● (=pj1 (prj2 (pj2 (Mβapp-inv k N)) (P ,, stp))))
              (+ind3 (λ x → red-cand (pj1 (βapp-stp x)) S)
                     (λ islam → N₀ind (neutral≠lam (neutral-extk k Mntr) islam))
                     (CR3-auxₗ Mntr fnc k Nrc)
                     (λ NN → N₀ind (Nnrm (pj1 NN) (pj2 NN)))
                     (pj1 (Mβapp-inv k N) (P ,, stp)))
          CR3-aux Mntr fnc {suc l} k {N} (strnrm-stp Nsns) Nrc {P} stp =
            ((λ x → red-cand x S) ● (=pj1 (prj2 (pj2 (Mβapp-inv k N)) (P ,, stp))))
              (+ind3 (λ x → red-cand (pj1 (βapp-stp x)) S)
                     (λ islam → N₀ind (neutral≠lam (neutral-extk k Mntr) islam))
                     (CR3-auxₗ Mntr fnc k Nrc)
                     (λ NN → prj2 (prj2 (red-cand-props (app (ext[ k ] M) (pj1 NN)) S))
                                (ntr-app (neutral-extk k Mntr))
                     -- because of this recursive call...
                                (CR3-aux Mntr fnc {l} k (Nsns (pj2 NN))
                                              (prj1 (prj2 (red-cand-props N T))
                                                 Nrc (pj2 NN))) )
                     -- ...it seems hard to do induction only on the right-hand side
                     (pj1 (Mβapp-inv k N) (P ,, stp)))

          CR3 : is-neutral M
                  → (∀ {M'} (stp : M ⟶ M') → red-cand M' (T ⇒ S))
                    → ∀ k {N} → red-cand N T → red-cand (app (ext[ k ] M) N) S
          CR3 Mntr fnc k {N} Nrc =
            prj2 (prj2 (red-cand-props (app (ext[ k ] M) N) S))
                 (ntr-app (neutral-extk k Mntr))
                 (CR3-aux Mntr fnc k (pj2 (prj1 (red-cand-props N T) Nrc)) Nrc)
  -- end red-cand-props

-- end file
