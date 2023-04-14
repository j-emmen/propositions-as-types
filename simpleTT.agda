
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


  -- projections of variables, possibly rearranging occurences of types in contexts
  infix 10 _◂_∶_
  data _◂_∶_ : (Γ' Γ : Ctx) → (Fin (len Γ') → Fin (len Γ)) → Set where
    π-∅ : ∀ {p} → [] ◂ [] ∶ p
    π-frg : ∀ {Γ' Γ p p'} R → (∀ i → fs (p i) == p' i)
               → Γ' ◂ Γ ∶ p → Γ' ◂ R ∣ Γ ∶ p'
    π-cnc : ∀ {Γ' Γ p p'} R → fz == p' fz → (∀ i → fs (p i) == p' (fs i))
               → Γ' ◂ Γ ∶ p → (R ∣ Γ') ◂ (R ∣ Γ) ∶ p'
    π-swp : ∀ {Γ' Γ p p'} R S → (fs fz == p' fz) → (fz == p' (fs fz))
                  → (∀ i → fs (fs (p i)) == p' (fs (fs i)))
                    → Γ' ◂ Γ ∶ p → (S ∣ R ∣ Γ') ◂ (R ∣ S ∣ Γ) ∶ p'


  π-id : ∀ {Γ} → Γ ◂ Γ ∶ id
  π-id {[]} = π-∅
  π-id {R ∣ Γ} = π-cnc R =rf (λ _ → =rf) π-id

  π-dsp : ∀ {Γ R} → Γ ◂ R ∣ Γ ∶ fs
  π-dsp {Γ} {R} = π-frg R (λ _ → =rf) π-id

  π-rfl : ∀ {Γ p} → (∀ i → i == p i) → Γ ◂ Γ ∶ p
  π-rfl {[]} eqp = π-∅
  π-rfl {R ∣ Γ} eqp = π-cnc R (eqp fz) (λ i → eqp (fs i)) π-id

  -- projections forget variables
  π-≤ : ∀ {Γ' Γ p} → Γ' ◂ Γ ∶ p → len Γ' ≤N len Γ
  π-≤ π-∅                              = 0₁
  π-≤  {Γ'} {R ∣ Γ} (π-frg R eq πp)     = suc-≤ (len Γ') (len Γ) (π-≤ πp)
  π-≤ (π-cnc R eqz eqs πp)             = π-≤ πp
  π-≤ (π-swp R S eqz eqsz eqss πp)     = π-≤ πp


  -- only the functions rearranging occurences of types in contexts
  data _≡_∶_ : (Γ Γ' : Ctx) → (Fin (len Γ) → Fin (len Γ')) → Set where
    ∅ : ∀ {f} → [] ≡ [] ∶ f
    ≡∶cnc : ∀ {Γ Γ' f f'} R → (fz == f' fz) → (∀ i → fs (f i) == f' (fs i))
                  → Γ' ≡ Γ ∶ f → (R ∣ Γ') ≡ (R ∣ Γ) ∶ f'
    ≡∶swp : ∀ {Γ Γ' f f'} R S → (fs fz == f' fz) → (fz == f' (fs fz))
                  → (∀ i → fs (fs (f i)) == f' (fs (fs i)))
                    → Γ' ≡ Γ ∶ f → (S ∣ R ∣ Γ') ≡ (R ∣ S ∣ Γ) ∶ f'

  ≡∶id : ∀ {Γ} → Γ ≡ Γ ∶ id
  ≡∶id {[]} = ∅
  ≡∶id {R ∣ Γ} = ≡∶cnc R =rf (λ _ → =rf) ≡∶id

  ≡∶rfl : ∀ {Γ f} → (∀ i → i == f i) → Γ ≡ Γ ∶ f
  ≡∶rfl {[]} eqf = ∅
  ≡∶rfl {R ∣ Γ} eqf = ≡∶cnc R (eqf fz) (λ i → eqf (fs i)) ≡∶id

  swap-first : ∀ {n} → Fin (suc (suc n)) → Fin (suc (suc n))
  swap-first fz = fs fz
  swap-first (fs fz) = fz
  swap-first (fs (fs i)) = fs (fs i)

  -- the restriction of swap-first to Fin (suc n) via fs is liftFin fs
  -- (i.e. the inclusion of Fin (suc n) which misses fs fz)
  liftFinfs=swap-first∘fs : ∀ {n} → (i : Fin (suc n)) → liftFin {n} fs i == swap-first (fs i)
  liftFinfs=swap-first∘fs fz = =rf
  liftFinfs=swap-first∘fs (fs i) = =rf

  -- the bijections are the projections between contexts of the same length
  ≡∶to◂∶ : ∀ {Γ Γ' f} → Γ' ≡ Γ ∶ f → Γ' ◂ Γ ∶ f
  ≡∶to◂∶ ∅ = π-∅
  ≡∶to◂∶ (≡∶cnc R eqz eqs bij) = π-cnc R eqz eqs (≡∶to◂∶ bij)
  ≡∶to◂∶ (≡∶swp R S eqz eqsz eqss bij) = π-swp R S eqz eqsz eqss (≡∶to◂∶ bij)

  ◂∶to≡∶ : ∀ {Γ Γ' p} → len Γ == len Γ' → Γ' ◂ Γ ∶ p → Γ' ≡ Γ ∶ p
  ◂∶to≡∶ eq π-∅ = ∅
  ◂∶to≡∶ eq (π-frg {Γ'} {Γ} R eqp πp) = N₀ind (suc-non-decr (len Γ) (=transp (λ x → x ≤N len Γ) (eq ⁻¹) (π-≤ πp)))
  ◂∶to≡∶ eq (π-cnc R eqz eqs πp) = ≡∶cnc R eqz eqs (◂∶to≡∶ (suc-inj eq) πp)
  ◂∶to≡∶ eq (π-swp R S eqz eqsz eqss πp) = ≡∶swp R S eqz eqsz eqss (◂∶to≡∶ (suc-inj (suc-inj eq)) πp)
  -- these two probably form an equivalence of types

  ∋v∶-= : ∀ {Γ T x x'} → x == x' → Γ ∋ x ∶ T → Γ ∋ x' ∶ T
  ∋v∶-= {Γ} {T} = =transp (λ x → Γ ∋ x ∶ T)

  ⊢∶-= : ∀ {Γ T M M'} → M == M' → Γ ⊢ M ∶ T → Γ ⊢ M' ∶ T
  ⊢∶-= {Γ} {T} = =transp (λ x → Γ ⊢ x ∶ T)

  π-= : ∀ {Γ Γ' p p'} → (∀ i → p i == p' i) → Γ' ◂ Γ ∶ p → Γ' ◂ Γ ∶ p'
  π-= eqp π-∅ = π-∅
  π-= eqp (π-frg R eq πp) = π-frg R (λ i → eq i • eqp i) πp
  π-= eqp (π-cnc R eqz eqs πp) = π-cnc R (eqz • eqp fz) (λ i → eqs i • eqp (fs i)) πp
  π-= eqp (π-swp R S eqz eqsz eqss πp) = π-swp R S (eqz • eqp fz)
                                                   (eqsz • eqp (fs fz))
                                                   (λ i → eqss i • eqp (fs (fs i)))
                                                   πp

  -- if T occurs in the i-th position in Γ' and Γ' ◂ Γ ∶ f,
  -- then T occurs in the (f i)-th position in Γ
  π-∋∶ : ∀ {Γ Γ' p T} → Γ' ◂ Γ ∶ p → ∀ {i} → Γ' ∋ i ∶ T → Γ ∋ (p i) ∶ T
  π-∋∶ (π-frg R eq πp) here =
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

  ≡∶-= : ∀ {Γ Γ' f f'} → (∀ i → f i == f' i) → Γ' ≡ Γ ∶ f → Γ' ≡ Γ ∶ f'
  ≡∶-= eqf ∅ = ∅
  ≡∶-= eqf (≡∶cnc P eqz eqs bij) = ≡∶cnc P (eqz • eqf fz) (λ i → eqs i • eqf (fs i)) bij
  ≡∶-= {f = f} {f'} eqf (≡∶swp {f = g} P Q eqsz eqz eqss bij) =
    ≡∶swp P Q (fs fz                  ==[ eqsz • eqf fz ]              f' fz         )
              (fz                     ==[ eqz • eqf (fs fz) ]          f' (fs fz)    )
              (λ i → fs (fs (g i))   ==[ eqss i • eqf (fs (fs i)) ]   f' (fs (fs i)))
              bij

  -- if T occurs in the i-th position in Γ' and Γ' ≡ Γ ∶ f,
  -- then T occurs in the (f i)-th position in Γ
  ≡∶-∋∶ : ∀ {Γ Γ' f T} → Γ' ≡ Γ ∶ f → ∀ {i} → Γ' ∋ i ∶ T → Γ ∋ (f i) ∶ T
  ≡∶-∋∶ (≡∶cnc P eqz eqs bij) here =
    ∋v∶-= eqz here
  ≡∶-∋∶ (≡∶cnc P eqz eqs bij) {fs i} (there inc) =
    ∋v∶-= (eqs i) (there (≡∶-∋∶ bij inc))
  ≡∶-∋∶ (≡∶swp P Q eqz eqsz eqss bij) here =
    ∋v∶-= eqz (there here)
  ≡∶-∋∶ (≡∶swp P Q eqz eqsz eqss bij) (there here) =
    ∋v∶-= eqsz here
  ≡∶-∋∶ (≡∶swp P Q eqz eqsz eqss bij) {fs (fs i)} (there (there inc)) =
    ∋v∶-= (eqss i) (there (there (≡∶-∋∶ bij inc)))

  -- the order of premises in a derivation does not matter,
  -- up to renaming the variables accordingly
  ≡∶-congr-⊢ : ∀ {Γ Γ' f M T} → Γ' ≡ Γ ∶ f
                → Γ' ⊢ M ∶ T → Γ ⊢ rename M f ∶ T
  ≡∶-congr-⊢ bij (⊢-var inc) = ⊢-var (≡∶-∋∶ bij inc)
  ≡∶-congr-⊢ bij (⊢-abs {T = T} der) = ⊢-abs (≡∶-congr-⊢ (≡∶cnc T =rf (λ _ → =rf) bij) der)
  ≡∶-congr-⊢ bij (⊢-app der₁ der₂) = ⊢-app (≡∶-congr-⊢ bij der₁) (≡∶-congr-⊢ bij der₂)


  -- weakening is admissible
  wkn-π : ∀ {Γ Γ' p M T} → Γ' ◂ Γ ∶ p → Γ' ⊢ M ∶ T → Γ ⊢ rename M p ∶ T
  wkn-π πp (⊢-var inc) = ⊢-var (π-∋∶ πp inc)
  wkn-π πp (⊢-abs {T = T} der) = ⊢-abs (wkn-π (π-cnc T =rf (λ _ → =rf) πp) der)
  wkn-π πp (⊢-app der₁ der₂) = ⊢-app (wkn-π πp der₁) (wkn-π πp der₂)

  wkn-0 : ∀ {Γ M T} R → Γ ⊢ M ∶ T → R ∣ Γ ⊢ (ext M) ∶ T
  wkn-0 R der = wkn-π π-dsp der


  -- typed substitutions
  infix 10 _←_∶_
  data _←_∶_ : (Γ Γ' : Ctx) → (Fin (len Γ) → Trm (len Γ')) → Set where
    σ-! : ∀ {Γ' s} → [] ← Γ' ∶ s
    σ-trm : ∀ {Γ Γ' s s' A M} → (M == s' fz) → (∀ i → s i == s' (fs i))
                 → Γ ← Γ' ∶ s → Γ' ⊢ M ∶ A → A ∣ Γ ← Γ' ∶ s'
  
  -- if T occurs in the i-th position in Γ' and Γ' ◂ Γ ∶ f,
  -- then the term s i has type T
  σ-∋∶ : ∀ {Γ Γ' s T} → Γ ← Γ' ∶ s → ∀ {i} → Γ ∋ i ∶ T → Γ' ⊢ s i ∶ T
  σ-∋∶ (σ-trm eqz eqs σs der) here = ⊢∶-= eqz  der
  σ-∋∶ (σ-trm eqz eqs σs der) {fs i} (there inc) = ⊢∶-= (eqs i) (σ-∋∶ σs inc)

  -- substitutions have lengths
  σ-len : ∀ {Γ Γ' s} → Γ ← Γ' ∶ s → Nat
  σ-len σ-! = zero
  σ-len (σ-trm _ _ σs _) = suc (σ-len σs)

  -- extensions of substitution are admissible
  σ-frg : ∀ {Γ Γ' s} T → Γ ← Γ' ∶ s → Γ ← T ∣ Γ' ∶ (ext ∘ s)
  σ-frg T σ-! =
    σ-!
  σ-frg T (σ-trm {s = s} {s'} eqz eqs σs der) =
    σ-trm (=ap ext eqz) (λ i → =ap ext (eqs i)) (σ-frg T σs) (wkn-0 T der)
  
  σ-wlift : ∀ {Γ Γ' s} T → Γ ← Γ' ∶ s → T ∣ Γ ← T ∣ Γ' ∶ wlift s
  σ-wlift T σ-! = σ-trm =rf (λ _ → =rf) σ-! (⊢-var here)
  σ-wlift T (σ-trm {s = s} {s'} eqz eqs σs der) =
    σ-trm =rf (λ _ → =rf) (σ-trm (=ap ext eqz) (λ i → =ap ext (eqs i))
                                  (σ-frg T σs) (wkn-0 T der))
              (⊢-var here)

  -- substitution is admissible
  subst-σ : ∀ {Γ Γ' s A M} → Γ ← Γ' ∶ s → Γ ⊢ M ∶ A → Γ' ⊢ subst-all M s ∶ A
  subst-σ σs (⊢-var inc) = σ-∋∶ σs inc
  subst-σ σs (⊢-abs der) = ⊢-abs (subst-σ (σ-wlift _ σs) der)
  subst-σ σs (⊢-app der₁ der₂) = ⊢-app (subst-σ σs der₁) (subst-σ σs der₂)

-- end file
