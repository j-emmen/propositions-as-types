
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


  -- the functions rearranging occurences of types in contexts
  data _≡_∶_ : (Γ' Γ : Ctx) → (Fin (len Γ) → Fin (len Γ')) → Set where
    ∅ : ∀ {f} → [] ≡ [] ∶ f
    ≡∶cnc : ∀ {Γ' Γ f f'} R → (fz == f' fz) → (∀ i → fs (f i) == f' (fs i))
                  → Γ' ≡ Γ ∶ f → (R ∣ Γ') ≡ (R ∣ Γ) ∶ f'
    ≡∶swp : ∀ {Γ' Γ f f'} R S → (fs fz == f' fz) → (fz == f' (fs fz))
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
  
  ∋v∶-= : ∀ {Γ T x x'} → x == x' → Γ ∋ x ∶ T → Γ ∋ x' ∶ T
  ∋v∶-= {Γ} {T} = =transp (λ x → Γ ∋ x ∶ T)

  ⊢∶-= : ∀ {Γ T M M'} → M == M' → Γ ⊢ M ∶ T → Γ ⊢ M' ∶ T
  ⊢∶-= {Γ} {T} = =transp (λ x → Γ ⊢ x ∶ T)

  ≡∶-= : ∀ {Γ Γ' f f'} → (∀ i → f i == f' i) → Γ' ≡ Γ ∶ f → Γ' ≡ Γ ∶ f'
  ≡∶-= eqf ∅ = ∅
  ≡∶-= eqf (≡∶cnc P eqz eqs bij) = ≡∶cnc P (eqz • eqf fz) (λ i → eqs i • eqf (fs i)) bij
  ≡∶-= {f = f} {f'} eqf (≡∶swp {f = g} P Q eqsz eqz eqss bij) =
    ≡∶swp P Q (fs fz                  ==[ eqsz • eqf fz ]              f' fz         )
              (fz                     ==[ eqz • eqf (fs fz) ]          f' (fs fz)    )
              (λ i → fs (fs (g i))   ==[ eqss i • eqf (fs (fs i)) ]   f' (fs (fs i)))
              bij

  -- if T occurs in the i-th position in Γ and Γ' ≡ Γ ∶ f,
  -- then T occurs in the (f i)-th position in Γ'
  -- (this is a sanity check: I don't think we'll need this term)
  ≡∶-∋∶ : ∀ {Γ Γ' f T} → Γ' ≡ Γ ∶ f → ∀ {i} → Γ ∋ i ∶ T → Γ' ∋ (f i) ∶ T
  ≡∶-∋∶ (≡∶cnc P eqz eqs bij) here =
    ∋v∶-= eqz here
  ≡∶-∋∶ (≡∶cnc P eqz eqs bij) {fs i} (there inc) =
    ∋v∶-= (eqs i) (there (≡∶-∋∶ bij inc))
  ≡∶-∋∶ (≡∶swp P Q eqsz eqz eqss bij) here =
    ∋v∶-= eqsz (there here)
  ≡∶-∋∶ (≡∶swp P Q eqsz eqz eqss bij) (there here) =
    ∋v∶-= eqz here
  ≡∶-∋∶ (≡∶swp P Q eqsz eqz eqss bij) {fs (fs i)} (there (there inc)) =
    ∋v∶-= (eqss i) (there (there (≡∶-∋∶ bij inc)))


  -- the order of premises in a derivation does not matter,
  -- up to renaming the variables accordingly
  ≡∶-congr-⊢ : ∀ {Γ Γ' f M T} → Γ' ≡ Γ ∶ f
                → Γ ⊢ M ∶ T → Γ' ⊢ rename M f ∶ T
  ≡∶-congr-⊢ bij (⊢-var inc) = ⊢-var (≡∶-∋∶ bij inc)
  ≡∶-congr-⊢ bij (⊢-abs {T = T} der) = ⊢-abs (≡∶-congr-⊢ (≡∶cnc T =rf (λ _ → =rf) bij) der)
  ≡∶-congr-⊢ bij (⊢-app der₁ der₂) = ⊢-app (≡∶-congr-⊢ bij der₁) (≡∶-congr-⊢ bij der₂)


  -- weakening is admissible
  wkn-0 : ∀ {Γ M T} R → Γ ⊢ M ∶ T → R ∣ Γ ⊢ (ext M) ∶ T
  wkn-0 R (⊢-var inc) = ⊢-var (there inc)
  wkn-0 R (⊢-abs {Γ} {T = T} der) =
    ⊢-abs (⊢∶-= (rename-sq⁻¹ _ {id} {swap-first} {fs} {liftFin fs} liftFinfs=swap-first∘fs)
                (≡∶-congr-⊢ {Γ = R ∣ T ∣ Γ} {T ∣ R ∣ Γ}
                            (≡∶swp {f' = swap-first} R T =rf =rf (λ _ → =rf) ≡∶id)
                            (wkn-0 R der)))
  wkn-0 R (⊢-app der₁ der₂) = ⊢-app (wkn-0 R der₁) (wkn-0 R der₂)


-- end file
