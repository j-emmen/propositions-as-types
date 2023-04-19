
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

  varty : ∀ Γ i → Γ ∋ i ∶ lst-pr Γ i
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
  ⊢-app-prem : ∀ {Γ S M N} → Γ ⊢ app M N ∶ S → Σ Ty (λ x → Γ ⊢ M ∶ x ⇒ S × Γ ⊢ N ∶ x)
  ⊢-app-prem (⊢-app {T = T} der₁ der₂) = T ,, (der₁ , der₂)
  ⊢-app-premₜ : ∀ {Γ S M N} → Γ ⊢ app M N ∶ S → Ty
  ⊢-app-premₜ der = pj1 (⊢-app-prem der)
  ⊢-app-premₗ : ∀ {Γ S M N} → (der : Γ ⊢ app M N ∶ S) → Γ ⊢ M ∶ (⊢-app-premₜ der) ⇒ S
  ⊢-app-premₗ der = prj1 (pj2 (⊢-app-prem der))
  ⊢-app-premᵣ : ∀ {Γ S M N} → (der : Γ ⊢ app M N ∶ S) → Γ ⊢ N ∶ (⊢-app-premₜ der)
  ⊢-app-premᵣ der = prj2 (pj2 (⊢-app-prem der))

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


  -- projections that forget all or just the first variable
  infix 10 _◃_∶_
  data _◃_∶_ : (Γ Γ' : Ctx) → (Fin (len Γ) → Fin (len Γ')) → Set where
    π'-! : ∀ {Γ' p} → [] ◃ Γ' ∶ p
    π'-frg : ∀ {Γ p} R → (∀ i → fs i == p i) → Γ ◃ R ∣ Γ ∶ p

  π-id : ∀ {Γ} → Γ ◂ Γ ∶ id
  π-id {[]} = π-∅
  π-id {R ∣ Γ} = π-cnc R =rf (λ _ → =rf) π-id

  ◃to◂ : ∀ {Γ Γ' p} → Γ ◃ Γ' ∶ p → Γ ◂ Γ' ∶ p
  ◃to◂ {Γ' = []} π'-! = π-∅
  ◃to◂ {Γ' = R ∣ Γ'} π'-! = π-frg {p = N₀ind} R N₀ind (◃to◂ π'-!)
  ◃to◂ (π'-frg R eq) = π-frg R eq π-id

  π-rfl : ∀ {Γ p} → (∀ i → i == p i) → Γ ◂ Γ ∶ p
  π-rfl {[]} eqp = π-∅
  π-rfl {R ∣ Γ} eqp = π-cnc R (eqp fz) (λ i → eqp (fs i)) π-id

  π'-dsp : ∀ {Γ R} → Γ ◃ R ∣ Γ ∶ fs
  π'-dsp {Γ} {R} = π'-frg R (λ _ → =rf)

  -- these two terms below could be derived from ◃to◂
  π-dsp : ∀ {Γ R} → Γ ◂ R ∣ Γ ∶ fs
  π-dsp {Γ} {R} = π-frg R (λ _ → =rf) π-id

  π-! : ∀ {Γ} p → [] ◂ Γ ∶ p
  π-! {[]} p = π-∅
  π-! {R ∣ Γ} p = π-frg {p = N₀ind} R N₀ind (π-! {Γ} _)

  -- projections are closed under composition
  -- (does not seem to be needed, perhaps because we work pointwise)
  π-cmp : ∀ {Γ Δ Θ p q r} → q ∘ p == r
             → Γ ◂ Δ ∶ p → Δ ◂ Θ ∶ q → Γ ◂ Θ ∶ r
  π-cmp eq π-∅ πq = π-! _
  π-cmp eq (π-frg R eqs πp) πq = {!!}
  π-cmp eq (π-cnc R eqz eqs πp) πq = {!!}
  π-cmp eq (π-swp R S eqz eqsz eqss πp) πq = {!!}

  -- projections forget variables
  π-≤ : ∀ {Γ' Γ p} → Γ' ◂ Γ ∶ p → len Γ' ≤N len Γ
  π-≤ π-∅                              = 0₁
  π-≤  {Γ'} {R ∣ Γ} (π-frg R eq πp)     = suc-≤ (len Γ') (len Γ) (π-≤ πp)
  π-≤ (π-cnc R eqz eqs πp)             = π-≤ πp
  π-≤ (π-swp R S eqz eqsz eqss πp)     = π-≤ πp

  -- indeed, the underlying function of a projection is injective (!)
  π-inj : ∀ {Γ' Γ p} → Γ' ◂ Γ ∶ p → ∀ {i j} → p i == p j → i == j
  π-inj (π-frg R eqs πp) {i} {j} eq =
    π-inj πp (fs-inj (eqs i • eq • eqs j ⁻¹))
  -- π-cnc, first term in eq is  p fz = fz
  π-inj (π-cnc R eqz eqs πp) {fz} {fz} eq =
    =rf
  π-inj (π-cnc R eqz eqs πp) {fz} {fs j} eq =
    N₀ind (PA4-Fin (eqz • eq • eqs j ⁻¹))
  -- all other variables
  π-inj (π-cnc R eqz eqs πp) {fs i} {fz} eq =
    N₀ind (PA4-Fin (eqz • eq ⁻¹ • eqs i ⁻¹))
  π-inj (π-cnc R eqz eqs πp) {fs i} {fs j} eq =
    =ap fs (π-inj πp (fs-inj (eqs i • eq • eqs j ⁻¹)))
  -- π-swp, first term in eq is  p fz = fs fz
  -- here and below, the second are p fz, p (fs fz) = fz, p (fs (fs j))
  π-inj (π-swp R S eqz eqsz eqss πp) {fz} {fz} eq =
    =rf
  π-inj (π-swp R S eqz eqsz eqss πp) {fz} {fs fz} eq =
    N₀ind (PA4-Fin (eqsz • eq ⁻¹ • eqz ⁻¹))
  π-inj (π-swp R S eqz eqsz eqss πp) {fz} {fs (fs j)} eq =
    N₀ind (PA4-Fin (fs-inj (eqz • eq • eqss j ⁻¹)))
  -- first term in eq is  p (fs fz) = fz
  π-inj (π-swp R S eqz eqsz eqss πp) {fs fz} {fz} eq =
    N₀ind (PA4-Fin (eqsz • eq • eqz ⁻¹))
  π-inj (π-swp R S eqz eqsz eqss πp) {fs fz} {fs fz} eq =
    =rf
  π-inj (π-swp R S eqz eqsz eqss πp) {fs fz} {fs (fs j)} eq =
    N₀ind (PA4-Fin (eqsz • eq • eqss j ⁻¹))
  -- all other variables
  π-inj (π-swp R S eqz eqsz eqss πp) {fs (fs i)} {fz} eq =
    N₀ind (PA4-Fin (fs-inj (eqz • eq ⁻¹ • eqss i ⁻¹)))
  π-inj (π-swp R S eqz eqsz eqss πp) {fs (fs i)} {fs fz} eq =
    N₀ind (PA4-Fin (eqsz • eq ⁻¹ • eqss i ⁻¹))
  π-inj (π-swp R S eqz eqsz eqss πp) {fs (fs i)} {fs (fs j)} eq =
    =ap fs (=ap fs ((π-inj πp (fs-inj (fs-inj (eqss i • eq • eqss j ⁻¹))))))


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
  -- between Γ' ≡ Γ ∶ p and (len Γ == len Γ') × (Γ' ◂ Γ ∶ p)

  ≡∶-= : ∀ {Γ Γ' f f'} → (∀ i → f i == f' i) → Γ' ≡ Γ ∶ f → Γ' ≡ Γ ∶ f'
  ≡∶-= eqf ∅ = ∅
  ≡∶-= eqf (≡∶cnc P eqz eqs bij) = ≡∶cnc P (eqz • eqf fz) (λ i → eqs i • eqf (fs i)) bij
  ≡∶-= {f = f} {f'} eqf (≡∶swp {f = g} P Q eqsz eqz eqss bij) =
    ≡∶swp P Q (fs fz                  ==[ eqsz • eqf fz ]              f' fz         )
              (fz                     ==[ eqz • eqf (fs fz) ]          f' (fs fz)    )
              (λ i → fs (fs (g i))   ==[ eqss i • eqf (fs (fs i)) ]   f' (fs (fs i)))
              bij

  ∋v∶-= : ∀ {Γ T x x'} → x == x' → Γ ∋ x ∶ T → Γ ∋ x' ∶ T
  ∋v∶-= {Γ} {T} = =transp (λ x → Γ ∋ x ∶ T)

  -- if T occurs in the i-th position in Γ' and Γ' ≡ Γ ∶ f,
  -- then T occurs in the (f i)-th position in Γ
  -- (this could also be proven from π-∋∶)
  ≡∶-∋∶ : ∀ {Γ Γ' f T} → Γ' ≡ Γ ∶ f → ∀ {i} → Γ' ∋ i ∶ T → Γ ∋ (f i) ∶ T
  ≡∶-∋∶ (≡∶cnc R eqz eqs bij) here =
    ∋v∶-= eqz here
  ≡∶-∋∶ (≡∶cnc R eqz eqs bij) {fs i} (there inc) =
    ∋v∶-= (eqs i) (there (≡∶-∋∶ bij inc))
  ≡∶-∋∶ (≡∶swp R S eqz eqsz eqss bij) here =
    ∋v∶-= eqz (there here)
  ≡∶-∋∶ (≡∶swp R S eqz eqsz eqss bij) (there here) =
    ∋v∶-= eqsz here
  ≡∶-∋∶ (≡∶swp R S eqz eqsz eqss bij) {fs (fs i)} (there (there inc)) =
    ∋v∶-= (eqss i) (there (there (≡∶-∋∶ bij inc)))

  -- the order of premises in a derivation does not matter,
  -- up to renaming the variables accordingly
  ≡∶-congr-⊢ : ∀ {Γ Γ' f M T} → Γ' ≡ Γ ∶ f
                → Γ' ⊢ M ∶ T → Γ ⊢ rename M f ∶ T
  ≡∶-congr-⊢ bij (⊢-var inc) = ⊢-var (≡∶-∋∶ bij inc)
  ≡∶-congr-⊢ bij (⊢-abs {T = T} der) = ⊢-abs (≡∶-congr-⊢ (≡∶cnc T =rf (λ _ → =rf) bij) der)
  ≡∶-congr-⊢ bij (⊢-app der₁ der₂) = ⊢-app (≡∶-congr-⊢ bij der₁) (≡∶-congr-⊢ bij der₂)

  -- some useful properties of derivations
  ⊢∶-= : ∀ {Γ T M M'} → M == M' → Γ ⊢ M ∶ T → Γ ⊢ M' ∶ T
  ⊢∶-= {Γ} {T} = =transp (λ x → Γ ⊢ x ∶ T)
  ⊢v∶-∋∶ : ∀ {Γ T i} → Γ ⊢ var i ∶ T → Γ ∋ i ∶ T
  ⊢v∶-∋∶ (⊢-var inc) = inc
  ⊢∶-∋∶ : ∀ {Γ T M} → Γ ⊢ M ∶ T → ∀ {i} → M == var i → Γ ∋ i ∶ T
  ⊢∶-∋∶ (⊢-var inc) eq = ⊢v∶-∋∶ (⊢∶-= eq (⊢-var inc))

  -- three useful properties of projections
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
  π-∋∶ : ∀ {Γ Γ' p} → Γ' ◂ Γ ∶ p → ∀ {i T} → Γ' ∋ i ∶ T → Γ ∋ (p i) ∶ T
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


  π-∋∶-inv : ∀ {Γ Γ' p} → (∀ {i j} → p i == p j → i == j)
               → (∀ {i T} → Γ' ∋ i ∶ T → Γ ∋ (p i) ∶ T) → Γ' ◂ Γ ∶ p
  π-∋∶-inv {[]} {[]} inj pf =
    π-∅
  π-∋∶-inv {R ∣ Γ} {[]} inj pf =
    π-frg {p = N₀ind} R N₀ind
          (π-∋∶-inv (λ {i} {j} _ → N₀ind {λ _ → i == j} i)
                    (λ {x} {_} → N₀ind {λ _ → ([] ∋ x ∶ _ → Γ ∋ N₀ind x ∶ _)} x))
  π-∋∶-inv {[]} {R' ∣ Γ'} {p} inj pf =
    N₀ind {λ _ → R' ∣ Γ' ◂ [] ∶ p} (p fz)
  π-∋∶-inv {R ∣ Γ} {R' ∣ Γ'} {p} inj pf = {!π-∋∶-inv ? pf'!}
    where pf' : ∀ {i T} → Γ' ∋ i ∶ T → R ∣ Γ ∋ (p (fs i)) ∶ T
          pf' inc = pf (there inc)
          -- need to define p' : Fin (len Γ') → Fin (suc (len Γ'))
          -- s.t. p' i = p (fs i)
          p₀ : Fin (len Γ') → Fin (len Γ)
          p₀ i = {!p (fs i)!}


  -- weakening is admissible
  wkn-π : ∀ {Γ Γ' p M T} → Γ' ◂ Γ ∶ p → Γ' ⊢ M ∶ T → Γ ⊢ rename M p ∶ T
  wkn-π πp (⊢-var inc) = ⊢-var (π-∋∶ πp inc)
  wkn-π πp (⊢-abs {T = T} der) = ⊢-abs (wkn-π (π-cnc T =rf (λ _ → =rf) πp) der)
  wkn-π πp (⊢-app der₁ der₂) = ⊢-app (wkn-π πp der₁) (wkn-π πp der₂)

  wkn-0 : ∀ {Γ M T} R → Γ ⊢ M ∶ T → R ∣ Γ ⊢ (ext M) ∶ T
  wkn-0 R der = wkn-π π-dsp der


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
  σ-∋∶ : ∀ {Γ Γ' s T} → Γ ← Γ' ∶ s → ∀ {i} → Γ ∋ i ∶ T → Γ' ⊢ s i ∶ T
  σ-∋∶ (σ-trm eqz eqs σs der) here = ⊢∶-= eqz  der
  σ-∋∶ (σ-trm eqz eqs σs der) {fs i} (there inc) = ⊢∶-= (eqs i) (σ-∋∶ σs inc)

  σ-∋∶' : ∀ {Γ Γ' s} → Γ ← Γ' ∶ s → ∀ i → Γ' ⊢ s i ∶ lst-pr Γ i
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

  -- projections are substitutions
  ◂to← : ∀ {Γ Γ' p s} → (∀ i → var (p i) == s i) → Γ ◂ Γ' ∶ p → Γ ← Γ' ∶ s
  ◂to← eq π-∅ =
    σ-!
  ◂to← eq (π-frg R eqs πp) =
    σ-frg R (λ i → =ap var (eqs i) • eq i) (◂to← (λ _ → =rf) πp)
  ◂to← {s = s} eq (π-cnc {p = p} {p'} R eqz eqs πp) =
    σ-wlift R (wlift-var-fn (=ap var eqz • eq fz) (λ i → =ap var (eqs i) • eq (fs i)))
            (◂to← (λ _ → =rf) πp)
  ◂to← eq (π-swp {p = p} {p'} R S eqz eqsz eqss πp) =
    σ-trm (=ap var eqz • eq fz) (λ _ → =rf)
          (σ-wlift R (wlift-var-fn (=ap var eqsz • eq (fs fz))
                                   (λ i → =ap var (eqss i) • eq (fs (fs i))))
                     (σ-frg S (λ _ → =rf)
                     (◂to← (λ _ → =rf) πp)))
          (⊢-var (there here))


  σ-id : ∀ {Γ} → Γ ← Γ ∶ var
  σ-id {Γ} = ◂to← (λ i → =rf) π-id

  σ-rfl : ∀ {Γ s} → (∀ i → var i == s i) → Γ ← Γ ∶ s
  σ-rfl {Γ} eq = ◂to← eq (π-rfl (λ _ → =rf))

  ←∶v-∋∶ : ∀ {Γ Γ' s} → Γ ← Γ' ∶ s → ∀ {i j} → s i == var j → Γ' ∋ j ∶ lst-pr Γ i
  ←∶v-∋∶ σs {i} eq = ⊢∶-∋∶ (σ-∋∶' σs i) eq


  ←to◂ : ∀ {Γ Γ' p s} → (∀ {i j} → p i == p j → i == j)
           → (∀ i → var (p i) == s i) → Γ ← Γ' ∶ s → Γ ◂ Γ' ∶ p
  ←to◂ inj eq σ-! = π-! _
  ←to◂ {R ∣ Γ} {Γ'} {p} inj eq (σ-trm {s = s} {s'} eqz eqs σs der) = π-∋∶-inv inj aux
    where aux : {i : Fin (suc (len Γ))} {T : Ty} → R ∣ Γ ∋ i ∶ T → Γ' ∋ p i ∶ T
          aux {fz} {T} here = ⊢∶-∋∶ der (eqz • eq fz ⁻¹)
          aux {fs i} {T} (there inc) = ⊢∶-∋∶ (σ-∋∶ σs inc) (eqs i • eq (fs i) ⁻¹)

  -- the substitution var ∘ pr₁₁ where (pr₁₁ : 0₂, 1₂ ⊢> 0₁), should NOT be a projection
  pr₁₁ : Fin two → Fin one
  pr₁₁ i = fz
  σdiag : ∀ {T s} → (∀ i → var fz == s i) → (T ∣ T ∣ []) ← (T ∣ []) ∶ s
  σdiag {T} {s} eqv = σ-trm (eqv fz) aux σ-id (⊢-var here)
    where aux : (i : Fin one) → var i == s (fs i)
          aux fz = eqv (fs fz)
  σdiag-π : ∀ {T} → (T ∣ T ∣ []) ◂ (T ∣ []) ∶ pr₁₁
  σdiag-π = ←to◂ {!!} (λ _ → =rf) (σdiag λ _ → =rf)

  -- term sections are substitutions
  σ-trmsect : ∀ {Γ T M} → Γ ⊢ M ∶ T → T ∣ Γ ← Γ ∶ trmsect M
  σ-trmsect der = σ-trm =rf (λ _ → =rf) σ-id der


  -- substitution is admissible
  σ-subst-all : ∀ {Γ Γ' s T M} → Γ ← Γ' ∶ s → Γ ⊢ M ∶ T → Γ' ⊢ subst-all M s ∶ T
  σ-subst-all σs (⊢-var inc) = σ-∋∶ σs inc
  σ-subst-all σs (⊢-abs der) = ⊢-abs (σ-subst-all (σ-wlift _ (λ _ → =rf) σs) der)
  σ-subst-all σs (⊢-app der₁ der₂) = ⊢-app (σ-subst-all σs der₁) (σ-subst-all σs der₂)

  σ-subst-0 : ∀ {Γ R T M N} → Γ ⊢ N ∶ R → R ∣ Γ ⊢ M ∶ T → Γ ⊢ subst-0 M N ∶ T
  σ-subst-0 der₁ der₂ = σ-subst-all (σ-trmsect der₁) der₂


  ---------------------
  -- subject reduction
  ---------------------
  subj-red : ∀ {Γ T M N} → Γ ⊢ M ∶ T → M ⟶ N → Γ ⊢ N ∶ T
  subj-red {M = app (lam M) N} {.(subst-all M (trmsect N))} der (β M N) =
    σ-subst-0 (⊢-app-premᵣ der) (⊢-abs-prem (⊢-app-premₗ der))
  subj-red {M = lam M} {lam N} (⊢-abs der) (βlam stp) =
    ⊢-abs (subj-red der stp)
  subj-red {M = app M L} {app N L} (⊢-app der₁ der₂) (βappₗ stp) =
    ⊢-app (subj-red der₁ stp) der₂
  subj-red {M = app L M} {app L N} (⊢-app der₁ der₂) (βappᵣ stp) =
    ⊢-app der₁ (subj-red der₂ stp)


  -- lam M is a canonical form
  lam-is-canf : ∀ {Γ T S M} → Γ ⊢ M ∶ T ⇒ S → is-value M
                  → Σ (Trm (suc (len Γ))) (λ x → lam x == M)
  lam-is-canf der (val-lam {M'} nrm') = M' ,, =rf


  -- progress
  progr : ∀ {T M} → [] ⊢ M ∶ T → is-normal M → is-value M
  progr (⊢-abs der) nrm = val-lam (nrm-lam nrm)
  progr {T} (⊢-app {M = M} {N} der₁ der₂) nrm = N₀ind (nrm (subst-0 M' N) stp')
    where nrmM : is-normal M
          nrmM = nrm-appₗ nrm
          M' : Trm one
          M' = pj1 (lam-is-canf der₁ (progr der₁ nrmM))
          λ=M : lam M' == M
          λ=M = pj2 (lam-is-canf der₁ (progr der₁ nrmM))
          stp' : app M N ⟶ subst-0 M' N
          stp' = =transp (λ x → app x N ⟶ subst-0 M' N) λ=M (β M' N)
          

-- end file
