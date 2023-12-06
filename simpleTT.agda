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

  -- projections of variables, which are the injective functions
  infix 10 _◂_∶_
  _◂_∶_ :  (Γ' Γ : Ctx) → (Fin (len Γ') → Fin (len Γ)) → Set
  Γ' ◂ Γ ∶ p = ∀ {i j} → p i == p j → i == j

  π-id : ∀ {Γ p} → (∀ i → p i == i) → Γ ◂ Γ ∶ p
  π-id isid {i} {j} e = isid i ⁻¹ • e • isid j 
  π-∅ : ∀ {p} → [] ◂ [] ∶ p
  π-∅ {p} = π-id N₀ind
  π-! : ∀ {Γ} p → [] ◂ Γ ∶ p
  π-! {Γ} p {i} {j} _ = N₀ind {i ==_} j
  π-dsp : ∀ {Γ} R → Γ ◂ R ∣ Γ ∶ fs
  π-dsp R = fs-inj
  π-cmp-rf : ∀ {Γ Δ Θ p q} → Γ ◂ Δ ∶ p → Δ ◂ Θ ∶ q → Γ ◂ Θ ∶ (q ∘ p)
  π-cmp-rf πp πq e = πp (πq e)
  ◂∶-= : ∀ {Γ' Γ p p'} → (∀ i → p i == p' i) → Γ' ◂ Γ ∶ p → Γ' ◂ Γ ∶ p'
  ◂∶-= eqp πp {i} {j} e = πp (eqp i • e • eqp j ⁻¹)
  π-frg-rf : ∀ {Γ' Γ p} R → R ∣ Γ' ◂ Γ ∶ p → Γ' ◂ Γ ∶ (p ∘ fs)
  π-frg-rf R πp e = fs-inj (πp e) 
  π-cnc-rf : ∀ {Γ' Γ p } R → Γ' ◂ Γ ∶ p → (R ∣ Γ') ◂ (R ∣ Γ) ∶ (liftFin p)
  π-cnc-rf R πp {i} {j} e = liftFin-inj πp e
  π-swp-rf : ∀ {Γ' Γ p } R S → R ∣ S ∣ Γ' ◂ Γ ∶ p → S ∣ R ∣ Γ' ◂ Γ ∶ (p ∘ swapFin id)
  π-swp-rf R S πp {i} {j} e = swapFin-inj id (πp e)
  π-cmp : ∀ {Γ Δ Θ p q r} → (∀ i → q (p i) == r i)
             → Γ ◂ Δ ∶ p → Δ ◂ Θ ∶ q → Γ ◂ Θ ∶ r
  π-cmp tr πp πq = ◂∶-= tr (π-cmp-rf πp πq)
  π-frg : ∀ {Γ' Γ p p'} R → (∀ i → p (fs i) == p' i)
             → R ∣ Γ' ◂ Γ ∶ p → Γ' ◂ Γ ∶ p'
  π-frg R eq πp =
    ◂∶-= eq (π-frg-rf R πp)
  π-cnc : ∀ {Γ' Γ p p'} R → fz == p' fz → (∀ i → fs (p i) == p' (fs i))
                → Γ' ◂ Γ ∶ p → (R ∣ Γ') ◂ (R ∣ Γ) ∶ p'
  π-cnc R eqz eqs πp =
    ◂∶-= {R ∣ _} {R ∣ _} (liftFin-ptw eqz eqs) (π-cnc-rf R πp)
  π-swp : ∀ {Γ' Γ p p'} R S → (p (fs fz) == p' fz) → (p fz == p' (fs fz))
             → (∀ i → p (fs (fs i)) == p' (fs (fs i)))
                   → R ∣ S ∣ Γ' ◂ Γ ∶ p → S ∣ R ∣ Γ' ◂ Γ ∶ p'
  π-swp {p = p} R S eqz eqsz eqss πp =
    ◂∶-= {S ∣ R ∣ _} (swapFin-pcmp {f = p} eqz eqsz eqss) (π-swp-rf R S πp)


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


  -- projections forget variables

  π-≤ : ∀ {Γ' Γ p} → Γ' ◂ Γ ∶ p → len Γ' ≤N len Γ
  π-≤ {[]} {Γ} πp =
    0₁
  π-≤ {R ∣ Γ'} {[]} {p} πp =
    p fz
  π-≤ {R ∣ Γ'} {S ∣ Γ} {p} πp =
    Fin-finj-≤ {f = faceFin-restr (p ∘ fs) (p fz) λ _ ps=pz → PA4-Fin (πp ps=pz ⁻¹)}
               (faceFin-restr-inj {f = p ∘ fs} {p fz} (λ _ ps=pz → PA4-Fin (πp ps=pz ⁻¹))
                                  (injective-cmp fs-inj πp))
  

  -- only the functions rearranging occurences of types in contexts
  -- in order not to use function extensionality,
  -- constructors are formulated invariant under pointwise equality
  data _≡_∶_ : (Γ Γ' : Ctx) → (Fin (len Γ) → Fin (len Γ')) → Set where
    ≡∶∅ : ∀ {f} → [] ≡ [] ∶ f
    ≡∶cnc : ∀ {Γ Γ' f f'} R → (fz == f' fz) → (∀ i → fs (f i) == f' (fs i))
               → Γ' ≡ Γ ∶ f → (R ∣ Γ') ≡ (R ∣ Γ) ∶ f'
    ≡∶swp : ∀ {Γ Γ' f f'} R S → (fs fz == f' fz) → (fz == f' (fs fz))
               → (∀ i → fs (fs (f i)) == f' (fs (fs i)))
                 → Γ' ≡ Γ ∶ f → (S ∣ R ∣ Γ') ≡ (R ∣ S ∣ Γ) ∶ f'

  -- what about defining them as the bijections??

  ≡∶id : ∀ {Γ} → Γ ≡ Γ ∶ id
  ≡∶id {[]} = ≡∶∅
  ≡∶id {R ∣ Γ} = ≡∶cnc R =rf (λ _ → =rf) ≡∶id
  ≡∶rfl : ∀ {Γ f} → (∀ i → i == f i) → Γ ≡ Γ ∶ f
  ≡∶rfl {[]} eqf = ≡∶∅
  ≡∶rfl {R ∣ Γ} eqf = ≡∶cnc R (eqf fz) (λ i → eqf (fs i)) ≡∶id
  ≡∶cnc-rf : ∀ {Γ Γ' f} R → Γ' ≡ Γ ∶ f → (R ∣ Γ') ≡ (R ∣ Γ) ∶ (liftFin f)
  ≡∶cnc-rf {Γ'} {Γ} {f} R = ≡∶cnc R =rf (λ _ → =rf)
  ≡∶swp-rf : ∀ {Γ Γ' f} R S → Γ' ≡ Γ ∶ f → (S ∣ R ∣ Γ') ≡ (R ∣ S ∣ Γ) ∶ (swapFin f)
  ≡∶swp-rf {Γ'} {Γ} {f} R S = ≡∶swp R S =rf =rf (λ _ → =rf)
  ≡∶-= : ∀ {Γ Γ' f f'} → (∀ i → f i == f' i) → Γ' ≡ Γ ∶ f → Γ' ≡ Γ ∶ f'
  ≡∶-= eqf ≡∶∅ = ≡∶∅
  ≡∶-= eqf (≡∶cnc P eqz eqs bij) = ≡∶cnc P (eqz • eqf fz) (λ i → eqs i • eqf (fs i)) bij
  ≡∶-= {f = f} {f'} eqf (≡∶swp {f = g} P Q eqsz eqz eqss bij) =
    ≡∶swp P Q (fs fz                  ==[ eqsz • eqf fz ]              f' fz         )
              (fz                     ==[ eqz • eqf (fs fz) ]          f' (fs fz)    )
              (λ i → fs (fs (g i))   ==[ eqss i • eqf (fs (fs i)) ]   f' (fs (fs i)))
              bij

  -- the following three probably provide an equivalence
  -- between `Γ' ≡ Γ ∶ f` and `len Γ' == len Γ`
  ≡∶-same-len : ∀ {Γ Γ' f} → Γ' ≡ Γ ∶ f → len Γ' == len Γ
  ≡∶-same-len {[]} {[]} {f} ∅ =
    =rf
  ≡∶-same-len {(R ∣ Γ')} {(R ∣ Γ)} {f} (≡∶cnc R eqz eqs bij) =
    =ap suc (≡∶-same-len bij)
  ≡∶-same-len {(R ∣ S ∣ Γ')} {(S ∣ R ∣ Γ)} {f} (≡∶swp R S eqz eqsz eqss bij) =
    =ap (suc ∘ suc) (≡∶-same-len bij)

  -- the bijections are the projections between contexts of the same length
  ≡∶to◂∶ : ∀ {Γ Γ' f} → Γ' ≡ Γ ∶ f → Γ' ◂ Γ ∶ f
  ≡∶to◂∶ ≡∶∅ =
    π-∅
  ≡∶to◂∶ (≡∶cnc R eqz eqs bij) =
    π-cnc R eqz eqs (≡∶to◂∶ bij)
  ≡∶to◂∶ {R ∣ S ∣ Γ} {S ∣ R ∣ Γ'} (≡∶swp {f = f} {f'} R S eqz eqsz eqss bij) =
    π-swp {Γ = R ∣ S ∣ Γ} {p = liftFin (liftFin f)} R S eqz eqsz eqss
          (π-cnc {S ∣ Γ'} {S ∣ Γ} R =rf (λ _ → =rf)
                 (π-cnc S =rf (λ _ → =rf) (≡∶to◂∶ bij)))

  ◂∶to≡∶ : ∀ {Γ Γ' p} → len Γ == len Γ' → Γ' ◂ Γ ∶ p → Γ' ≡ Γ ∶ p
  ◂∶to≡∶ {[]} {[]} {p} eq πp = ≡∶∅
  ◂∶to≡∶ {R ∣ Γ} {S ∣ Γ'} {p} eq πp = {!◂∶to≡∶ {p = p'} leneq !}
    where leneq : len Γ == len Γ'
          leneq = suc-inj eq
          p' : Fin (len Γ') → Fin (len Γ)
          p' = faceFin-restr (p ∘ fs) (p fz) (λ _ ps=pz → PA4-Fin (πp ps=pz ⁻¹))

{-
  ◂∶to≡∶ eq π-∅ =
    ∅
  ◂∶to≡∶ eq (π-frg {Γ'} {Γ} R eqp πp) =
    N₀ind (suc-non-decr (len Γ) (=transp (λ x → x ≤N len Γ) (eq ⁻¹) (π-≤ πp)))
  ◂∶to≡∶ eq (π-cnc R eqz eqs πp) =
    ≡∶cnc R eqz eqs (◂∶to≡∶ (suc-inj eq) πp)
  ◂∶to≡∶ eq (π-swp R S eqz eqsz eqss πp) =
    {!!} -- might use composition of projections?
    -- ≡∶swp R S eqz eqsz eqss (◂∶to≡∶ (suc-inj (suc-inj eq)) πp)
  -- these two probably form an equivalence of types
  -- between Γ' ≡ Γ ∶ p and (len Γ == len Γ') × (Γ' ◂ Γ ∶ p)
-}

  ≡∶-cmp : ∀ {Γ Δ Θ f g h} → (∀ i → g (f i) == h i)
             → Γ ≡ Δ ∶ f → Δ ≡ Θ ∶ g → Γ ≡ Θ ∶ h
  ≡∶-cmp {[]} {[]} {Θ} {f} {g} {h} tr ∅ qvg =
    ≡∶-= N₀ind qvg
  ≡∶-cmp {R ∣ Γ} {R ∣ Δ} {R ∣ Θ} {f} {g} {h} tr
         (≡∶cnc {f = f₀} R eqzf₀ eqsf₀ qvf₀) (≡∶cnc {f = g₀} R eqzg₀ eqsg₀ qvg₀) =
    ≡∶cnc R
          (=proof fz           ==[ eqzg₀ ] /
                  g fz         ==[ =ap g eqzf₀ ] /
                  g (f fz)     ==[ tr fz ]∎
                  h fz ∎)
          (λ i → =proof fs (g₀ (f₀ i))       ==[ eqsg₀ (f₀ i) ] /
                         g (fs (f₀ i))        ==[ =ap g (eqsf₀ i) ] /
                         g (f (fs i))         ==[ tr (fs i) ]∎
                         h (fs i) ∎)
          (≡∶-cmp (λ _ → =rf) qvf₀ qvg₀)
  ≡∶-cmp {R ∣ Γ} {R ∣ S ∣ Δ} {S ∣ R ∣ Θ} {f} {g} {h} tr
         (≡∶cnc {f = f₀} R eqzf₀ eqsf₀ qvf₀) (≡∶swp {f = g₀} S R eqzg₀ eqszg₀ eqssg₀ qvg₀) =
    {!!}
  ≡∶-cmp {S ∣ R ∣ Γ} {R ∣ S ∣ Δ} {R ∣ Θ} {f} {g} {h} tr
         (≡∶swp R S eqzf₀ eqszf₀ eqssf₀ qvf₀) (≡∶cnc R eqzg₀ eqsg₀ qvg) =
    {!!}
  ≡∶-cmp {S ∣ R ∣ Γ} {R ∣ S ∣ Δ} {S ∣ R ∣ Θ} {f} {g} {h} tr
         (≡∶swp R S eqzf₀ eqszf₀ eqssf₀ qvf₀) (≡∶swp S R eqzg₀ eqszg₀ eqssg₀ qvg) =
    {!!}


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

  -- if a type occurs in a context, WLOG it occurs in the first position
  ≡∶-occur : ∀ {Γ T i} → Γ ∋ i ∶ T
               → Σ[ Ctx ] (λ x →
                   Σ[ (Fin (suc (len x)) → Fin (len Γ)) ] ((T ∣ x) ≡ Γ ∶_))
  ≡∶-occur {T ∣ Γ} {T} {fz} here =
    Γ
    ,, (id
    ,, ≡∶id)
  ≡∶-occur {R ∣ Γ} {T} {fs i} (there pf) =
    (R ∣ pj1 (≡∶-occur pf))
    ,, ( (liftFin (pj1 (pj2 (≡∶-occur pf))) ∘ swapFin id)
    ,, {!≡∶cnc-rf R (pj2 (pj2 (≡∶-occur pf)))!} )

  -- three useful properties of projections
  π-= : ∀ {Γ Γ' p p'} → (∀ i → p i == p' i) → Γ' ◂ Γ ∶ p → Γ' ◂ Γ ∶ p'
  π-= eqp πp {i} {j} eq = πp (eqp i • eq • eqp j ⁻¹)

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

{-
{[]} {[]} inj pf =
    π-∅
  π-∋∶-inv {R ∣ Γ} {[]} inj pf =
    π-frg {p = N₀ind} R N₀ind
          (π-∋∶-inv (λ {i} {j} _ → N₀ind {λ _ → i == j} i)
                    (λ {x} {_} → N₀ind {λ _ → ([] ∋ x ∶ _ → Γ ∋ N₀ind x ∶ _)} x))
  π-∋∶-inv {[]} {R' ∣ Γ'} {p} inj pf =
    N₀ind {λ _ → R' ∣ Γ' ◂ [] ∶ p} (p fz)
  π-∋∶-inv {R ∣ Γ} {R' ∣ Γ'} {p} inj pf = {!!}
    where -- note that `p fz` is an occurrence of `R'` in `R ∣ Γ` by `pf`, that is
          Θ : Ctx
          Θ = pj1 (≡∶-occur (pf here))
          f : Fin (suc (len Θ)) → Fin (suc (len Γ))
          f = pj1 (pj2 (≡∶-occur (pf here)))
          fbij : (R' ∣ Θ) ≡ (R ∣ Γ) ∶ f
          fbij = pj2 (pj2 (≡∶-occur (pf here)))
          lΘ : len Θ == len Γ
          lΘ = suc-inj (≡∶-same-len fbij)
          -- then `p (fs i)` is in `Θ` for every `i`, that is
          p₀ : Fin (len Γ') → Fin (len Θ)
          p₀ = {!!}
          eq₀ : ∀ {i} → fs (Fin-=to→ lΘ (p₀ i)) == p (fs i)
          eq₀ = {!!}
          pp₀ : Γ' ◂ Θ ∶ p₀
          pp₀ = {!!}
-}


  ---------------------------
  -- weakening is admissible
  ---------------------------
  
  wkn-π : ∀ {Γ Γ' p M T} → Γ' ◂ Γ ∶ p → Γ' ⊢ M ∶ T → Γ ⊢ rename M p ∶ T
  wkn-π πp (⊢-var inc) = ⊢-var (π-∋∶ πp inc)
  wkn-π πp (⊢-abs {T = T} der) = ⊢-abs (wkn-π (π-cnc T =rf (λ _ → =rf) πp) der)
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
  σ-∋∶ : ∀ {Γ Γ' s T} → Γ ← Γ' ∶ s → ∀ {i} → Γ ∋ i ∶ T → Γ' ⊢ s i ∶ T
  σ-∋∶ (σ-trm eqz eqs σs der) here = ⊢∶-= eqz  der
  σ-∋∶ (σ-trm eqz eqs σs der) {fs i} (there inc) = ⊢∶-= (eqs i) (σ-∋∶ σs inc)

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

  -- projections are substitutions
  ◂to← : ∀ {Γ Γ' p s} → (∀ i → var (p i) == s i) → Γ ◂ Γ' ∶ p → Γ ← Γ' ∶ s
  ◂to← = {!!}

{-
eq π-∅ =
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
-}

  σ-id : ∀ {Γ} → Γ ← Γ ∶ var
  σ-id {Γ} = ◂to← (λ i → =rf) (π-id (λ _ → =rf))

  σ-rfl : ∀ {Γ s} → (∀ i → var i == s i) → Γ ← Γ ∶ s
  σ-rfl {Γ} eq = ◂to← eq (π-id (λ _ → =rf))

  ←∶v-∋∶ : ∀ {Γ Γ' s} → Γ ← Γ' ∶ s → ∀ {i j} → s i == var j → Γ' ∋ j ∶ pr Γ i
  ←∶v-∋∶ σs {i} eq = ⊢∶-∋∶ (σ-∋∶' σs i) eq


  ←to◂ : ∀ {Γ Γ' p s} → (∀ {i j} → p i == p j → i == j)
           → (∀ i → var (p i) == s i) → Γ ← Γ' ∶ s → Γ ◂ Γ' ∶ p
  ←to◂ inj eq σ-! = π-! _
  ←to◂ {R ∣ Γ} {Γ'} {p} inj eq (σ-trm {s = s} {s'} eqz eqs σs der) = π-∋∶-inv inj aux
    where aux : {i : Fin (suc (len Γ))} {T : Ty} → R ∣ Γ ∋ i ∶ T → Γ' ∋ p i ∶ T
          aux {fz} {T} here = ⊢∶-∋∶ der (eqz • eq fz ⁻¹)
          aux {fs i} {T} (there inc) = ⊢∶-∋∶ (σ-∋∶ σs inc) (eqs i • eq (fs i) ⁻¹)

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
  subj-red {M = app (lam M) N} {.(subst-all M (trmsect N))} (β M N) der =
    σ-subst-0 (⊢-app-premᵣ der) (⊢-abs-prem (⊢-app-premₗ der))
  subj-red {M = lam M} {lam N} (βlam stp) (⊢-abs der) =
    ⊢-abs (subj-red stp der)
  subj-red {M = app M L} {app N L} (βappₗ stp) (⊢-app der₁ der₂) =
    ⊢-app (subj-red stp der₁) der₂
  subj-red {M = app L M} {app L N} (βappᵣ stp) (⊢-app der₁ der₂) =
    ⊢-app der₁ (subj-red stp der₂)
  -- light grey indicates that the clauses do NOT hold definitionally

  -----------------------------
  -- lam M is a canonical form
  -----------------------------
  
  lam-is-canf : ∀ {Γ T S M} → Γ ⊢ M ∶ T ⇒ S → is-value M
                  → Σ[ Trm (suc (len Γ)) ] (λ x → lam x == M)
  lam-is-canf der (val-lam {M'} nrm') = M' ,, =rf

  ------------
  -- progress
  ------------
  
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


  ------------------
  -- neutral terms
  ------------------
  
  data is-neutral {n} : Trm n → Set where
    ntr-var : ∀ {i} → is-neutral (var i)
    ntr-app : ∀ {M N} → is-neutral M → is-neutral (app M N)

  var-is-neutral : ∀ {n M} → Trm-is-var {n} M → is-neutral M
  var-is-neutral {n} {M} Mvar = (is-neutral ● (pj2 Mvar)) (ntr-var {i = pj1 Mvar})
  neutral-is-app+var : ∀ {n M} → is-neutral {n} M → Trm-is-var M + Trm-is-app M
  neutral-is-app+var (ntr-var {i = i}) = inl (i ,, =rf) 
  neutral-is-app+var (ntr-app {M₁} {M₂} _) = inr ((M₁ , M₂) ,, =rf)
  -- and M and N are app+var as well, and so on
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
  -- the second clause quantifies over all `k` and `N : Trm (k +N n)`
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
