
module IPL-implic-frag (A : Set) where
  open import Basic-Inductives

  infixr 50 _⊃_
  data WFF : Set where
    atm : A → WFF
    _⊃_ : WFF → WFF → WFF

  Prem : Set
  Prem = List WFF

  infix 10 _⊢_
  data _⊢_ : Prem → WFF → Set where
    Ass : ∀ {Δ P} → Δ ∋ P → Δ ⊢ P
    →I : ∀ {Δ P Q} → P ∣ Δ ⊢ Q → Δ ⊢ P ⊃ Q
    →E : ∀ {Δ P Q} → Δ ⊢ P ⊃ Q → Δ ⊢ P → Δ ⊢ Q


  -- the order of premises in a derivation does not matter
  ≡-congr-⊢ : ∀ {Δ Δ' P} → Δ ≡ Δ' → Δ ⊢ P → Δ' ⊢ P
  ≡-congr-⊢ eqv (Ass PinΔ) = Ass (≡-∋ eqv PinΔ)
  ≡-congr-⊢ eqv (→I der) = →I (≡-congr-⊢ (≡cnc _ eqv) der)
  ≡-congr-⊢ eqv (→E der₁ der₂) = →E (≡-congr-⊢ eqv der₁) (≡-congr-⊢ eqv der₂)

  ≡⋆-congr-⊢ : ∀ {Δ Δ' P} → Δ ≡⋆ Δ' → Δ ⊢ P → Δ' ⊢ P
  ≡⋆-congr-⊢ (tcin eqv) der =                  ≡-congr-⊢ eqv der
  ≡⋆-congr-⊢ (tccnc {Δ} {Ξ} ch eqv) der =      ≡-congr-⊢ eqv (≡⋆-congr-⊢ ch der)

  -- inswap the first two premises
  swap-prem⊢ : ∀ {Δ P Q R} → Q ∣ R ∣ Δ ⊢ P → R ∣ Q ∣ Δ ⊢ P
  swap-prem⊢ {Q = Q} {R} der = ≡-congr-⊢ (≡swp Q R ≡rfl) der


  swap-prem⊢₂ : ∀ {Δ P Q R S} → Q ∣ R ∣ S ∣ Δ ⊢ P → R ∣ S ∣ Q ∣ Δ ⊢ P
  swap-prem⊢₂ {Q = Q} {R} {S} der =
    ≡⋆-congr-⊢ (≡⋆tr (≡swpcnc ≡rfl) (≡⋆ext R (≡⋆in (≡swp Q S ≡rfl)))) der

  -- weakening is admissible
  wkn-0 : ∀ {Δ P} R → Δ ⊢ P → R ∣ Δ ⊢ P
  wkn-0 R (Ass PinΔ) = Ass (there PinΔ)
  wkn-0 R (→I der) = →I (swap-prem⊢ (wkn-0 R der))
  wkn-0 R (→E der₁ der₂) = →E (wkn-0 R der₁) (wkn-0 R der₂)

{-
  -- contraction is admissible
  cntr-0 : ∀ {Δ P R} → R ∣ R ∣ Δ ⊢ P → R ∣ Δ ⊢ P
  cntr-0 (Ass here) = Ass here
  cntr-0 (Ass (there inp)) = Ass inp
  cntr-0 (→I der) = →I (swap-prem⊢ (cntr-0 (swap-prem⊢₂ der)))
  cntr-0 (→E der₁ der₂) = →E (cntr-0 der₁) (cntr-0 der₂)
-}

  -- not an actual inverse: it adds one step to the derivation
  →I-inv :  ∀ {Δ P Q} → Δ ⊢ P ⊃ Q → P ∣ Δ ⊢ Q
  →I-inv der = →E (wkn-0 _ der) (Ass here)

  →I-comm : ∀ {Δ P Q R} → Δ ⊢ P ⊃ Q ⊃ R → Δ ⊢ Q ⊃ P ⊃ R
  →I-comm der = →I (→I (swap-prem⊢ (→I-inv (→I-inv der))))

  -- type of premises whose extension with P is equivalent to Δ
  _─_ : Prem → WFF → Set
  Δ ─ P = Σ Prem (λ x → Δ ≡⋆ P ∣ x)
  -- take away the first occurrence of a premise
  _─_[_] : ∀ Δ P → Δ ∋ P → Δ ─ P
  (P ∣ Δ) ─ P [ here ] =             Δ ,, ≡⋆rfl
  (R ∣ Δ) ─ P [ there inp ] =        R ∣ pj1 Δ─P  ,,  ≡⋆swpcnc (pj2 Δ─P)
    where Δ─P : Δ ─ P
          Δ─P = Δ ─ P [ inp ]

  →Igen : ∀ {Δ P Q} → (inp : Δ ∋ P) → Δ ⊢ Q → pj1 (Δ ─ P [ inp ]) ⊢ P ⊃ Q
  →Igen {Δ} {P} {Q} inp der = →I (≡⋆-congr-⊢ (pj2 Δ─P) der)
    where Δ─P : Δ ─ P
          Δ─P = Δ ─ P [ inp ]


-- end file
