{-# OPTIONS --without-K #-}

module Basic-Inductives where

  -- Identity and composite functions

  id : {A : Set} → A → A
  id = λ x → x

  infixr 4 _∘_ _∘'_
  _∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
  g ∘ f = λ x → g (f x)
  _∘'_ : {A' A : Set} → (A → Set) → (A' → A) → A' → Set
  B ∘' f = λ x → B (f x)

  -- Identity type

  infix 1 _==_
  data _==_ {A : Set} (a : A) : A → Set where
    =rf : a == a

  -- Binary products and Σ-types

  infixr 3 _,_ _×_ ⟨_∣_⟩
  data _×_ (A : Set) (B : Set) : Set where
    _,_ : A → B → A × B
  prj1 : {A : Set} → {B : Set}  → A × B → A
  prj1 (a , b) = a
  prj2 : {A : Set} → {B : Set}  → A × B → B
  prj2 (a , b) = b
  ⟨_∣_⟩ : {C A B : Set} → (C → A) → (C → B) → C → A × B
  ⟨ f ∣ g ⟩ = λ x → f x , g x

  infixr 4 _,,_ Σ[_]_ ⟨_∣∣_⟩
  data Σ[_]_ (A : Set) (B : A → Set) : Set where
    _,,_ : (a : A) → B a → Σ[ A ] B
  pj1 : {A : Set} → {B : A → Set} → Σ[ A ] B → A
  pj1 (a ,, b) = a
  pj2 : {A : Set} → {B : A → Set}  → (u : Σ[ A ] B) → (B (pj1 u))
  pj2 (a ,, b) = b
  ⟨_∣∣_⟩ : {C A : Set}{B : A → Set} → (f : C → A) → (∀ c → B (f c)) → C → Σ[ A ] B
  ⟨ f ∣∣ g ⟩ = λ x → f x ,, g x

  -- sums
  infixr 3 _+_ [_∣_] [_∥_∥_]
  data _+_ (A : Set) (B : Set) : Set where
    inl : A → A + B
    inr : B → A + B

  inrl : {A B C : Set} → B → A + B + C
  inrl {A} {B} {C} = inr ∘ inl
  inrr : {A B C : Set} → C → A + B + C
  inrr {A} {B} {C} = inr ∘ inr

  [_∣_] : ∀ {A B C : Set} → (A → C) → (B → C) → A + B → C
  [ f ∣ g ] (inl a) = f a
  [ f ∣ g ] (inr b) = g b

  +rec3 [_∥_∥_] : ∀ {A B C D : Set} → (A → D) → (B → D) → (C → D) → A + B + C → D
  +rec3 f g h = [ f ∣ [ g ∣ h ] ]
  [ f ∥ g ∥ h ] = +rec3 f g h

  +ind : ∀ {A B : Set} → (C : A + B → Set ) → (∀ a → C (inl a)) → (∀ b → C (inr b))
           → ∀ x → C x
  +ind C ls rs (inl a) = ls a
  +ind C ls rs (inr b) = rs b

  +ind3 : ∀ {A B C : Set} → (D : A + B + C → Set )
            → (∀ a → D (inl a)) → (∀ b → D (inrl b)) → (∀ c → D (inrr c))
              → ∀ x → D x
  +ind3 C ls cs rs (inl a) = ls a
  +ind3 C ls cs rs (inr (inl b)) = cs b
  +ind3 C ls cs rs (inr (inr c)) = rs c

  +rec3-dist : ∀ {A₁ A₂ A₃ B₁ B₂ B₃ : Set} (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) (f₃ : A₃ → B₃)
                  → ∀ v → [ inl ∘ f₁ ∥ inrl ∘ f₂ ∥ inrr ∘ f₃ ] v
                                == [ inl ∘ f₁ ∣ inr ∘ [ (inl ∘ f₂) ∣ (inr ∘ f₃) ] ] v
  +rec3-dist f₁ f₂ f₃ = +ind3 (λ v → [ inl ∘ f₁ ∥ inrl ∘ f₂ ∥ inrr ∘ f₃ ] v
                                           == [ inl ∘ f₁ ∣ inr ∘ [ inl ∘ f₂ ∣ inr ∘ f₃ ] ] v)
                              (λ _ → =rf)
                              (λ _ → =rf)
                              (λ _ → =rf)

  -- distributivities

  +×+-dist : {A₁ A₂ B₁ B₂ : Set} → (A₁ + B₁) × (A₂ + B₂)
                 → (A₁ × A₂) + (A₁ × B₂) + (B₁ × A₂) + (B₁ × B₂)
  +×+-dist (inl a1 , inl a2) = inl (a1 , a2)
  +×+-dist (inl a1 , inr b2) = inr (inl (a1 , b2))
  +×+-dist (inr b1 , inl a2) = inr (inr (inl (b1 , a2)))
  +×+-dist (inr b1 , inr b2) = inr (inr (inr (b1 , b2)))


  -- Natural numbers and its initial segments

  data Nat : Set where
    zero : Nat
    suc : Nat → Nat

  one two three : Nat
  one = suc zero
  two = suc one
  three = suc two
  prdc : Nat → Nat
  prdc zero = zero
  prdc (suc n) = n
  infixr 10 _+N_
  _+N_ : Nat → Nat → Nat
  zero +N m = m
  suc n +N m = suc (n +N m)


  data Fin : Nat → Set where
    fz : ∀ {n} → Fin (suc n)
    fs : ∀ {n} → Fin n → Fin (suc n)

  Fin-ind : ∀ {n} (C : Fin (suc n) → Set) → (cz : C fz) → (cs : ∀ j → C (fs j)) → ∀ j → C j
  Fin-ind C cz cs fz = cz
  Fin-ind C cz cs (fs j) = cs j
  Fin-rec : ∀ {n} {C : Set} → (cz : C) → (cs : Fin n → C) → Fin (suc n) → C
  Fin-rec cz cs fz = cz
  Fin-rec cz cs (fs j) = cs j

  fp : ∀ {n} → Fin (suc (suc n)) → Fin (suc n)
  fp fz = fz
  fp (fs i) = i
  fi : ∀ {n} → Fin n → Fin (suc n)
  fi {suc n} fz = fz
  fi {suc n} (fs i) = fs (fi i)

  N₀ N₁ N₂ : Set
  N₀ = Fin zero
  N₁ = Fin one
  N₂ = Fin two
  0₁ : N₁
  0₁ = fz
  0₂ 1₂ : N₂
  0₂ = fz
  1₂ = fs 0₁
  N₀rec : {C : Set} → N₀ → C
  N₀rec {C} ()
  N₀ind : {C : N₀ → Set} → (x : N₀) → C x
  N₀ind {C} ()
  N₁ind : {C : N₁ → Set}(c : C 0₁) → (x : N₁) → C x
  N₁ind {C} c fz = c

  ¬ : Set → Set
  ¬ A = A → N₀
  ¬-is-covar : {A B : Set} → (A → B) → ¬ B → ¬ A
  ¬-is-covar f = λ nb a → nb (f a)
  ¬¬η : {A : Set} → A → ¬ (¬ A)
  ¬¬η a = λ f → f a
  dec→¬¬e : {A : Set} → A + ¬ A → ¬ (¬ A) → A
  dec→¬¬e (inl a) = λ _ → a
  dec→¬¬e (inr na) = λ f → N₀ind (f na)

  ¬Σ→Π¬ : ∀ {A} {B : A → Set} → ¬ (Σ[ A ] B) → ∀ a → ¬ (B a)
  ¬Σ→Π¬ ne = λ a → ne ∘ (a ,,_)
  Π¬→¬Σ : ∀ {A} {B : A → Set} → (∀ a → ¬ (B a)) → ¬ (Σ[ A ] B)
  Π¬→¬Σ an = λ z → an (pj1 z) (pj2 z)

  ---------
  -- Lists
  ---------

  infixr 20 _∣_ _∥_
  data List (A : Set) : Set where
    [] : List A
    _∣_ : A → List A → List A

  lenList : ∀ {A} → List A → Nat
  lenList [] = zero
  lenList (a ∣ α) = suc (lenList α)

  _∥_ : ∀ {A} → List A → List A → List A
  [] ∥ Ξ = Ξ
  (P ∣ Δ) ∥ Ξ = P ∣ (Δ ∥ Ξ)

  infix 10 _∋_
  data _∋_ {A} : List A → A → Set where
    here  : ∀ {α a} → a ∣ α ∋ a
    there : ∀ {α a b} → α ∋ a → b ∣ α ∋ a

  -- position of the member of a list
  posList : ∀ {A α a} → α ∋ a → Fin (lenList {A = A} α)
  posList here = fz
  posList (there inls) = fs (posList inls)

  -- i-th element of a list
  prList : ∀ {A} → (α : List A) → Fin (lenList α) → A
  prList (a ∣ α) fz = a
  prList (a ∣ α) (fs i) = prList α i

-- end of file
