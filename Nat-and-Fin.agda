{-# OPTIONS --without-K #-}

module Nat-and-Fin where
  open import Identity public

  -------------------
  -- Some arithmetic
  -------------------

  PA4 : ∀ {n} → ¬ (suc n == zero)
  PA4 p = =transp fam4 p 0₁ 
        where fam4 : Nat → Set
              fam4 zero = N₀
              fam4 (suc n) = N₁
  
  suc-inj : ∀ {n m} → suc n == suc m → n == m
  suc-inj {n} {m} p = =ap prdc p

  PA4g : ∀ {n} → ¬ (suc n == n)
  PA4g {zero} = PA4
  PA4g {suc n} = PA4g ∘ suc-inj

  sum-0-is-0 : ∀ {n} {m} → n +N m == zero → n == zero
  sum-0-is-0 {zero} {m} sumisz = =rf
  sum-0-is-0' : ∀ {n} {m} → n +N m == zero → m == zero
  sum-0-is-0' {zero} {m} sumisz = sumisz

  sum-succNat : ∀{n} → (f : Fin (suc n) → Nat) → Nat
  sum-succNat {zero} f = f fz
  sum-succNat {suc n} f = f fz +N sum-succNat (f ∘ fs)

  Nat-dicot : ∀ n → (n == zero) + Σ[ Nat ] (λ x → n == suc x)
  Nat-dicot zero = inl =rf
  Nat-dicot (suc n) = inr (n ,, =rf)

  Nat-is-decid : (n m : Nat) → (n == m) + (n == m → N₀)
  Nat-is-decid zero zero =
    inl =rf
  Nat-is-decid zero (suc m) =
    inr (λ u → PA4 (u ⁻¹))
  Nat-is-decid (suc n) zero =
    inr PA4
  Nat-is-decid (suc n) (suc m) =
    [ (λ u → inl (=ap suc u)) ∣ (λ v → inr (v ∘ suc-inj)) ] (Nat-is-decid n m)

  Nat-is-set : isSet Nat
  Nat-is-set = HedbergThm Nat-is-decid

  +N-idr : ∀ n → n +N zero == n
  +N-idr zero = =rf
  +N-idr (suc n) = =ap suc (+N-idr n)
  +N-sucswap : ∀ n m → n +N suc m == suc n +N m
  +N-sucswap zero m = =rf
  +N-sucswap (suc n) m = =ap suc (+N-sucswap n m) 

  +N-commut : ∀ n m → n +N m == m +N n
  +N-commut zero m = +N-idr m ⁻¹
  +N-commut (suc n) zero = =ap suc (+N-idr n)
  +N-commut (suc n) (suc m) =
    =ap suc (+N-sucswap n m • =ap suc (+N-commut n m) • +N-sucswap m n ⁻¹)

  -- order on Nat
  infix 5 _≤N_ _<N_
  _≤N_ : Nat → Nat → Set
  zero ≤N m = N₁
  suc n ≤N zero = N₀
  suc n ≤N suc m = n ≤N m

  _<N_ : Nat → Nat → Set
  n <N zero = N₀
  zero <N suc m = N₁
  suc n <N suc m = n <N m

  z<Ns : ∀ {n} → zero <N suc n
  z<Ns {n} = 0₁
  <Ns : ∀ {n} → n <N suc n
  <Ns {zero} = 0₁
  <Ns {suc n} = <Ns {n}
  s<Ns : ∀ {n} {m} → n <N m → suc n <N suc m
  s<Ns {n} {m} = id

  <N-trn : ∀ {n m l} → n <N m → m <N l → n <N l
  <N-trn {zero} {m} {suc l} dq1 dq2 = 0₁
  <N-trn {suc n} {suc m} {suc l} dq1 dq2 = <N-trn {n} {m} {l} dq1 dq2

  <+N : ∀ {n} {m} → n <N m → ∀ k → n <N k +N m
  <+N dq zero = dq
  <+N {n} {m} dq (suc k) = <N-trn {n} {k +N m} {suc (k +N m)} (<+N dq k) (<Ns {k +N m})
  <+N' : ∀ {n} {m} → n <N m → ∀ k → n <N m +N k
  <+N' {zero} {suc m} dq k = 0₁
  <+N' {suc n} {suc m} dq k = <+N' {n} {m} dq k
  <s+N : ∀ n k → n <N suc k +N n
  <s+N zero k = 0₁
  <s+N (suc n) k = ((n <N_) ● +N-sucswap k n ⁻¹) (<s+N n k)
  <+Ns : ∀ n k → n <N n +N suc k
  <+Ns zero k = 0₁
  <+Ns (suc n) k = <+Ns n k

  +N<N+N : ∀ {n} {m} → n <N m → ∀ k → k +N n <N k +N m
  +N<N+N dq zero = dq
  +N<N+N dq (suc k) = +N<N+N dq k
  +N<N+N' : ∀ {n} {m} → n <N m → ∀ k → n +N k <N m +N k
  +N<N+N' {zero} {suc m} dq k = <s+N k m
  +N<N+N' {suc n} {suc m} dq k = +N<N+N' {n} {m} dq k
  
  <→≤ : ∀ {n} {m} → n <N m → n ≤N m
  <→≤ {zero} {m} dq = 0₁
  <→≤ {suc n} {suc m} dq = <→≤ {n} dq

  suc-non-decr : ∀ n → suc n ≤N n → N₀
  suc-non-decr (suc n) dq = suc-non-decr n dq

  z≤N : ∀ {n} → zero ≤N n
  z≤N {zero} = 0₁
  z≤N {suc n} = 0₁

  ≤N-rfl : ∀ {n} → n ≤N n
  ≤N-rfl {zero} = 0₁
  ≤N-rfl {suc n} = ≤N-rfl {n}

  =2≤N : ∀ {n m} → n == m → n ≤N m
  =2≤N {n} eq = =transp (n ≤N_) eq (≤N-rfl {n})
  =≤N : ∀ {n n' m} → n == n' → n ≤N m → n' ≤N m
  =≤N {m = m} eq = =transp (_≤N m) eq
  ≤N= : ∀ {n m m'} → n ≤N m → m == m' → n ≤N m'
  ≤N= {n} dq eq = =transp (n ≤N_) eq dq
  =≤N' : ∀ {n n' m} → n == n' → n' ≤N m → n ≤N m
  =≤N' {m = m} eq = =transp (_≤N m) (eq ⁻¹)
  ≤N=' : ∀ {n m m'} → n ≤N m' → m == m' → n ≤N m
  ≤N=' {n} dq eq = =transp (n ≤N_) (eq ⁻¹) dq
    
  ≤N-trn : ∀ {n m l} → n ≤N m → m ≤N l → n ≤N l
  ≤N-trn {zero} dq₁ dq₂ = 0₁
  ≤N-trn {suc n} {suc m} {suc l} dq₁ dq₂ = ≤N-trn {n} {m} {l} dq₁ dq₂

  suc-≤-0 : ∀ n → n ≤N suc n
  suc-≤-0 zero = 0₁
  suc-≤-0 (suc n) = suc-≤-0 n

  suc-≤ : ∀ {n m} → n ≤N m → n ≤N suc m
  suc-≤ {n} {m} dq = ≤N-trn {n} dq (suc-≤-0 m)

  ≤+N : ∀ {n m} → n ≤N m → ∀ k → n ≤N m +N k
  ≤+N {zero} {m} dq k = 0₁
  ≤+N {suc n} {suc m} dq k = ≤+N {n} dq k
  ≤+N' : ∀ {n m} → n ≤N m → ∀ k → n ≤N k +N m
  ≤+N' {n} {m} dq zero = dq
  ≤+N' {n} {m} dq (suc k) = ≤N-trn {n} {k +N m} {suc (k +N m)}
                                    (≤+N' {n} dq k)
                                    (suc-≤-0 (k +N m))

  +N-≤ : ∀ {n₁ n₂ m₁ m₂} → n₁ ≤N m₁ → n₂ ≤N m₂ → n₁ +N n₂ ≤N m₁ +N m₂
  +N-≤ {zero} {n₂} {m₁} {m₂} dq1 dq2 = ≤+N' {n₂} dq2 m₁
  +N-≤ {suc n₁} {n₂} {suc m₁} {m₂} dq1 dq2 = +N-≤ {n₁} dq1 dq2

  ≤anti-sym : ∀ {n m} → n ≤N m → m ≤N n → n == m
  ≤anti-sym {zero} {zero} fz m≤n = =rf
  ≤anti-sym {suc n} {suc m} n≤m m≤n = =ap suc (≤anti-sym n≤m m≤n)

  ≤N-EM : ∀ n m → n ≤N m + m ≤N n
  ≤N-EM zero m = inl 0₁
  ≤N-EM (suc n) zero = inr 0₁
  ≤N-EM (suc n) (suc m) = ≤N-EM n m

  ≤N-diff : ∀ {n m} → n ≤N m → Σ[ Nat ] (λ x → x +N n == m)
  ≤N-diff {zero} {m} leq = m ,, +N-idr m
  ≤N-diff {suc n} {suc m} leq = pj1 (≤N-diff {n} {m} leq) ,, +N-sucswap _ n • =ap suc (pj2 (≤N-diff {n} leq))


  -- finite sets

  fs-inj : ∀ {n}{i j : Fin n} → fs i == fs j → i == j
  fs-inj {_} {fz} {fz} eq = =rf
  fs-inj {_} {fs i} {fs j} eq = =ap fp eq

  PA4-Fin : ∀ {n}{i : Fin n} → fz == fs i → N₀
  PA4-Fin {n} {i} eq = =transp fam4 eq 0₁
                     where fam4 : Fin (suc n) → Set
                           fam4 fz = N₁
                           fam4 (fs i) = N₀

  Fin-is-decid : ∀ {n} → (i j : Fin n) → (i == j) + (i == j → N₀)
  Fin-is-decid {suc n} fz fz =
    inl =rf
  Fin-is-decid {suc n} fz (fs j) =
    inr PA4-Fin
  Fin-is-decid {suc n} (fs i) fz =
    inr (λ v → PA4-Fin (v ⁻¹))
  Fin-is-decid {suc n} (fs i) (fs j) =
    [ (λ u → inl (=ap fs u)) ∣ (λ v → inr (v ∘ fs-inj)) ] (Fin-is-decid i j)

  Fin-is-set : ∀ n → isSet (Fin n)
  Fin-is-set n = HedbergThm (Fin-is-decid {n})

  Fin-=to→ : ∀ {n m} → n == m → Fin n → Fin m
  Fin-=to→ {n} {m} p = =transp Fin p

  Fin-=to→-invrt : ∀ {n m} → (p : n == m) → is-invrt (Fin-=to→ {n} {m} p)
  Fin-=to→-invrt = =transp-is-invrt Fin

  Fin-inhab-is-suc : ∀ {n} → Fin n → Σ[ Nat ] (λ x → suc x == n)
  Fin-inhab-is-suc {zero} = N₀ind
  Fin-inhab-is-suc {suc n} = λ _ → n ,, =rf
  Fin-suc-is-inhab : ∀ {n m} → suc m == n → Fin n
  Fin-suc-is-inhab {n} {m} eq = Fin-=to→ eq fz

  Fin-diag : ∀ {n} → Fin (suc (suc n)) → Fin (suc n)
  Fin-diag fz = fz
  Fin-diag (fs i) = i

  Fin-+Nto→  : ∀ k {n} → Fin n → Fin (k +N n)
  Fin-+Nto→ zero = id
  Fin-+Nto→ (suc k) = fs ∘ Fin-+Nto→ k
  Fin-≤to→ : ∀ {n m} → n ≤N m → Fin n → Fin m
  Fin-≤to→ {n} {m} leq = Fin-=to→ eq ∘ Fin-+Nto→ k
    where k : Nat
          k = pj1 (≤N-diff {n} leq)
          eq : k +N n == m
          eq = pj2 (≤N-diff {n} leq)

  Fin[_∣_]_ Fin+N-fnc : ∀ {n m} {A : Set} → (Fin n → A) → (Fin m → A) → Fin (n +N m) → A
  Fin+N-fnc {zero} lt rt             = rt
  Fin+N-fnc {suc n} lt rt fz         = lt fz
  Fin+N-fnc {suc n} lt rt (fs i)     = Fin+N-fnc (lt ∘ fs) rt i
  Fin[_∣_]_ = Fin+N-fnc

  Fin+N-inl : ∀ {n m} → Fin n → Fin (n +N m)
  Fin+N-inl {zero} = N₀ind
  Fin+N-inl {suc n} fz        = fz
  Fin+N-inl {suc n} (fs i)    = fs (Fin+N-inl i)

  Fin+N-inr : ∀ {n m} → Fin m → Fin (n +N m)
  Fin+N-inr {zero} {m}      = id
  Fin+N-inr {suc n} {m}     = fs ∘ Fin+N-inr {n} {m}

  Fin+N-trl : ∀ {n m} {A : Set} → (lt : Fin n → A) → (rt : Fin m → A)
                → ∀ i → Fin+N-fnc lt rt (Fin+N-inl i) == lt i
  Fin+N-trl {suc n} lt rt fz          = =rf {a = lt fz}
  Fin+N-trl {suc n} lt rt (fs i)      = Fin+N-trl (lt ∘ fs) rt i

  Fin+N-trr : ∀ {n m} {A : Set} → (lt : Fin n → A) → (rt : Fin m → A)
                → ∀ i → Fin+N-fnc lt rt (Fin+N-inr i) == rt i
  Fin+N-trr {zero} lt rt i           = =rf {a = rt i}
  Fin+N-trr {suc n} lt rt i          = Fin+N-trr (lt ∘ fs) rt i


  Fin+N-ind : ∀ {n m} (C : Fin (n +N m) → Set)
                → (∀ i → C (Fin+N-inl {n} i)) → (∀ i → C (Fin+N-inr {m = m} i))
                  → ∀ i → C i
  Fin+N-ind {zero} {m} C lt rt            = rt
  Fin+N-ind {suc n} {m} C lt rt fz        = lt fz
  Fin+N-ind {suc n} {m} C lt rt (fs i)    = Fin+N-ind (λ x → C (fs x)) (λ x → lt (fs x)) rt i

  Fin+N-indl : ∀ {n m} {C : Fin (n +N m) → Set}
                 (lt : ∀ i → C (Fin+N-inl {n} i)) (rt : ∀ i → C (Fin+N-inr {m = m} i))
                   → ∀ i → Fin+N-ind C lt rt (Fin+N-inl i) == lt i
  Fin+N-indl {suc n} {m} {C} lt rt fz           = =rf {a = lt fz}
  Fin+N-indl {suc n} {m} {C} lt rt (fs i)       = Fin+N-indl (λ x → lt (fs x)) rt i

  Fin+N-indr : ∀ {n m} {C : Fin (n +N m) → Set}
                 (lt : ∀ i → C (Fin+N-inl {n} i)) (rt : ∀ i → C (Fin+N-inr {m = m} i))
                   → ∀ i → Fin+N-ind C lt rt (Fin+N-inr i) == rt i
  Fin+N-indr {zero} {m} {C} lt rt i           = =rf {a = rt i}
  Fin+N-indr {suc n} {m} {C} lt rt i          = Fin+N-indr (λ x → lt (fs x)) rt i


  Fin+N-induqg :  ∀ {n m} {C : Fin (n +N m) → Set} {f g : ∀ i → C i}
                    → (∀ i → f (Fin+N-inl {n} i) == g (Fin+N-inl i))
                    → (∀ i → f (Fin+N-inr i) == g (Fin+N-inr i))
                      → ∀ i → f i == g i
  Fin+N-induqg {f = f} {g} = Fin+N-ind (λ i → f i == g i)

  Fin+N-induq :  ∀ {n m} {C : Fin (n +N m) → Set}
                   (lt : ∀ i → C (Fin+N-inl {n} i)) (rt : ∀ i → C (Fin+N-inr {m = m} i))
                   {f : ∀ i → C i}
                → (∀ i → f (Fin+N-inl i) == lt i) → (∀ i → f (Fin+N-inr i) == rt i)
                  → ∀ i → f i == Fin+N-ind C lt rt i
  Fin+N-induq lt rt {f} eql eqr = Fin+N-induqg {f = f} {Fin+N-ind _ lt rt}
                                               (λ i → eql i • Fin+N-indl lt rt i ⁻¹)
                                               (λ i → eqr i • Fin+N-indr lt rt i ⁻¹)

  Fin+N-fncuqg :  ∀ {n m} {A : Set} {f g : Fin (n +N m) → A}
                    → (∀ i → f (Fin+N-inl {n} i) == g (Fin+N-inl i))
                    → (∀ i → f (Fin+N-inr i) == g (Fin+N-inr i))
                      → ∀ i → f i == g i
  Fin+N-fncuqg {f = f} {g} = Fin+N-ind (λ i → f i == g i)

  Fin+N-fncuq :  ∀ {n m} {A : Set} (lt : Fin n → A) (rt : Fin m → A) {f : Fin (n +N m) → A}
                   → (∀ i → f (Fin+N-inl i) == lt i) → (∀ i → f (Fin+N-inr i) == rt i)
                     → ∀ i → f i == Fin+N-fnc lt rt i
  Fin+N-fncuq lt rt {f} eql eqr = Fin+N-fncuqg {f = f} {Fin+N-fnc lt rt}
                                               (λ i → eql i • Fin+N-trl lt rt i ⁻¹)
                                               (λ i → eqr i • Fin+N-trr lt rt i ⁻¹)


  Fin+N-fnc-invrt : ∀ {n m} {A B : Set}{f : Fin n → A}{g : Fin m → B}
                    → is-invrt f → is-invrt g → is-invrt (Fin+N-fnc (inl ∘ f) (inr ∘ g))
  Fin+N-fnc-invrt {n} {m}  {A} {B} {f} {g} invf invg =
    h ,, (h[fg]=id , [fg]h=id)
    where h : A + B → Fin (n +N m)
          h = [ Fin+N-inl ∘ pj1 invf ∣ Fin+N-inr ∘ pj1 invg ]
          h[fg]=id : ∀ i → h (Fin+N-fnc (inl ∘ f) (inr ∘ g) i) == i
          h[fg]=id = Fin+N-fncuqg {f = h ∘ Fin+N-fnc (inl ∘ f) (inr ∘ g)} {id}
                                  (λ i → =proof
                     h (Fin+N-fnc (inl ∘ f) (inr ∘ g) (Fin+N-inl i))
                                            ==[ =ap h (Fin+N-trl (inl ∘ f) (inr ∘ g) i) ] /
                     h (inl (f i))          ==[ =ap Fin+N-inl (prj1 (pj2 invf) i) ]∎
                     -- = Fin+N-inl (pj1 invf (f i))
                     Fin+N-inl i ∎)
                                  λ i → =proof
                     h (Fin+N-fnc (inl ∘ f) (inr ∘ g) (Fin+N-inr i))
                                            ==[ =ap h (Fin+N-trr (inl ∘ f) (inr ∘ g) i) ] /
                     h (inr (g i))          ==[ =ap Fin+N-inr (prj1 (pj2 invg) i) ]∎
                     -- = Fin+N-inr (pj1 invg (g i))
                     Fin+N-inr i ∎
          [fg]h=id : ∀ x → Fin+N-fnc (inl ∘ f) (inr ∘ g) (h x) == x
          [fg]h=id = +ind (λ x → Fin+N-fnc (inl ∘ f) (inr ∘ g) (h x) == x)
                          (λ a → =proof
                     Fin+N-fnc (inl ∘ f) (inr ∘ g) (h (inl a))
                                         ==[ Fin+N-trl (inl ∘ f) (inr ∘ g) (pj1 invf a) ] /
                     inl (f (pj1 invf a))               ==[ =ap inl (prj2 (pj2 invf) a) ]∎
                     inl a ∎)
                          λ b → =proof
                     Fin+N-fnc (inl ∘ f) (inr ∘ g) (h (inr b))
                                         ==[ Fin+N-trr (inl ∘ f) (inr ∘ g) (pj1 invg b) ] /
                     inr (g (pj1 invg b))               ==[ =ap inr (prj2 (pj2 invg) b) ]∎
                     inr b ∎

  Fin+N-fnc-eqv : ∀ {n m} {A B : Set}{f : Fin n → A}{g : Fin m → B}
                    → is-equiv f → is-equiv g → is-equiv (Fin+N-fnc (inl ∘ f) (inr ∘ g))
  Fin+N-fnc-eqv eqvf eqvg = invrt-is-eqv (Fin+N-fnc-invrt (eqv-is-invrt eqvf)
                                                          (eqv-is-invrt eqvg))

  -- max of finite stuff
  is-maxN-2 : ∀ n m → Nat → Set
  is-maxN-2 n m = λ x → n ≤N x × m ≤N x × (∀ {l} → n ≤N l → m ≤N l → x ≤N l)

  max≤N-2 : ∀ n m → Σ[ Nat ] (is-maxN-2 n m)
  max≤N-2 zero m =
    m ,, (z≤N {m} , ≤N-rfl {m} , λ _ dq → dq)
  max≤N-2 (suc n) zero =
    suc n ,, (≤N-rfl {n} , 0₁ , λ dq _ → dq)
  max≤N-2 (suc n) (suc m) =
    suc (pj1 ih) ,, (prj1 (pj2 ih) , prj1 (prj2 (pj2 ih)) , λ {l} → aux {l})
    where ih : Σ[ Nat ] (is-maxN-2 n m)
          ih = max≤N-2 n m
          aux : {l : Nat} → suc n ≤N l → suc m ≤N l → suc (pj1 ih) ≤N l
          aux {suc l} = prj2 (prj2 (pj2 ih)) {l}

  max≤N-2-EM : ∀ n m → (pj1 (max≤N-2 n m) == n) + (pj1 (max≤N-2 n m) == m)
  max≤N-2-EM zero m = inr =rf
  max≤N-2-EM (suc n) zero = inl =rf
  max≤N-2-EM (suc n) (suc m) = [ inl ∘ =ap suc ∣ inr ∘ =ap suc ] (max≤N-2-EM n m)

  is-max≤N-Fin : ∀ {n} → (f : Fin n → Nat) → Fin n → Set
  is-max≤N-Fin f iₘₓ = ∀ i → f i ≤N f iₘₓ

  max≤N-Finsuc : ∀ {n} → (f : Fin (suc n) → Nat) → Σ[ Fin (suc n) ] (is-max≤N-Fin f)
  max≤N-Finsuc {zero} f = fz ,, λ i → =2≤N (=ap f (pj2 (N₁-isContr) i))
  max≤N-Finsuc {suc n} f = pj1 iₘₓ ,, i-ismax
    where mxffs : Σ[ Fin (suc n) ] (is-max≤N-Fin (f ∘ fs))
          mxffs = max≤N-Finsuc (f ∘ fs)
          mxN : Σ[ Nat ] (is-maxN-2 (f (fs (pj1 (max≤N-Finsuc (f ∘ fs))))) (f fz))
          mxN = max≤N-2 (f (fs (pj1 mxffs))) (f fz)
          iₘₓ : Σ[ Fin (suc (suc n)) ] (λ x → f x == pj1 mxN)
          iₘₓ = [ f₁ ∣ f₂ ] (max≤N-2-EM (f (fs (pj1 mxffs))) (f fz))
            where f₁ : pj1 (max≤N-2 (f (fs (pj1 mxffs))) (f fz)) == f (fs (pj1 mxffs))
                           → Σ[ Fin (two +N n) ] (λ x → f x == pj1 mxN)
                  f₁ eq = fs (pj1 mxffs) ,, eq ⁻¹
                  f₂ : pj1 (max≤N-2 (f (fs (pj1 mxffs))) (f fz)) == f fz
                           → Σ[ Fin (suc (suc n)) ] (λ x → f x == pj1 mxN)
                  f₂ eq = fz ,, eq ⁻¹
          i-ismax : ∀ i → f i ≤N f (pj1 iₘₓ)
          i-ismax fz = ≤N= {f fz} {pj1 mxN} {f (pj1 iₘₓ)} (prj1 (prj2 (pj2 mxN))) (pj2 iₘₓ ⁻¹)
          i-ismax (fs i) = ≤N-trn {f (fs i)} {f (fs (pj1 mxffs))} {f (pj1 iₘₓ)}
                                  (pj2 mxffs i) (≤N= {f (fs (pj1 mxffs))} {pj1 mxN} (prj1 (pj2 mxN))
                                                                                    (pj2 iₘₓ ⁻¹))

  max≤N-Fin : ∀ {n} → (f : Fin n → Nat)
                    → (Fin n → N₀) + Σ[ Fin n ] (is-max≤N-Fin f)
  max≤N-Fin {zero} f = inl id
  max≤N-Fin {suc n} f = inr (max≤N-Finsuc f)


  is-finite : Set → Set
  is-finite A = Σ[ Nat ] (λ n → Σ[ (Fin n → A) ] is-equiv)

  is-finite-bound : Set → Set
  is-finite-bound A = Σ[ Nat ] (λ n → Σ[ ((Fin n → A) × (A → Fin n)) ]
                                          (λ x → ∀ a → prj1 x (prj2 x a) == a))

  -- function that misses an element (face map)
  miss-Fin : ∀ {n} → (i : Fin (suc n))
               → Σ[ (Fin n → Fin (suc n)) ] (λ x → ∀ j → i == x j → N₀)
  miss-Fin fz = fs ,, λ j → PA4-Fin {i = j}
  miss-Fin {suc n} (fs i) = fst ,, snd
    where ih : Σ[ (Fin n → Fin (suc n)) ] (λ x → ∀ j → i == x j → N₀)
          ih = miss-Fin i
          fst : Fin (suc n) → Fin (suc (suc n))
          fst fz = fz
          fst (fs j) = fs (pj1 ih j)
          snd : (j : Fin (suc n)) → fs i == fst j → N₀
          snd fz eq = PA4-Fin {i = i} (eq ⁻¹)
          snd (fs j) eq = pj2 ih j (fs-inj eq)

  miss-restr : ∀ {n m} → (f : Fin n → Fin (suc m))
                → ∀ i → (∀ j → Σ[ Fin m ] (λ x → f j == pj1 (miss-Fin i) x))
                  → Σ[ (Fin n → Fin m) ]
                       (λ x → ∀ j → f j == pj1 (miss-Fin i) (x j))
  miss-restr {n} {m} f i missi = (λ j → pj1 (missi j)) ,, (λ j → pj2 (missi j))

{-
  missf-Fin : ∀ {n m} → (f : Fin (suc n) → Fin (suc m))
                → ∀ i → Σ[ (Fin n → Fin m) ]
                           (λ x → ∀ j → f (pj1 (miss-Fin i) j) == pj1 (miss-Fin (f i)) (x j))
  missf-Fin {n} {m} f i = {!!} ,, {!!}
    where rst : Σ (Fin n → Fin m)
                  (λ x → ∀ j → f (pj1 (miss-Fin i) j) == pj1 (miss-Fin (f i)) (x j))
          rst = miss-restr (f ∘ pj1 (miss-Fin i))
                           (f i)
                           (λ j → {!!})
-}

  -- canonical lift of a function between finite sets
  liftFin :  ∀ {n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
  liftFin f fz = fz
  liftFin f (fs i) = fs (f i)
  -- listFin f = [fx ; fs ∘ f] : 1 + Fin n → Fin (suc m)

  -- lift that swaps the first two elements
  swapFin : ∀ {n m} → (Fin n → Fin m) → Fin (suc (suc n)) → Fin (suc (suc m))
  swapFin f fz = fs fz
  swapFin f (fs i) = liftFin (fs ∘ f) i

  -- some properties of it
  liftFin-id : ∀ {n f} → (∀ i → f i == i) → ∀ i → liftFin {n} f i == i
  liftFin-id isid fz = =rf
  liftFin-id isid  (fs i) = =ap fs (isid i)
  liftFin-ptw : {n m : Nat}{f f' : Fin n → Fin m}
                   → (∀ i → f i == f' i) → ∀ i → liftFin f i == liftFin f' i
  liftFin-ptw {f = f} {f'} pf fz = =rf {a = fz}
  liftFin-ptw {f = f} {f'} pf (fs i) = =ap fs (pf i)

  liftFin-cmp : {n m k : Nat}(f : Fin n → Fin m)(g : Fin m → Fin k)
                       → (i : Fin (suc n)) → liftFin g (liftFin f i) == liftFin (g ∘ f) i
  liftFin-cmp f g fz = =rf
  liftFin-cmp f g (fs i) = =rf

  liftFin-cmp⁻¹ : {n m k : Nat}(f : Fin n → Fin m)(g : Fin m → Fin k)
                       → (i : Fin (suc n)) → liftFin (g ∘ f) i == liftFin g (liftFin f i)
  liftFin-cmp⁻¹ f g i = liftFin-cmp f g i ⁻¹

  liftFin-sq : {n m : Nat}{f : Fin n → Fin m}{f' : Fin (suc n) → Fin (suc m)}
               {g : Fin n → Fin (suc n)}{g' : Fin m → Fin (suc m)}
                 → (∀ i → g' (f i) == f' (g i))
                   → ∀ i → liftFin g' (liftFin f i) == liftFin f' (liftFin g i)
  liftFin-sq pf fz = =rf
  liftFin-sq pf (fs i) = =ap fs (pf i)

  liftFin-inj : ∀ {n m} {f : Fin n → Fin m} (finj : ∀ {x x'} → f x == f x' → x == x')
                  → ∀ {x x'} → liftFin f x == liftFin f x' → x == x'
  liftFin-inj finj {fz} {fz} eq = =rf
  liftFin-inj finj {fs x} {fs x'} eq = =ap fs (finj (fs-inj eq))

-- end of file
