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
  PA4⁻¹ : ∀ {n} → ¬ (zero == suc n)
  PA4⁻¹ p = PA4 (p ⁻¹)

  suc-inj : ∀ {n m} → suc n == suc m → n == m
  suc-inj {n} {m} p = =ap prdc p

  PA4g : ∀ {n} → ¬ (suc n == n)
  PA4g {zero} = PA4
  PA4g {suc n} = PA4g ∘ suc-inj

  sum-succNat : ∀{n} → (f : Fin (suc n) → Nat) → Nat
  sum-succNat {zero} f = f fz
  sum-succNat {suc n} f = f fz +N sum-succNat (f ∘ fs)

  Nat-dicot : ∀ n → (zero == n) + Σ[ Nat ] (λ x → suc x == n)
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

  Nat-isSet : isSet Nat
  Nat-isSet = HedbergThm Nat-is-decid
  suc-idfull : is-idfull suc
  suc-idfull = inj-set-is-idfull Nat-isSet suc-inj

  +N-idr : ∀ n → n +N zero == n
  +N-idr zero = =rf
  +N-idr (suc n) = =ap suc (+N-idr n)
  +N-idr⁻¹ : ∀ n → n == n +N zero
  +N-idr⁻¹ n = +N-idr n ⁻¹
  +N-idlg⁻¹ : ∀ {n m} → zero == n → m == n +N m
  +N-idlg⁻¹ {n} {m} = =ap (_+N m)
  +N-idlg : ∀ {n m} → zero == n → n +N m == m
  +N-idlg n=z = +N-idlg⁻¹ n=z ⁻¹
  +N-idrg⁻¹ : ∀ {n m} → zero == m → n == n +N m
  +N-idrg⁻¹ {n} {m} m=z = +N-idr⁻¹ n • =ap (n +N_) m=z
  +N-idrg : ∀ {n m} → zero == m → n +N m == n
  +N-idrg m=z = +N-idrg⁻¹ m=z ⁻¹

  +N-sucswap : ∀ n m → n +N suc m == suc n +N m
  +N-sucswap zero m = =rf
  +N-sucswap (suc n) m = =ap suc (+N-sucswap n m) 
  +N-sucswap⁻¹ : ∀ n m → suc n +N m == n +N suc m
  +N-sucswap⁻¹ n m = +N-sucswap n m ⁻¹

  +N-commut : ∀ n m → n +N m == m +N n
  +N-commut zero m = +N-idr m ⁻¹
  +N-commut (suc n) zero = =ap suc (+N-idr n)
  +N-commut (suc n) (suc m) =
    =ap suc (+N-sucswap n m • =ap suc (+N-commut n m) • +N-sucswap⁻¹ m n)

  sum-0-is-0 : ∀ {n} {m} → n +N m == zero → zero == n
  sum-0-is-0 {zero} {m} sumisz = =rf
  sum-0-is-0⁻¹ : ∀ {n} {m} → n +N m == zero → n == zero
  sum-0-is-0⁻¹ sumisz = sum-0-is-0 sumisz ⁻¹
  sum-0-is-0' : ∀ {n} {m} → n +N m == zero → zero == m
  sum-0-is-0' {zero} {m} sumisz = sumisz ⁻¹
  sum-0-is-0'⁻¹ : ∀ {n} {m} → n +N m == zero → m == zero
  sum-0-is-0'⁻¹ sumisz = sum-0-is-0' sumisz ⁻¹
  sum-lh-rh-zero : ∀ {n m} → n +N m == n → m == zero
  sum-lh-rh-zero {zero} =            id
  sum-lh-rh-zero {suc n} sn+m=sn =   sum-lh-rh-zero (suc-inj sn+m=sn)
  sum-rh-lh-zero : ∀ {n m} → m +N n == n → m == zero
  sum-rh-lh-zero {zero} {m} m+z=z =
    +N-idr⁻¹ m • m+z=z
  sum-rh-lh-zero {suc n} {m} m+sn=sn =
    sum-rh-lh-zero {n} {m} (suc-inj (+N-sucswap⁻¹ _ _ • m+sn=sn))

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

  fs-inj : ∀ {n} → is-injective (fs {n})
  fs-inj {_} {fz} {fz} eq = =rf
  fs-inj {_} {fs i} {fs j} eq = =ap fp eq
  
  PA4-Fin : ∀ {n}{i : Fin n} → fz == fs i → N₀
  PA4-Fin {n} {i} eq = =transp fam4 eq 0₁
                     where fam4 : Fin (suc n) → Set
                           fam4 fz = N₁
                           fam4 (fs i) = N₀
  PA4-Fin⁻¹ : ∀ {n}{i : Fin n} → fs i == fz → N₀
  PA4-Fin⁻¹ eq = PA4-Fin (eq ⁻¹)

  Fin-dicot : ∀ {n} i → (fz == i) + Σ[ Fin n ] (λ x → fs x == i)
  Fin-dicot {n} fz = inl =rf
  Fin-dicot {n} (fs i) = inr (i ,, =rf)
  Fin-dicotfz : ∀ {n} i → ¬ (Σ[ Fin n ] (λ x → fs x == i)) → fz == i
  Fin-dicotfz i i≠s =
    [ id
    ∣ (λ x → N₀ind (i≠s x))
    ] (Fin-dicot i)  
  Fin-dicotfs : ∀ {n} i → ¬ (fz == i) → Σ[ Fin n ] (λ x → fs x == i)
  Fin-dicotfs i i≠z =
    [ (λ x → N₀ind (i≠z x))
    ∣ id
    ] (Fin-dicot i)

  Fin-is-decid : ∀ {n} → (i j : Fin n) → (i == j) + (i == j → N₀)
  Fin-is-decid {suc n} fz fz =
    inl =rf
  Fin-is-decid {suc n} fz (fs j) =
    inr PA4-Fin
  Fin-is-decid {suc n} (fs i) fz =
    inr (λ v → PA4-Fin (v ⁻¹))
  Fin-is-decid {suc n} (fs i) (fs j) =
    [ (λ u → inl (=ap fs u)) ∣ (λ v → inr (v ∘ fs-inj)) ] (Fin-is-decid i j)

  Fin-isSet : ∀ n → isSet (Fin n)
  Fin-isSet n = HedbergThm (Fin-is-decid {n})
  fs-idfull : ∀ {n} → is-idfull (fs {n})
  fs-idfull = inj-set-is-idfull (Fin-isSet _) fs-inj

  Fin-=to→ : ∀ {n m} → n == m → Fin n → Fin m
  Fin-=to→ {n} {m} p = =transp Fin p

  Fin-=to→-fzap : ∀ {n m} (n=m : n == m)
                  → Fin-=to→ (=ap suc n=m) fz == fz
  Fin-=to→-fzap = =J (λ _ u → Fin-=to→ (=ap suc u) fz == fz) =rf
  Fin-=to→-fz : ∀ {n m} (sn=sm : suc n == suc m)
                  → Fin-=to→ sn=sm fz == fz
  Fin-=to→-fz {n} {m} sn=sm =
    ((λ u → Fin-=to→ u fz == fz) ● pf) (Fin-=to→-fzap n=m)
    where n=m : n == m
          n=m = pj1 (suc-idfull sn=sm)
          pf : =ap suc n=m == sn=sm
          pf = pj2 (suc-idfull sn=sm)
  
  Fin-=to→-fsap : ∀ {n m} (n=m : n == m)
                  → ∀ j → fs (Fin-=to→ n=m j) == Fin-=to→ (=ap suc n=m) (fs j)
  Fin-=to→-fsap = =J (λ _ u → ∀ j → fs (Fin-=to→ u j) == Fin-=to→ (=ap suc u) (fs j))
                      (λ _ → =rf)
  Fin-=to→-fs : ∀ {n m} (n=m : n == m) (sn=sm : suc n == suc m)
                  → ∀ j → fs (Fin-=to→ n=m j) == Fin-=to→ sn=sm (fs j)
  Fin-=to→-fs {n} {m} n=m sn=sm j =
    ((λ u → fs (Fin-=to→ n=m j) == Fin-=to→ u (fs j)) ● pf)
          (Fin-=to→-fsap n=m j)
    where pf : =ap suc n=m == sn=sm
          pf = Nat-isSet _ _


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


  -- the finite set on a sum is the sum of the sets
  Fin[_∣_] Fin+N-fnc : ∀ {n m} {A : Set} → (Fin n → A) → (Fin m → A) → Fin (n +N m) → A
  Fin+N-fnc {zero} lt rt             = rt
  Fin+N-fnc {suc n} lt rt fz         = lt fz
  Fin+N-fnc {suc n} lt rt (fs i)     = Fin+N-fnc (lt ∘ fs) rt i
  Fin[_∣_] = Fin+N-fnc

  -- canonical injections
  Fin+N-inl : ∀ {n m} → Fin n → Fin (n +N m)
  Fin+N-inl {zero} = N₀ind
  Fin+N-inl {suc n} fz        = fz
  Fin+N-inl {suc n} (fs i)    = fs (Fin+N-inl i)

  Fin+N-inr : ∀ {n m} → Fin m → Fin (n +N m)
  Fin+N-inr {zero} {m}      = id
  Fin+N-inr {suc n} {m}     = fs ∘ Fin+N-inr {n} {m}

  Fin+N-inl≠inr : ∀ {n m} i j → ¬ (Fin+N-inl {n} i == Fin+N-inr {_} {m} j)
  Fin+N-inl≠inr {suc n} {suc m} fz j       = PA4-Fin
  Fin+N-inl≠inr {suc n} {suc m} (fs i) j   = Fin+N-inl≠inr i j ∘ fs-inj
  Fin+N-inl≠inr⁻¹ : ∀ {n m} i j → ¬ (Fin+N-inr {_} {m} j == Fin+N-inl {n} i)
  Fin+N-inl≠inr⁻¹ i j p = Fin+N-inl≠inr i j (p ⁻¹)
  Fin+N-inl-inj : ∀ {n m} → is-injective (Fin+N-inl {n} {m})
  Fin+N-inl-inj {suc n} {m} {fz} {fz} _         = =rf
  Fin+N-inl-inj {suc n} {m} {fs i} {fs i'} eq   = =ap fs (Fin+N-inl-inj (fs-inj eq))
  Fin+N-inr-inj : ∀ {n m} → is-injective (Fin+N-inr {n} {m})
  Fin+N-inr-inj {zero} {m} {i} {i'}       = id
  Fin+N-inr-inj {suc n} {m} {i} {i'} eq   = Fin+N-inr-inj (fs-inj eq)

  Fin+N-inlz : ∀ {n m} (n=n+m : n == n +N m)
                 → ∀ i → Fin+N-inl i == Fin-=to→ n=n+m i
  Fin+N-inlz {suc n} {m} sn=sn+m fz = Fin-=to→-fz sn=sn+m ⁻¹
  Fin+N-inlz {suc n} {m} sn=sn+m (fs i) = =proof
    fs (Fin+N-inl i)                       ==[ =ap fs (Fin+N-inlz (suc-inj sn=sn+m) i) ] /
    fs (Fin-=to→ (suc-inj sn=sn+m) i)     ==[ Fin-=to→-fs (suc-inj sn=sn+m) sn=sn+m i ]∎
    Fin-=to→ sn=sn+m (fs i) ∎
  Fin+N-inrz : ∀ {n m} (n=m+n : n == m +N n)
                 → ∀ i → Fin+N-inr i == Fin-=to→ n=m+n i
  Fin+N-inrz {n} {zero} n=m+n i =
    ●loop=idₚₜ Nat-isSet n=m+n i ⁻¹
  Fin+N-inrz {n} {suc m} n=sm+n i =
    N₀rec (PA4 (sum-rh-lh-zero (n=sm+n ⁻¹)))

{-
  Fin+N-inr-●l :  ∀ {n n' m} (eq : n == n')
                    → ∀ j → Fin-=to→ eq
-}

  Fin+N-inr-●sucswap : ∀ n m
                     → ∀ j → Fin-=to→ (+N-sucswap n m) (Fin+N-inr {n} (fs j))
                                      == Fin+N-inr {suc n} j
  Fin+N-inr-●sucswap zero m j = =rf
  Fin+N-inr-●sucswap (suc n) m j = =proof
    Fin-=to→ (=ap suc (+N-sucswap n m)) (fs (Fin+N-inr (fs j)))
      ==[ Fin-=to→-fs (+N-sucswap n m) (=ap suc (+N-sucswap n m)) (Fin+N-inr (fs j)) ⁻¹  ] /
    fs (Fin-=to→ (+N-sucswap n m) (Fin+N-inr (fs j)))
      ==[ =ap fs (Fin+N-inr-●sucswap n m j) ]∎
    fs (fs (Fin+N-inr j)) ∎
  Fin+N-inr-●sucswap⁻¹ : ∀ n m
                     → ∀ j → Fin-=to→ (+N-sucswap⁻¹ n m) (Fin+N-inr {suc n} j)
                                      == Fin+N-inr {n} (fs j)
  Fin+N-inr-●sucswap⁻¹ n m j = =proof
    Fin-=to→ (+N-sucswap⁻¹ n m) (Fin+N-inr j)
             ==[ =ap (Fin-=to→ (+N-sucswap⁻¹ n m)) (Fin+N-inr-●sucswap n m j) ⁻¹ ] /
    Fin-=to→ (+N-sucswap⁻¹ n m) (Fin-=to→ (+N-sucswap n m) (Fin+N-inr (fs j)))
             ==[ prj1 (pj2 inv) _ ]∎
    Fin+N-inr (fs j) ∎
    where inv : is-invrt (Fin-=to→ (+N-sucswap n m))
          inv = Fin-=to→-invrt (+N-sucswap n m)



  -- inclusion on the right given by order
  Fin-≤to→r : ∀ {n m} → n ≤N m → Fin n → Fin m
  Fin-≤to→r {n} {m} leq = Fin-=to→ eq ∘ Fin+N-inr {k} {n}
    where k : Nat
          k = pj1 (≤N-diff {n} leq)
          eq : k +N n == m
          eq = pj2 (≤N-diff {n} leq)

  -- triangles
  Fin+N-trl : ∀ {n m} {A : Set} → (lt : Fin n → A) → (rt : Fin m → A)
                → ∀ i → Fin+N-fnc lt rt (Fin+N-inl i) == lt i
  Fin+N-trl {suc n} lt rt fz          = =rf {a = lt fz}
  Fin+N-trl {suc n} lt rt (fs i)      = Fin+N-trl (lt ∘ fs) rt i

  Fin+N-trr : ∀ {n m} {A : Set} → (lt : Fin n → A) → (rt : Fin m → A)
                → ∀ i → Fin+N-fnc lt rt (Fin+N-inr i) == rt i
  Fin+N-trr {zero} lt rt i           = =rf {a = rt i}
  Fin+N-trr {suc n} lt rt i          = Fin+N-trr (lt ∘ fs) rt i

  -- induction
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
  Fin+N-fnc-eqv eqvf eqvg = invrt-is-eqv (Fin+N-fnc-invrt (equiv-is-invrt eqvf)
                                                          (equiv-is-invrt eqvg))

  -- splits a finite set before and after a given element

  is-FinSplit+N : ∀ {n} → Fin (suc n) → Nat × Nat → Set
  is-FinSplit+N {n} i nn = Σ[ (prj1 nn +N suc (prj2 nn) == suc n) ] ( λ y →
                            Fin-=to→ y (Fin+N-inr fz) == i )
  FinSplit+N : ∀ {n} → Fin (suc n) → Set
  FinSplit+N {n} i = Σ[ Nat × Nat ] (is-FinSplit+N i)
  Fin-splt+N-nl Fin-splt+N-nr : ∀ {n i} → FinSplit+N {n} i → Nat
  Fin-splt+N-nl fsp = prj1 (pj1 fsp)
  Fin-splt+N-nr fsp = prj2 (pj1 fsp)
  Fin-splt+N-eq : ∀ {n i} → (fsp : FinSplit+N {n} i) → Fin-splt+N-nl fsp +N suc (Fin-splt+N-nr fsp) == suc n
  Fin-splt+N-eq fsp = pj1 (pj2 fsp)
  Fin-splt+N-eqn : ∀ {n i} → (fsp : FinSplit+N {n} i) → Fin-splt+N-nl fsp +N Fin-splt+N-nr fsp == n
  Fin-splt+N-eqn fsp = suc-inj (+N-sucswap _ _ ⁻¹ • Fin-splt+N-eq fsp)
  Fin-splt+N-el : ∀ {n i} → (fsp : FinSplit+N {n} i)
                    → Fin-=to→ (Fin-splt+N-eq fsp) (Fin+N-inr fz) == i
  Fin-splt+N-el fsp = pj2 (pj2 fsp)

  Fin-splt+N-lmiss : ∀ {n i} → (fsp : FinSplit+N {n} i)
                       → ∀ j → ¬ (Fin-=to→ (Fin-splt+N-eq fsp) (Fin+N-inl {Fin-splt+N-nl fsp} j) == i)
  Fin-splt+N-lmiss {n} {i} fsp j eq =
    Fin+N-inl≠inr⁻¹ _ fz (invrt-is-injective (Fin-=to→-invrt (Fin-splt+N-eq fsp)) (Fin-splt+N-el fsp • eq ⁻¹))
  Fin-splt+N-rmiss : ∀ {n i} → (fsp : FinSplit+N {n} i)
                       → ∀ j → ¬ (Fin-=to→ (Fin-splt+N-eq fsp) (Fin+N-inr {Fin-splt+N-nl fsp} (fs j)) == i)
  Fin-splt+N-rmiss {n} {i} fsp j eq = PA4-Fin (auxinj (Fin-splt+N-el fsp • eq ⁻¹))
    where auxinj : is-injective (Fin-=to→ (Fin-splt+N-eq fsp) ∘ Fin+N-inr {Fin-splt+N-nl fsp})
          auxinj = injective-cmp Fin+N-inr-inj (invrt-is-injective (Fin-=to→-invrt (Fin-splt+N-eq fsp)))


  Fin+N-fsinr : ∀ {n l r} (e : l +N r == n) (se : suc l +N r == suc n)
       → ∀ j → (fs ∘ Fin-=to→ e ∘ Fin+N-inr {l} {r}) j == (Fin-=to→ se ∘ Fin+N-inr) j
  Fin+N-fsinr {n} {l} {r} e se j = =proof
    fs (Fin-=to→ e (Fin+N-inr {l} j))             ==[ Fin-=to→-fsap e _ ] /
    Fin-=to→ (=ap suc e) (fs (Fin+N-inr {l} j))   ==[ ●irrelₚₜ Nat-isSet (=ap suc e) se _ ]∎
    Fin-=to→ se (Fin+N-inr {suc l} j) ∎


  module FinSplit+N {n : Nat} {i : Fin (suc n)} (fsp : FinSplit+N i) where
    nl nr : Nat
    nl = Fin-splt+N-nl fsp
    nr = Fin-splt+N-nr fsp
    eq : nl +N suc nr == suc n
    eq = Fin-splt+N-eq fsp
    eqn : nl +N nr == n
    eqn = Fin-splt+N-eqn fsp
    el : Fin-=to→ eq (Fin+N-inr fz) == i
    el = Fin-splt+N-el fsp    
  -- end FinSplit+N


  -- it is a set. In fact, it is contractible (see below)
  is-FinSplit+N-isProp : ∀ {n} i nn → isProp (is-FinSplit+N {n} i nn)
  is-FinSplit+N-isProp i nn = Σpp-is-prop Nat-isSet (λ _ → Fin-isSet _)
  FinSplit+N-isSet : ∀ {n} i → isSet (FinSplit+N {n} i)
  FinSplit+N-isSet {n} i = Σsp-is-set (×ss-is-set Nat-isSet Nat-isSet)
                                      (is-FinSplit+N-isProp i)

  -- splittings can be lifted and restricted along fs
  liftFin-splt+N : ∀ {n} (i : Fin (suc n)) → FinSplit+N i → FinSplit+N (fs i)
  liftFin-splt+N {n} i fsp =
    (suc fsp.nl , fsp.nr)
    ,, =ap suc fsp.eq
       ,, (=proof Fin-=to→ (=ap suc fsp.eq) (fs (Fin+N-inr fz))
                                                          ==[ Fin-=to→-fsap fsp.eq _ ⁻¹ ] /
                  fs (Fin-=to→ fsp.eq (Fin+N-inr fz))             ==[ =ap fs fsp.el ]∎
                  fs i ∎)
    where module fsp = FinSplit+N fsp


  restrFin-splt+N : ∀ {n} (i : Fin (suc n)) → (fsp : FinSplit+N (fs i))
                      → Σ[ FinSplit+N i ] (λ x →
                          suc (Fin-splt+N-nl x) == Fin-splt+N-nl fsp)
  restrFin-splt+N {n} i fsp =
    ((nk , fsp.nr)
     ,, k+sr=sn ,, elk)
    ,, pj2 sk=nl
    where module fsp = FinSplit+N fsp
          z≠nl : ¬ (zero == fsp.nl)
          z≠nl z=nl = PA4-Fin (=proof
            fz
                                               ==[ Fin-=to→-fz (+N-idlg⁻¹ z=nl • fsp.eq) ⁻¹ ] /
            Fin-=to→ (+N-idlg⁻¹ z=nl • fsp.eq) fz
                                                         ==[ =transp-•-ptw⁻¹ Fin _ fsp.eq fz ] /
            Fin-=to→ fsp.eq (Fin-=to→ (+N-idlg⁻¹ z=nl) fz)
                              ==[ =ap (Fin-=to→ fsp.eq) (Fin+N-inrz (+N-idlg⁻¹ z=nl) fz) ⁻¹ ] /
            Fin-=to→ fsp.eq (Fin+N-inr fz)
                                                                               ==[ fsp.el ]∎
            fs i ∎)
          sk=nl : Σ[ Nat ] (λ x → suc x == fsp.nl)
          sk=nl = [ (λ z=nl → N₀rec (z≠nl z=nl)) ∣ id ] (Nat-dicot fsp.nl)
          nk : Nat
          nk = pj1 sk=nl
          k+sr=sn : nk +N suc fsp.nr == suc n
          k+sr=sn = =proof
            pj1 sk=nl +N suc fsp.nr      ==[ +N-sucswap _ _ ] /
            suc (pj1 sk=nl) +N fsp.nr    ==[ =ap (_+N fsp.nr) (pj2 sk=nl) ] /
            fsp.nl +N fsp.nr                 ==[ fsp.eqn ]∎
            suc n ∎
          elk : Fin-=to→ k+sr=sn (Fin+N-inr {nk} fz) == i
          elk = fs-inj (=proof
            fs (Fin-=to→ k+sr=sn (Fin+N-inr {nk} fz))
                  ==[ Fin+N-fsinr k+sr=sn (=ap (_+N suc fsp.nr) (pj2 sk=nl) • fsp.eq) fz ] /
            Fin-=to→ (=ap (_+N suc fsp.nr) (pj2 sk=nl) • fsp.eq) (fs (Fin+N-inr fz))
              ==[ =transp-•-ptw⁻¹ Fin  (=ap (_+N suc fsp.nr) (pj2 sk=nl)) (fsp.eq) _ ] /
            (Fin-=to→ fsp.eq ∘ Fin-=to→ (=ap (_+N suc fsp.nr) (pj2 sk=nl))) (Fin+N-inr {suc nk} fz)
                      ==[ =ap (Fin-=to→ fsp.eq) (=proof
              Fin-=to→ (=ap (_+N suc fsp.nr) (pj2 sk=nl)) (Fin+N-inr {suc nk} fz)
                       ==[ ●=ap-is-● Fin (_+N suc fsp.nr) (pj2 sk=nl) _ ] /
              =transp (Fin ∘' _+N suc fsp.nr) (pj2 sk=nl) (Fin+N-inr {suc nk} fz)
                      ==[ =transp-is-nat {B = λ _ → Fin (suc fsp.nr)} {Fin} {_+N suc fsp.nr}
                               (λ {x} → Fin+N-inr {x} {suc fsp.nr}) (pj2 sk=nl) fz ] /
              Fin+N-inr {fsp.nl} (=transp (λ _ → Fin (suc fsp.nr)) (pj2 sk=nl) fz)
                        ==[ =ap (Fin+N-inr {fsp.nl}) (=transpcnst _ (pj2 sk=nl) fz) ]∎
              Fin+N-inr {fsp.nl} fz ∎) ] /
            Fin-=to→ fsp.eq (Fin+N-inr {fsp.nl} fz)
                      ==[ fsp.el ]∎
            fs i ∎)

  -- the (unique) splitting, and functions above instantiated
  splt+N-Fin : ∀ {n} (i : Fin (suc n)) → FinSplit+N i
  splt+N-Fin {zero} i =              (zero , zero) ,, =rf ,, N₁-isProp fz i
  splt+N-Fin {suc n} fz =            (zero , suc n) ,, =rf ,, =rf
  splt+N-Fin {suc n} (fs i) =        liftFin-splt+N i (splt+N-Fin i)
  module splt+N-Fin {n} (i : Fin (suc n)) = FinSplit+N (splt+N-Fin i)

  -- FinSplit+N is contractible
  
  FinSplit+N-isContr-pf : ∀ {n} (i : Fin (suc n)) (fsp : FinSplit+N i)
                            → splt+N-Fin i == fsp
  FinSplit+N-isContr-pf {zero} i fsp =
    =Σchar (=×char (sum-0-is-0 (Fin-splt+N-eqn fsp)) (sum-0-is-0' (Fin-splt+N-eqn fsp)))
           (is-FinSplit+N-isProp i (pj1 fsp) _ _)
  FinSplit+N-isContr-pf {suc n} fz fsp =
    =Σchar (=×char z=nl sn=nr)
           (is-FinSplit+N-isProp fz (pj1 fsp) _ _)
    where z=nl : zero == Fin-splt+N-nl fsp
          z=nl = [ id
                 ∣ (λ z → N₀rec (Fin-splt+N-lmiss fsp (Fin-=to→ (pj2 z) fz)
                                                      (=proof
                   Fin-=to→ (Fin-splt+N-eq fsp) (Fin+N-inl (Fin-=to→ (pj2 z) fz))
                         ==[ =ap (Fin-=to→ (Fin-splt+N-eq fsp)) (=proof
                     Fin+N-inl (Fin-=to→ (pj2 z) fz)
                       ==[ =transp-is-nat⁻¹ {B = Fin} {Fin} {_+N suc (Fin-splt+N-nr fsp)}
                                            (λ {x} → Fin+N-inl {x} {_}) (pj2 z) fz ] /
                     ((λ x → Fin (x +N suc (Fin-splt+N-nr fsp))) ● pj2 z)
                           (Fin+N-inl {suc (pj1 z)} fz)
                           ==[ ●=ap-is-●⁻¹ Fin (_+N suc (Fin-splt+N-nr fsp)) (pj2 z) fz ]∎
                     Fin-=to→ (=ap (_+N suc (Fin-splt+N-nr fsp)) (pj2 z)) fz ∎) ] /
                   Fin-=to→ (Fin-splt+N-eq fsp)
                             (Fin-=to→ (=ap (_+N suc (Fin-splt+N-nr fsp)) (pj2 z))
                                        fz)
                            ==[ =transp-•-ptw Fin _ (Fin-splt+N-eq fsp) fz ] /
                   Fin-=to→ (=ap (_+N suc (Fin-splt+N-nr fsp)) (pj2 z) • Fin-splt+N-eq fsp)
                             fz
                           ==[ Fin-=to→-fz (_ • Fin-splt+N-eq fsp) ]∎
                      fz ∎)))
                 ] (Nat-dicot (Fin-splt+N-nl fsp))
          sn=nr : suc n == Fin-splt+N-nr fsp
          sn=nr = =proof
            suc n                                     ==[ Fin-splt+N-eqn fsp ⁻¹ ] /
            Fin-splt+N-nl fsp +N Fin-splt+N-nr fsp    ==[ +N-idlg z=nl ]∎
            Fin-splt+N-nr fsp ∎
  FinSplit+N-isContr-pf {suc n} (fs i) fsp =
    =Σchar (=×char leq req)
           (=Σchar (Nat-isSet _ _) (Fin-isSet _ _ _))
    where rfsp : FinSplit+N i
          rfsp = pj1 (restrFin-splt+N i fsp)
          ih : splt+N-Fin i == rfsp
          ih = FinSplit+N-isContr-pf i _
          req : splt+N-Fin.nr i == Fin-splt+N-nr fsp
          req = splt+N-Fin.nr i       ==[ =prj2 (=pj1 ih) ]
                Fin-splt+N-nr rfsp
          leq : suc (splt+N-Fin.nl i) == Fin-splt+N-nl fsp
          leq = =proof
            suc (splt+N-Fin.nl i)
                               ==[ =ap suc (=prj1 (=pj1 ih)) ] /
            suc (Fin-splt+N-nl rfsp)
                               ==[ pj2 (restrFin-splt+N i fsp) ]∎
            Fin-splt+N-nl fsp ∎

  FinSplit+N-isContr : ∀ {n} (i : Fin (suc n)) → isContr (FinSplit+N i)
  FinSplit+N-isContr i = splt+N-Fin i ,, λ s → FinSplit+N-isContr-pf i s ⁻¹


  -- induction with arbitrary base element

  Fin+Ns-ind : ∀ {nl nr} (C : Fin (nl +N suc nr) → Set)
                     → (cel : C (Fin+N-inr fz))
                     → (cl : (j : Fin nl) → C (Fin+N-inl j))
                     → (cr : (j : Fin nr) → C (Fin+N-inr (fs j)))
                       → ∀ j → C j
  Fin+Ns-ind {nl} {nr} C cel cl cr = Fin+N-ind C cl (Fin-ind _ cel cr)
  Fin+Ns-indel : ∀ {nl nr} {C : Fin (nl +N suc nr) → Set}
                     → (cel : C (Fin+N-inr fz))
                     → (cl : (j : Fin nl) → C (Fin+N-inl j))
                     → (cr : (j : Fin nr) → C (Fin+N-inr (fs j)))
                       → Fin+Ns-ind C cel cl cr (Fin+N-inr fz) == cel
  Fin+Ns-indel cel cl cr = Fin+N-indr cl (Fin-ind _ cel cr) fz
  Fin+Ns-indl : ∀ {nl nr} {C : Fin (nl +N suc nr) → Set}
                     → (cel : C (Fin+N-inr fz))
                     → (cl : (j : Fin nl) → C (Fin+N-inl j))
                     → (cr : (j : Fin nr) → C (Fin+N-inr (fs j)))
                       → ∀ j → Fin+Ns-ind C cel cl cr (Fin+N-inl j) == cl j
  Fin+Ns-indl cel cl cr j = Fin+N-indl cl (Fin-ind _ cel cr) j
  Fin+Ns-indr : ∀ {nl nr} {C : Fin (nl +N suc nr) → Set}
                     → (cel : C (Fin+N-inr fz))
                     → (cl : (j : Fin nl) → C (Fin+N-inl j))
                     → (cr : (j : Fin nr) → C (Fin+N-inr (fs j)))
                       → ∀ j → Fin+Ns-ind C cel cl cr (Fin+N-inr (fs j)) == cr j
  Fin+Ns-indr cel cl cr j = Fin+N-indr cl (Fin-ind _ cel cr) (fs j)

  -- induction with base element from a splitting
  Fin-splt+N-ind : ∀ {n} (C : Fin (suc n) → Set) (i : Fin (suc n)) (fsp : FinSplit+N i)
                     → (cel : C i)
                     → (cl : (j : Fin (Fin-splt+N-nl fsp)) → C (Fin-=to→ (Fin-splt+N-eq fsp) (Fin+N-inl j)))
                     → (cr : (j : Fin (Fin-splt+N-nr fsp)) → C (Fin-=to→ (Fin-splt+N-eq fsp) (Fin+N-inr (fs j))))
                       → ∀ j → C j 
  Fin-splt+N-ind C i fsp cel cl cr j =
    (C ● idcod j) (Fin+Ns-ind (C ∘' Fin-=to→ (Fin-splt+N-eq fsp))
                              ((C ● Fin-splt+N-el fsp ⁻¹) cel)
                              cl
                              cr
                              (Fin-=to→ (Fin-splt+N-eq fsp ⁻¹) j))
    where idcod : ∀ j → Fin-=to→ (Fin-splt+N-eq fsp) (Fin-=to→ (Fin-splt+N-eq fsp ⁻¹) j) == j
          idcod = prj2 (pj2 (Fin-=to→-invrt (Fin-splt+N-eq fsp)))

  Fin-splt+N-ind-comp : ∀ {n} {C : Fin (suc n) → Set} {i : Fin (suc n)} (fsp : FinSplit+N i)
                          → (cel : C i)
                          → (cl : (j : Fin (Fin-splt+N-nl fsp)) → C (Fin-=to→ (Fin-splt+N-eq fsp) (Fin+N-inl j)))
                          → (cr : (j : Fin (Fin-splt+N-nr fsp)) → C (Fin-=to→ (Fin-splt+N-eq fsp) (Fin+N-inr (fs j))))
                            →  (Fin-splt+N-ind C i fsp cel cl cr i == cel)
                                × (∀ j → Fin-splt+N-ind C i fsp cel cl cr (Fin-=to→ (Fin-splt+N-eq fsp) (Fin+N-inl j)) == cl j)
                                × (∀ j → Fin-splt+N-ind C i fsp cel cl cr (Fin-=to→ (Fin-splt+N-eq fsp) (Fin+N-inr (fs j))) == cr j)
  Fin-splt+N-ind-comp {n} {C} {i} fsp cel cl cr =
    (=proof Fin-splt+N-ind C i fsp cel cl cr i
                           ==[ =apd (Fin-splt+N-ind C i fsp cel cl cr) (Fin-splt+N-el fsp) ⁻¹ ] /
            (C ● Fin-splt+N-el fsp) (Fin-splt+N-ind C i fsp cel cl cr (Fin-=to→ (Fin-splt+N-eq fsp) (Fin+N-inr fz)))
                       ==[ =ap (C ● Fin-splt+N-el fsp) (=proof
               _           ==[ aux (Fin+N-inr fz) ] /
               Fin+Ns-ind (C ∘' Fin-=to→ (Fin-splt+N-eq fsp)) ((C ● Fin-splt+N-el fsp ⁻¹) cel) cl cr (Fin+N-inr fz)
                           ==[ Fin+Ns-indel _ cl cr ]∎
               (C ● Fin-splt+N-el fsp ⁻¹) cel ∎) ] /
            (C ● Fin-splt+N-el fsp) ((C ● Fin-splt+N-el fsp ⁻¹) cel)
                           ==[ =transp-back-forth-ptw C (Fin-splt+N-el fsp) cel ]∎
            cel ∎)
    , (λ j → =proof
         Fin-splt+N-ind C i fsp cel cl cr (Fin-=to→ (Fin-splt+N-eq fsp) (Fin+N-inl j))
                            ==[ aux (Fin+N-inl j) ] /
         Fin+Ns-ind (C ∘' Fin-=to→ (Fin-splt+N-eq fsp)) ((C ● Fin-splt+N-el fsp ⁻¹) cel) cl cr (Fin+N-inl j)
                            ==[ Fin+Ns-indl ((C ● (Fin-splt+N-el fsp ⁻¹)) cel) cl cr j ]∎
         cl j ∎ )
    , λ j → =proof
         Fin-splt+N-ind C i fsp cel cl cr (Fin-=to→ (Fin-splt+N-eq fsp) (Fin+N-inr (fs j)))
                            ==[ aux (Fin+N-inr (fs j)) ] /
         Fin+Ns-ind (C ∘' Fin-=to→ (Fin-splt+N-eq fsp)) ((C ● Fin-splt+N-el fsp ⁻¹) cel) cl cr (Fin+N-inr (fs j))
                            ==[ Fin+Ns-indr ((C ● (Fin-splt+N-el fsp ⁻¹)) cel) cl cr j ]∎
         cr j ∎
    where iddom : ∀ j → Fin-=to→ (Fin-splt+N-eq fsp ⁻¹) (Fin-=to→ (Fin-splt+N-eq fsp) j) == j
          iddom = prj1 (pj2 (Fin-=to→-invrt (Fin-splt+N-eq fsp)))
          idcod : ∀ j → Fin-=to→ (Fin-splt+N-eq fsp) (Fin-=to→ (Fin-splt+N-eq fsp ⁻¹) j) == j
          idcod = prj2 (pj2 (Fin-=to→-invrt (Fin-splt+N-eq fsp)))
          aux : ∀ j → Fin-splt+N-ind C i fsp cel cl cr (Fin-=to→ (Fin-splt+N-eq fsp) j)
                         == Fin+Ns-ind (C ∘' Fin-=to→ (Fin-splt+N-eq fsp)) ((C ● Fin-splt+N-el fsp ⁻¹) cel) cl cr j
          aux j = =proof
            Fin-splt+N-ind C i fsp cel cl cr (Fin-=to→ (Fin-splt+N-eq fsp) j)
                            ==[ =ap (C ● idcod _) (=proof
              (Fin+Ns-ind (C ∘' Fin-=to→ (Fin-splt+N-eq fsp)) ((C ● Fin-splt+N-el fsp ⁻¹) cel) cl cr
                             (Fin-=to→ (Fin-splt+N-eq fsp ⁻¹) (Fin-=to→ (Fin-splt+N-eq fsp) j)))
                            ==[ =transp-flip (C ∘' Fin-=to→ (Fin-splt+N-eq fsp)) (iddom _)
                                                 (=apd (Fin+Ns-ind _ ((C ● Fin-splt+N-el fsp ⁻¹) cel) cl cr) (iddom _)) ] /
              ((C ∘' Fin-=to→ (Fin-splt+N-eq fsp)) ● (iddom _ ⁻¹))
               (Fin+Ns-ind (C ∘' Fin-=to→ (Fin-splt+N-eq fsp)) ((C ● Fin-splt+N-el fsp ⁻¹) cel) cl cr j)
                            ==[ ●=ap-is-●⁻¹ C (Fin-=to→ (Fin-splt+N-eq fsp)) (iddom _ ⁻¹) _ ]∎
              (C ● =ap (Fin-=to→ (Fin-splt+N-eq fsp)) (iddom _ ⁻¹)) _ ∎) ] /
            (C ● idcod _) ((C ● =ap (Fin-=to→ (Fin-splt+N-eq fsp)) (iddom _ ⁻¹)) _)
                            ==[ =transp-•-ptw C (=ap (Fin-=to→ (Fin-splt+N-eq fsp)) (iddom _ ⁻¹)) (idcod _) _ ] /
            (C ● (=ap (Fin-=to→ (Fin-splt+N-eq fsp)) (iddom _ ⁻¹) • idcod _)) _
                            ==[ =transp-ext-ptw C (Fin-isSet _ (=ap (Fin-=to→ (Fin-splt+N-eq fsp)) (iddom _ ⁻¹) • idcod _) =rf) _ ]∎
            Fin+Ns-ind (C ∘' Fin-=to→ (Fin-splt+N-eq fsp)) ((C ● Fin-splt+N-el fsp ⁻¹) cel) cl cr j ∎

  -- induction for the unique splitting  
  splt+N-Fin-ind : ∀ {n} (C : Fin (suc n) → Set) (i : Fin (suc n))
                     → (cel : C i)
                     → (cl : (j : Fin (splt+N-Fin.nl i)) → C (Fin-=to→ (splt+N-Fin.eq i) (Fin+N-inl j)))
                     → (cr : (j : Fin (splt+N-Fin.nr i)) → C (Fin-=to→ (splt+N-Fin.eq i) (Fin+N-inr (fs j))))
                       → ∀ j → C j
  splt+N-Fin-ind C i = Fin-splt+N-ind C i (splt+N-Fin i)

  splt+N-Fin-ind-comp : ∀ {n} (C : Fin (suc n) → Set) {i : Fin (suc n)}
                          → (cel : C i)
                          → (cl : (j : Fin (splt+N-Fin.nl i)) → C (Fin-=to→ (splt+N-Fin.eq i) (Fin+N-inl j)))
                          → (cr : (j : Fin (splt+N-Fin.nr i)) → C (Fin-=to→ (splt+N-Fin.eq i) (Fin+N-inr (fs j))))
                            →  (splt+N-Fin-ind C i cel cl cr i == cel)
                                × (∀ j → splt+N-Fin-ind C i cel cl cr (Fin-=to→ (splt+N-Fin.eq i) (Fin+N-inl j)) == cl j)
                                × (∀ j → splt+N-Fin-ind C i cel cl cr (Fin-=to→ (splt+N-Fin.eq i) (Fin+N-inr (fs j))) == cr j)
  splt+N-Fin-ind-comp C {i = i} = Fin-splt+N-ind-comp (splt+N-Fin i)
      


  -- function that misses an element (face map)
  
  is-faceFinSplit : ∀ {n} → (i : Fin (suc n)) (fsp : FinSplit+N i)
                      → (Fin n → Fin (suc n)) → Set
  is-faceFinSplit {n} i fsp f =
             (∀ j → ¬ (f j == i))
             × (∀ j → (f ∘ Fin-=to→ (Fin-splt+N-eqn fsp) ∘ Fin+N-inl {Fin-splt+N-nl fsp}) j
                                    == (Fin-=to→ (Fin-splt+N-eq fsp) ∘ Fin+N-inl) j)
             × (∀ j → (f ∘ Fin-=to→ (Fin-splt+N-eqn fsp) ∘ Fin+N-inr) j
                                    == (Fin-=to→ (Fin-splt+N-eq fsp) ∘ Fin+N-inr ∘ fs) j)
  module is-faceFinSplit {n i} (fsp : FinSplit+N {n} i)
                         {f} (isfc : is-faceFinSplit i fsp f)
                         where
    miss : ∀ j → ¬ (f j == i)
    miss = prj1 isfc
    left : ∀ j → (f ∘ Fin-=to→ (Fin-splt+N-eqn fsp) ∘ Fin+N-inl {Fin-splt+N-nl fsp}) j
                                    == (Fin-=to→ (Fin-splt+N-eq fsp) ∘ Fin+N-inl) j
    left = prj1 (prj2 isfc)
    right : ∀ j → (f ∘ Fin-=to→ (Fin-splt+N-eqn fsp) ∘ Fin+N-inr) j
                                    == (Fin-=to→ (Fin-splt+N-eq fsp) ∘ Fin+N-inr ∘ fs) j
    right = prj2 (prj2 isfc)



  faceFin-fun : ∀ {n} → (i : Fin (suc n)) → Fin n → Fin (suc n)
  faceFin-fun fz =                       fs
  faceFin-fun {suc n} (fs i) fz =        fz
  faceFin-fun {suc n} (fs i) (fs j) =    fs (faceFin-fun i j)

  faceFin : ∀ {n} → (i : Fin (suc n))
                → is-faceFinSplit i (splt+N-Fin i) (faceFin-fun i)
  faceFin {zero} i =
    (λ j _ → j) , (λ j → N₀rec j) , λ j → N₀rec j
  faceFin {suc n} fz =
    (λ j → PA4-Fin⁻¹ {i = j}) , (λ j → N₀rec j) , λ _ → =rf
  faceFin {suc n} (fs i) =
    miss , left , right
    where module i = splt+N-Fin i
          module ii = FinSplit+N (splt+N-Fin (fs i))
          ih : is-faceFinSplit i (splt+N-Fin i) (faceFin-fun i)
          ih = faceFin i
          miss : ∀ j → ¬ (faceFin-fun (fs i) j == fs i)
          miss fz = PA4-Fin {i = i}
          miss (fs j) eq = prj1 ih j (fs-inj eq)

          left : (j : Fin (suc i.nl)) → faceFin-fun (fs i) (Fin-=to→ ii.eqn (Fin+N-inl j))
                                            == Fin-=to→ (=ap suc i.eq) (Fin+N-inl j)
          left fz = =proof
            faceFin-fun (fs i) (Fin-=to→ ii.eqn fz)
            ==[ =ap (faceFin-fun (fs i)) (Fin-=to→-fz ii.eqn) ] /
            fz
            ==[ Fin-=to→-fz (=ap suc i.eq) ⁻¹ ]∎
            Fin-=to→ (=ap suc i.eq) fz ∎
          left (fs j) = =proof
            faceFin-fun (fs i) (Fin-=to→ ii.eqn (fs (Fin+N-inl j)))
                          ==[ =ap (faceFin-fun (fs i)) (Fin-=to→-fs i.eqn ii.eqn _ ⁻¹) ] /
            faceFin-fun (fs i) (fs (Fin-=to→ i.eqn (Fin+N-inl j)))
                                                   ==[ =ap fs (prj1 (prj2 ih) j) ] /
            fs (Fin-=to→ i.eq (Fin+N-inl j))
                                                ==[ Fin-=to→-fs i.eq (=ap suc i.eq) _ ]∎
            Fin-=to→ (=ap suc i.eq) (fs (Fin+N-inl j)) ∎

          right : (j : Fin ii.nr) → faceFin-fun (fs i) (Fin-=to→ ii.eqn (fs (Fin+N-inr j)))
                                        == Fin-=to→ (=ap suc i.eq) (fs (Fin+N-inr (fs j)))
          right j = =proof
            faceFin-fun (fs i) (Fin-=to→ ii.eqn (fs (Fin+N-inr j)))
                          ==[ =ap (faceFin-fun (fs i)) (Fin-=to→-fs i.eqn ii.eqn _ ⁻¹) ] /
            faceFin-fun (fs i) (fs (Fin-=to→ i.eqn (Fin+N-inr j)))
                                                   ==[ =ap fs (prj2 (prj2 ih) j) ] /
            fs (Fin-=to→ i.eq (Fin+N-inr (fs j)))
                                                ==[ Fin-=to→-fs i.eq (=ap suc i.eq) _ ]∎
            Fin-=to→ (=ap suc i.eq) (fs (Fin+N-inr (fs j))) ∎
  module faceFin {n} (i : Fin (suc n)) = is-faceFinSplit (splt+N-Fin i) (faceFin i)


  faceFin-inj : ∀ {n} → (i : Fin (suc n)) → is-injective (faceFin-fun i)
  faceFin-inj fz =                                fs-inj
  faceFin-inj {suc n} (fs i) {fz} {fz} eq =       =rf
  faceFin-inj {suc n} (fs i) {fs j} {fs j'} eq =  =ap fs (faceFin-inj i (fs-inj eq))
  faceFin-idfull : ∀ {n} (i : Fin (suc n)) → is-idfull (faceFin-fun i)
  faceFin-idfull i = inj-set-is-idfull (Fin-isSet _) (faceFin-inj i)

  faceFin-img : ∀ {n} (i : Fin (suc n))
                → ∀ {j} → ¬ (j == i) → fib (faceFin-fun i) j
  faceFin-img {zero} i {j} j≠i =                N₀ind (j≠i (N₁-isProp j i))
  faceFin-img {suc n} fz {j} j≠z =              Fin-dicotfs j (λ x → j≠z (x ⁻¹))
  faceFin-img {suc n} (fs i) {fz} z≠si =        fz ,, =rf
  faceFin-img {suc n} (fs i) {fs j} sj≠si =     fs (pj1 ih) ,, =ap fs (pj2 ih)
    where ih : Σ[ Fin n ] (λ x → faceFin-fun i x == j)
          ih = faceFin-img i {j} (λ x → sj≠si (=ap fs x))

  faceFin-dicot : ∀ {n} (i : Fin (suc n))
                    → ∀ j → (i == j) + Σ[ Fin n ] (λ x → faceFin-fun i x == j)
  faceFin-dicot i j = [ (inl ∘ _⁻¹) ∣ inr ∘ faceFin-img i ] (Fin-is-decid j i)



  -- restriction of a function missing an element

  faceFin-restr : ∀ {n m} (f : Fin n → Fin (suc m)) (i : Fin (suc m))
                    → (∀ j → ¬ (f j == i))
                      → Fin n → Fin m
  faceFin-restr {n} {m} f i f≠i j = pj1 (faceFin-img i (f≠i j))

  faceFin-restr-tr : ∀ {n m} {f : Fin n → Fin (suc m)} (i : Fin (suc m))
                       → (f≠i : ∀ j → ¬ (f j == i))
                         → ∀ j → (faceFin-fun i ∘ faceFin-restr f i f≠i) j == f j
  faceFin-restr-tr i f≠i j = pj2 (faceFin-img i (f≠i j))

  faceFin-restr-inj : ∀ {n m} {f : Fin n → Fin (suc m)} {i : Fin (suc m)}
                        → (f≠i : ∀ j → ¬ (f j == i)) → is-injective f
                          → is-injective (faceFin-restr f i f≠i)
  faceFin-restr-inj {f = f} {i} f≠i finj = 
    injective-tr {f = faceFin-restr f i f≠i} {faceFin-fun i} {f}
                 (λ {j} → faceFin-restr-tr i f≠i j)
                 finj

  faceFin-restr-precmp : ∀ {n m k} (g : Fin k → Fin n) {f : Fin n → Fin (suc m)}
                         (i : Fin (suc m)) (miss : ∀ j → ¬ (f j == i))
                             →  ∀ j → faceFin-restr (f ∘ g) i (λ x → miss (g x)) j == faceFin-restr f i miss (g j)
  faceFin-restr-precmp  g {f} i miss j = faceFin-inj i (=proof
    faceFin-fun i (faceFin-restr (f ∘ g) i (λ x → miss (g x)) j)
                  ==[ faceFin-restr-tr i  (λ x → miss (g x)) j ] /
    f (g j)
                  ==[ faceFin-restr-tr i miss (g j) ⁻¹ ]∎
    faceFin-fun i (faceFin-restr f i miss (g j)) ∎)

  faceFin-restr-ext : ∀ {n m} {f f' : Fin n → Fin (suc m)} (i : Fin (suc m))
                      (miss : ∀ j → ¬ (f j == i)) (miss' : ∀ j → ¬ (f' j == i))
                        → (∀ j → f j == f' j)
                          →  ∀ j → faceFin-restr f i miss j == faceFin-restr f' i miss' j
  faceFin-restr-ext {f = f} {f'} i miss miss' f=f' j = faceFin-inj i (=proof
    faceFin-fun i (faceFin-restr f i miss j)
                  ==[ faceFin-restr-tr i miss j ] /
    f j
                  ==[ f=f' j ] /
    f' j
                  ==[ faceFin-restr-tr i miss' j ⁻¹ ]∎
    faceFin-fun i (faceFin-restr f' i miss' j) ∎)

  -- removing an element from the image of an injective function

  faceFin-restrinj : ∀ {n m} (f : Fin (suc n) → Fin (suc m))
                      → is-injective f → (i : Fin (suc n)) → Fin n → Fin m
  faceFin-restrinj f finj i = faceFin-restr (f ∘ faceFin-fun i) (f i) fj≠fi
    where fj≠fi : ∀ j → ¬ (f (faceFin-fun i j) == f i)
          fj≠fi j ff=fi = faceFin.miss i j (finj ff=fi)

  faceFin-restrinj-tr : ∀ {n m} {f : Fin (suc n) → Fin (suc m)}
                       → (finj : is-injective f) → (i : Fin (suc n))
                         → ∀ j → (faceFin-fun (f i) ∘ faceFin-restrinj f finj i) j == (f ∘ faceFin-fun i) j
  faceFin-restrinj-tr {f = f} finj i = faceFin-restr-tr (f i) fj≠fi
    where fj≠fi : ∀ j → ¬ (f (faceFin-fun i j) == f i)
          fj≠fi j ff=fi = faceFin.miss i j (finj ff=fi)

  faceFin-restrinj-inj : ∀ {n m} {f : Fin (suc n) → Fin (suc m)}
                        → (finj : is-injective f) → (i : Fin (suc n))
                          → is-injective (faceFin-restrinj f finj i)
  faceFin-restrinj-inj {f = f} finj i =
    faceFin-restr-inj {f = f ∘ faceFin-fun i} fj≠fi (injective-cmp (faceFin-inj i) finj)
    where fj≠fi : ∀ j → ¬ (f (faceFin-fun i j) == f i)
          fj≠fi j ff=fi = faceFin.miss i j (finj ff=fi)

  faceFin-restrinj-=pt :  ∀ {n m} {f : Fin (suc n) → Fin (suc m)}
                            (finj : is-injective f) {i i' : Fin (suc n)}
                              → i == i' → ∀ j → faceFin-restrinj f finj i j == faceFin-restrinj f finj i' j
  faceFin-restrinj-=pt {f = f} finj i=i' j = =ap (λ x → faceFin-restrinj f finj x j) i=i' 

  faceFin-restrinj-id :  ∀ {n} (i : Fin (suc n))
                           → ∀ j → faceFin-restrinj id id i j == j
  faceFin-restrinj-id i j = faceFin-inj i (faceFin-restrinj-tr id i j)

  faceFin-restrinj-cmp-rf :  ∀ {n m k} {f : Fin (suc n) → Fin (suc m)} {g : Fin (suc m) → Fin (suc k)}
                             (finj : is-injective f) (ginj : is-injective g) (i : Fin (suc n))
                               → ∀ j → faceFin-restrinj g ginj (f i) (faceFin-restrinj f finj i j)
                                                  == faceFin-restrinj (g ∘ f) (finj ∘ ginj) i j
  faceFin-restrinj-cmp-rf {f = f} {g} finj ginj i j = faceFin-inj (g (f i)) (=proof
    faceFin-fun (g (f i)) (faceFin-restrinj g ginj (f i) (faceFin-restrinj f finj i j))
                                                           ==[ faceFin-restrinj-tr ginj (f i) _ ] /
    (g ∘ faceFin-fun (f i) ∘ faceFin-restrinj f finj i) j
                                                           ==[ =ap g (faceFin-restrinj-tr finj i j) ] /
    (g ∘ f ∘ faceFin-fun i) j
                                                           ==[ faceFin-restrinj-tr (finj ∘ ginj) i j ⁻¹ ]∎
    faceFin-fun (g (f i)) (faceFin-restrinj (g ∘ f) (finj ∘ ginj) i j) ∎)

  faceFin-restrinj-ext :  ∀ {n m} {f f' : Fin (suc n) → Fin (suc m)}
                            (finj : is-injective f) (finj' : is-injective f') (i : Fin (suc n))
                              → (∀ j → f j == f' j)
                                → ∀ j → faceFin-restrinj f finj i j == faceFin-restrinj f' finj' i j
  faceFin-restrinj-ext {f = f} {f'} finj finj' i f=f' j = faceFin-inj (f i) (=proof
    faceFin-fun (f i) (faceFin-restrinj f finj i j)
                                                      ==[ faceFin-restrinj-tr finj i j ] /
    f (faceFin-fun i j)
                                                      ==[ f=f' _ ] /
    f' (faceFin-fun i j)
                                                      ==[ faceFin-restrinj-tr finj' i j ⁻¹ ] /
    faceFin-fun (f' i) (faceFin-restrinj f' finj' i j)
                                                      ==[ =ap (λ x → faceFin-fun x _) (f=f' i ⁻¹) ]∎
    faceFin-fun (f i) (faceFin-restrinj f' finj' i j) ∎)
  
  faceFin-restrinj-invrt : ∀ {n m} {f : Fin (suc n) → Fin (suc m)}
                             (finj : is-injective f) (i : Fin (suc n))
                               → is-invrt f → is-invrt (faceFin-restrinj f finj i)
  faceFin-restrinj-invrt {n} {m} {f} finj i finv =
    faceFin-restrinj g ginj (f i)
    ,, (lft , rgt)
    where g : Fin (suc m) → Fin (suc n)
          g = pj1 finv
          ginv : is-invrt g
          ginv = f ,, (prj2 (pj2 finv) , prj1 (pj2 finv))
          ginj : is-injective g
          ginj = invrt-is-injective ginv
          rstf : Fin n → Fin m
          rstf = faceFin-restrinj f finj fz
          rstg : Fin m → Fin n
          rstg = faceFin-restrinj g ginj (f fz)
          lft : (j : Fin n) → faceFin-restrinj g ginj (f i) (faceFin-restrinj f finj i j) == j
          lft j = =proof
            faceFin-restrinj g ginj (f i) (faceFin-restrinj f finj i j)
                                          ==[ faceFin-restrinj-cmp-rf finj ginj i j ] /
            faceFin-restrinj (g ∘ f) (finj ∘ ginj) i j
                                          ==[ faceFin-restrinj-ext (finj ∘ ginj) id i (prj1 (pj2 finv)) j ] /
            faceFin-restrinj id id i j
                                          ==[ faceFin-restrinj-id i j ]∎
            j ∎
          rgt : (j : Fin m) → faceFin-restrinj f finj i (faceFin-restrinj g ginj (f i) j) == j
          rgt j = =proof
            faceFin-restrinj f finj i (faceFin-restrinj g ginj (f i) j)
                                          ==[ faceFin-restrinj-=pt finj (prj1 (pj2 finv) i ⁻¹) _ ] /
            faceFin-restrinj f finj (g (f i)) (faceFin-restrinj g ginj (f i) j)
                                          ==[ faceFin-restrinj-cmp-rf ginj finj (f i) j ] /
            faceFin-restrinj (f ∘ g) (ginj ∘ finj) (f i) j
                                          ==[ faceFin-restrinj-ext (ginj ∘ finj) id (f i) (prj2 (pj2 finv)) j ] /
            faceFin-restrinj id id (f i) j
                                          ==[ faceFin-restrinj-id (f i) j ]∎
            j ∎

          


  -- function that repeats an element (degeneracy map)
  -- it maps i,i+1 to i.
  degenFin : ∀ {n} → (i : Fin n)
               → Σ[ (Fin (suc n) → Fin n) ] (λ x → x (fi i)  == x (fs i))
  degenFin {suc n} fz = Fin-diag ,, =rf
  degenFin {suc n} (fs i) = fst ,, snd
    where ih : Σ[ (Fin (suc n) → Fin n) ] (λ x → x (fi i) == x (fs i))
          ih = degenFin i
          fst : Fin (suc (suc n)) → Fin (suc n)
          fst fz = fz
          fst (fs j) = fs (pj1 ih j)
          snd : fst (fi (fs i)) == fst (fs (fs i))
          snd = =ap fs (pj2 ih)

  -- the number of elements does not decrease along injective functions between finite sets
  Fin-finj-≤ : ∀ {n m} {f : Fin n → Fin m} → is-injective f → n ≤N m
  Fin-finj-≤ {zero} {m} {f} finj = 0₁
  Fin-finj-≤ {suc n} {zero} {f} finj = f fz
  Fin-finj-≤ {suc n} {suc m} {f} finj =
    Fin-finj-≤ {n} {m} {f = restr}
               (faceFin-restr-inj {f = f ∘ fs} {f fz} (λ _ fs≠fz → PA4-Fin (finj fs≠fz ⁻¹))
                                  (injective-cmp fs-inj finj))
    where restr : Fin n → Fin m
          restr = faceFin-restr (f ∘ fs) (f fz) (λ _ fs=fz → PA4-Fin (finj fs=fz ⁻¹))

  
  -- induction with arbitrary base case using the face map

  faceFin-ind :  ∀ {n} {C : Fin (suc n) → Set} (i : Fin (suc n))
                   → (cel : C i) → (cfun : ∀ x → C (faceFin-fun i x))
                     → Σ[ (∀ j → C j) ] ( λ x →
                         (x i == cel) × (∀ j → x (faceFin-fun i j)== cfun j) )
  faceFin-ind {n} {C} i cel cfun =
    fst
    ,, (sndel , sndfc)
    where module i = splt+N-Fin i
          module fc = faceFin i
          lfun : ∀ j → C (Fin-=to→ i.eq (Fin+N-inl {i.nl} j))
          lfun j = (C ● fc.left j) (cfun (Fin-=to→ i.eqn (Fin+N-inl {i.nl} j)))
          rfun : ∀ j → C (Fin-=to→ i.eq (Fin+N-inr {i.nl} (fs j)))
          rfun j = (C ● fc.right j) (cfun (Fin-=to→ i.eqn (Fin+N-inr {i.nl} j)))
          fst : ∀ j → C j
          fst = splt+N-Fin-ind C i cel lfun rfun

          sndel : fst i == cel
          sndel = prj1 (splt+N-Fin-ind-comp C cel lfun rfun)
          sndfc+ : (j : Fin (i.nl +N i.nr))
                     → fst (faceFin-fun i (Fin-=to→ i.eqn j)) == cfun (Fin-=to→ i.eqn j)
          sndfc+ = Fin+N-ind (λ j → fst (faceFin-fun i (Fin-=to→ i.eqn j))
                                       == cfun (Fin-=to→ i.eqn j))
                             (λ j → =proof
             fst (faceFin-fun i (Fin-=to→ i.eqn (Fin+N-inl j)))
                                   ==[ =transp-flip C (fc.left j) (=apd fst (fc.left j)) ] /
             (C ● fc.left j ⁻¹) (fst (Fin-=to→ i.eq (Fin+N-inl j)))
                                                                 ==[ =ap (C ● fc.left j ⁻¹)
                                   (prj1 (prj2 (splt+N-Fin-ind-comp C cel lfun rfun)) j) ] /
             (C ● fc.left j ⁻¹) (lfun j)
                                              ==[ =transp-forth-back-ptw C (fc.left j) _ ]∎
             cfun (Fin-=to→ i.eqn (Fin+N-inl j)) ∎)
                             (λ j → =proof
             fst (faceFin-fun i (Fin-=to→ i.eqn (Fin+N-inr j)))
                                 ==[ =transp-flip C (fc.right j) (=apd fst (fc.right j)) ] /
             (C ● fc.right j ⁻¹) (fst (Fin-=to→ i.eq (Fin+N-inr (fs j))))
                                                                ==[ =ap (C ● fc.right j ⁻¹)
                                   (prj2 (prj2 (splt+N-Fin-ind-comp C cel lfun rfun)) j) ] /
             (C ● fc.right j ⁻¹) (rfun j)
                                             ==[ =transp-forth-back-ptw C (fc.right j) _ ]∎
             cfun (Fin-=to→ i.eqn (Fin+N-inr j)) ∎)

          eqn-id : ∀ j → Fin-=to→ i.eqn (Fin-=to→ (i.eqn ⁻¹) j) == j
          eqn-id = =transp-back-forth-ptw Fin i.eqn
          sndfc : (j : Fin n) → fst (faceFin-fun i j) == cfun j
          sndfc j = =proof
            fst (faceFin-fun i j)
                                        ==[ =apd fst (=ap (faceFin-fun i) (eqn-id j)) ⁻¹ ] /
            (C ● =ap (faceFin-fun i) (eqn-id j))
               (fst (faceFin-fun i (Fin-=to→ i.eqn (Fin-=to→ (i.eqn ⁻¹) j))))
                                                ==[ =ap (C ● =ap (faceFin-fun i) (eqn-id j))
                                                        (sndfc+ (Fin-=to→ (i.eqn ⁻¹) j)) ] /
            (C ● =ap (faceFin-fun i) (eqn-id j))
               (cfun (Fin-=to→ i.eqn (Fin-=to→ (i.eqn ⁻¹) j)))
                                            ==[ ●=ap-is-● C (faceFin-fun i) (eqn-id j) _ ] /
            ((C ∘' faceFin-fun i) ● eqn-id j)
               (cfun (Fin-=to→ i.eqn (Fin-=to→ (i.eqn ⁻¹) j)))
                                                                 ==[ =apd cfun (eqn-id j) ]∎
            cfun j ∎

          



  -- canonical lift of a function between finite sets
  liftFin :  ∀ {n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
  liftFin f fz = fz
  liftFin f (fs i) = fs (f i)
  -- listFin f = [fx ; fs ∘ f] : 1 + Fin n → Fin (suc m)

  -- lift that swaps the first two elements
  swapFin : ∀ {n m} → (Fin n → Fin m) → Fin (suc (suc n)) → Fin (suc (suc m))
  swapFin f fz = fs fz
  swapFin f (fs i) = liftFin (fs ∘ f) i

  -- some properties of these
  liftFin-id : ∀ {n f} → (∀ i → f i == i) → ∀ i → liftFin {n} f i == i
  liftFin-id isid fz = =rf
  liftFin-id isid  (fs i) = =ap fs (isid i)
  liftFin-ptw : {n m : Nat}{f : Fin n → Fin m}{g : Fin (suc n) → Fin (suc m)}
                   → fz == g fz → (∀ i → fs (f i) == g (fs i))
                     → ∀ i → liftFin f i == g i
  liftFin-ptw eqz eqs fz = eqz
  liftFin-ptw eqz eqs (fs i) = eqs i
  liftFin-ap : {n m : Nat}{f f' : Fin n → Fin m}
                   → (∀ i → f i == f' i) → ∀ i → liftFin f i == liftFin f' i
  liftFin-ap {f = f} {f'} pf = liftFin-ptw {g = liftFin f'} =rf (λ i → =ap fs (pf i))

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

  liftFin-inj : ∀ {n m} {f : Fin n → Fin m}
                  → is-injective f → is-injective (liftFin f)
  liftFin-inj finj {fz} {fz} eq = =rf
  liftFin-inj finj {fs x} {fs x'} eq = =ap fs (finj (fs-inj eq))


  liftFin-invrt : ∀ {n m} {f : Fin n → Fin m}
                  → is-invrt f → is-invrt (liftFin f)
  liftFin-invrt {n} {m} {f} finv = liftFin g ,, (lglf=id , lflg=id)
    where g : Fin m → Fin n
          g = pj1 finv
          lglf=id : ∀ x → liftFin g (liftFin f x) == x
          lglf=id fz = =rf
          lglf=id (fs x) = =ap fs (prj1 (pj2 finv) x)
          lflg=id : ∀ x → liftFin f (liftFin g x) == x
          lflg=id fz = =rf
          lflg=id (fs x) = =ap fs (prj2 (pj2 finv) x)


  swapFin-ptw : ∀ {n m}{f : Fin n → Fin m}{g : Fin (suc (suc n)) → Fin (suc (suc m))}
                   → fs fz == g fz → fz == g (fs fz)
                     → (∀ i → fs (fs (f i)) == g (fs (fs i)))
                       → ∀ i → swapFin f i == g i
  swapFin-ptw eqz eqsz eqss fz = eqz
  swapFin-ptw eqz eqsz eqss (fs fz) = eqsz
  swapFin-ptw eqz eqsz eqss (fs (fs i)) = eqss i

  swapFin-pcmp : ∀ {n m}{f g : Fin (suc (suc n)) → Fin m}
                   → (f (fs fz) == g fz) → (f fz == g (fs fz))
                     → (∀ i → f (fs (fs i)) == g (fs (fs i)))
                       → ∀ i → f (swapFin id i) == g i
  swapFin-pcmp eqz eqsz eqss fz = eqz
  swapFin-pcmp eqz eqsz eqss (fs fz) = eqsz
  swapFin-pcmp eqz eqsz eqss (fs (fs i)) = eqss i


  swapFin-inj : ∀ {n m} {f : Fin n → Fin m}
                  → is-injective f → is-injective (swapFin f)
  swapFin-inj finj {fz} {fz} eq =
    =rf
  swapFin-inj finj {fz} {fs fz} eq =
    N₀ind (PA4-Fin (eq ⁻¹))
  swapFin-inj finj {fz} {fs (fs j)} eq =
    N₀ind (PA4-Fin (fs-inj eq))
  swapFin-inj finj {fs i} {fz} eq =
    [ (λ e → N₀ind (PA4-Fin (=transp (λ x → liftFin (fs ∘ _) x == fs fz) (e ⁻¹) eq)))
    ∣ (λ je → N₀ind (PA4-Fin (fs-inj (=transp (λ x → liftFin (fs ∘ _) x == fs fz)
                                              (pj2 je ⁻¹)
                                              eq) ⁻¹)))
    ] (Fin-dicot i)
  swapFin-inj finj {fs i} {fs j} eq =
    =ap fs (liftFin-inj (finj ∘ fs-inj) eq)

  swapFin-invrt : ∀ {n m} {f : Fin n → Fin m}
                  → is-invrt f → is-invrt (swapFin f)
  swapFin-invrt {n} {m} {f} finv = swapFin g ,, (lglf=id , lflg=id)
    where g : Fin m → Fin n
          g = pj1 finv
          lglf=id : ∀ x → swapFin g (swapFin f x) == x
          lglf=id fz = =rf
          lglf=id (fs fz) = =rf
          lglf=id (fs (fs x)) = =ap (fs ∘ fs) (prj1 (pj2 finv) x)
          lflg=id : ∀ x → swapFin f (swapFin g x) == x
          lflg=id fz = =rf
          lflg=id (fs fz) = =rf
          lflg=id (fs (fs x)) = =ap (fs ∘ fs) (prj2 (pj2 finv) x)


  -- the pigeonhole principle, and related stuff

  Fin-pgnhl : ∀ {n m} {f : Fin n → Fin m} → n == m → is-injective f → is-surjective f
  Fin-pgnhl {n} {zero} {f} z=m finj j =
    N₀rec j
  Fin-pgnhl {suc n} {suc m} {f} sn=sm finj =
    pj1 (faceFin-ind (f fz) (fz ,, =rf) ≠ffz)
    where ih : is-surjective (faceFin-restrinj f finj fz)
          ih = Fin-pgnhl (suc-inj sn=sm) (faceFin-restrinj-inj finj fz)
          ≠ffz : ∀ j → fib f (faceFin-fun (f fz) j)
          ≠ffz j = fs (pj1 (ih j))
                   ,, (=proof
            f (fs (pj1 (ih j)))             ==[ faceFin-restrinj-tr finj fz _ ⁻¹ ] /
            faceFin-fun (f fz) (faceFin-restrinj f finj fz (pj1 (ih j)))
                                            ==[ =ap (faceFin-fun (f fz)) (pj2 (ih j)) ]∎
            faceFin-fun (f fz) j ∎)

  Fin-invrt-=len : ∀ {n m} {f : Fin n → Fin m} → is-invrt f → n == m
  Fin-invrt-=len {zero} {zero} {f} finv =      =rf
  Fin-invrt-=len {zero} {suc m} {f} finv =     N₀rec (pj1 finv fz)
  Fin-invrt-=len {suc n} {zero} {f} _ =        N₀rec (f fz)
  Fin-invrt-=len {suc n} {suc m} {f} finv =
    =ap suc (Fin-invrt-=len {f = faceFin-restrinj f finj fz}
                            (faceFin-restrinj-invrt finj fz finv))
    where finj : is-injective f
          finj = invrt-is-injective finv

-- -- end of file
