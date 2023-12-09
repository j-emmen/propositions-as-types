{-# OPTIONS --without-K #-}

module Lambda-Calculus where
  open import Nat-and-Fin

-- Lambda Terms in De Bruijn notation
-- a variable var i is bound by the i-th closest abstraction if any
-- lam (app (var 0) (var 1)) : Trm 2 (var 0 is bound while var 1 is free)

  data Trm : Nat → Set where
    var : ∀ {n} → Fin n → Trm n
    lam : ∀ {n} → Trm (suc n) → Trm n
    app : ∀ {n} → Trm n → Trm n → Trm n

-- these should be defined using `is-idfull` but then Agda would complain about the pattern
-- since, I guess, we would be treating an inductive constructor as any function term
  var-inj-all : ∀ {n i j} (p : var {n} i == var j) → Σ[ i == j ] (λ u → =ap var u == p)
  var-inj-all  =rf = =rf ,, =rf
  lam-inj-all : ∀ {n M N} (p : lam {n} M == lam N) → Σ[ M == N ] (λ u → =ap lam u == p)
  lam-inj-all =rf = =rf ,, =rf
  app-inj-all : ∀ {n M₁ M₂ N₁ N₂} (p : app {n} M₁ M₂ == app N₁ N₂)
                  → Σ[ (M₁ == N₁) × (M₂ == N₂) ] (λ u → =ap₂ app (prj1 u) (prj2 u) == p)
  app-inj-all =rf = (=rf , =rf) ,, =rf

  var-inj : ∀ {n i j} → var {n} i == var j → i == j
  var-inj p = pj1 (var-inj-all p)
  lam-inj : ∀ {n M N} → lam {n} M == lam N → M == N
  lam-inj p = pj1 (lam-inj-all p)
  app-inj : ∀ {n M₁ M₂ N₁ N₂} → app {n} M₁ M₂ == app N₁ N₂ → (M₁ == N₁) × (M₂ == N₂)
  app-inj p = pj1 (app-inj-all p)
  app-injₗ : ∀ {n M₁ M₂ N₁ N₂} → app {n} M₁ M₂ == app N₁ N₂ → M₁ == N₁
  app-injₗ = prj1 ∘ app-inj
  app-injᵣ : ∀ {n M₁ M₂ N₁ N₂} → app {n} M₁ M₂ == app N₁ N₂ → M₂ == N₂
  app-injᵣ = prj2 ∘ app-inj
  var-inj-inv : ∀ {n i j} → is-invrt (var-inj {n} {i} {j})
  var-inj-inv {n} {i} {j} =
    =ap (var {n}) ,, ((λ q → pj2 (var-inj-all q))
                     , =J (λ _ p → var-inj (=ap var p) == p) =rf)
  lam-inj-inv : ∀ {n M N} → is-invrt (lam-inj {n} {M} {N})
  lam-inj-inv {n} = 
    =ap (lam {n}) ,, ((λ q → pj2 (lam-inj-all q))
                     , =J (λ _ p → lam-inj (=ap lam p) == p) =rf)
  app-inj-inv : ∀ {n M₁ M₂ N₁ N₂} →  is-invrt (app-inj {n} {M₁} {M₂} {N₁} {N₂})
  app-inj-inv {n} {M₁} {M₂} {N₁} {N₂} = 
    (λ z → =ap₂ (app {n}) (prj1 z) (prj2 z))
    ,, ((λ q → pj2 (app-inj-all q))
       , λ pp → =J (λ _ p₁ → ∀ {y} (p₂ : M₂ == y) → app-inj (=ap₂ app p₁ p₂) == (p₁ , p₂))
                    (=J (λ _ u → app-inj (=ap₂ app =rf u) == =rf , u) =rf)
                    (prj1 pp)
                    (prj2 pp)
                • ×η pp)

  var≠lam : ∀ {n} i M → ¬ (var {n} i == lam M)
  var≠lam {n} i M = λ u → (fam ● u) 0₁
    where fam : Trm n → Set
          fam (var j) = N₁
          fam (lam P) = N₀
          fam (app P₁ P₂) = N₀
  lam≠var : ∀ {n} i M → ¬ (lam M == var {n} i)
  lam≠var {n} i M = ¬=sym (var≠lam i M)

  var≠app : ∀ {n} i M N → ¬ (var {n} i == app M N)
  var≠app {n} i M N = λ u → (fam ● u) 0₁
    where fam : Trm n → Set
          fam (var j) = N₁
          fam (lam P) = N₀
          fam (app P₁ P₂) = N₀  
  app≠var : ∀ {n} i M N → ¬ (app M N == var {n} i)
  app≠var {n} i M N = ¬=sym (var≠app i M N)

  lam≠app : ∀ {n} P M N → ¬ (lam {n} P == app M N)
  lam≠app {n} P M N = λ u → (fam ● u) 0₁
    where fam : Trm n → Set
          fam (var j) = N₀
          fam (lam P) = N₁
          fam (app P₁ P₂) = N₀
  app≠lam : ∀ {n} M N P → ¬ (app M N == lam {n} P)
  app≠lam M N P = ¬=sym (lam≠app P M N)

  -- a term is either a variable, a lambda, or an application
  Trm-is-var : ∀ {n} → (M : Trm n) → Set
  Trm-is-var {n} M = Σ[ Fin n ] (λ x → var x == M)
  Trm-is-lam : ∀ {n} → (M : Trm n) → Set
  Trm-is-lam {n} M = Σ[ Trm (suc n) ] (λ x → lam x == M)
  Trm-is-app : ∀ {n} → (M : Trm n) → Set
  Trm-is-app {n} M = Σ[ Trm n × Trm n ] (λ x → app (prj1 x) (prj2 x) == M)
  Trm-Cases : ∀ {n} → (M : Trm n) → Set
  Trm-Cases {n} M = Trm-is-var M + Trm-is-lam M + Trm-is-app M
  Trm-cases : ∀ {n} → (M : Trm n) → Trm-Cases M
  Trm-cases (var i)             = inl (i ,, =rf)
  Trm-cases (lam M)             = inr (inl (M ,, =rf))
  Trm-cases (app M₁ M₂)         = inr (inr ((M₁ , M₂) ,, =rf))

  Trm-is-decid : ∀ {n} (M N : Trm n) → (M == N) + (¬ (M == N))
  Trm-is-decid (var i) (var j) =
    [ inl ∘ =ap var ∣ (λ nu → inr (nu ∘ var-inj)) ] (Fin-is-decid i j)
  Trm-is-decid (var i) (lam N) =
    inr (var≠lam i N)
  Trm-is-decid (var i) (app N₁ N₂) =
    inr (var≠app i N₁ N₂)
  Trm-is-decid (lam M) (var j) =
    inr (lam≠var j M)
  Trm-is-decid (lam M) (lam N) =
    [ inl ∘ =ap lam ∣ (λ ne → inr (ne ∘ lam-inj)) ] (Trm-is-decid M N)
  Trm-is-decid (lam M) (app N₁ N₂) =
    inr (lam≠app M N₁ N₂)
  Trm-is-decid (app M₁ M₂) (var j) =
    inr (app≠var j M₁ M₂)
  Trm-is-decid (app M₁ M₂) (lam N) =
    inr (app≠lam M₁ M₂ N)
  Trm-is-decid (app M₁ M₂) (app N₁ N₂) =
    [ inl ∘ (λ z → =ap₂ app (prj1 z) (prj2 z))
    ∥ inr ∘ ¬-is-covar app-injₗ
    ∥ inr ∘ ¬-is-covar app-injᵣ
    ] aux
    where MN1 : (M₁ == N₁) + ¬ (M₁ == N₁)
          MN1 = Trm-is-decid M₁ N₁
          MN2 : (M₂ == N₂) + ¬ (M₂ == N₂)
          MN2 = Trm-is-decid M₂ N₂
          MN : ((M₁ == N₁) × (M₂ == N₂)) + ((M₁ == N₁) × (¬ (M₂ == N₂)))
                    + ((¬ (M₁ == N₁)) × (M₂ == N₂)) + ((¬ (M₁ == N₁)) × (¬ (M₂ == N₂)))
          MN = +×+-dist (MN1 , MN2)
          aux : ((M₁ == N₁) × (M₂ == N₂)) + ¬ (M₁ == N₁) + ¬ (M₂ == N₂)
          aux = [ inl ∣ [ inr ∘ inr ∘ prj2 ∥ inr ∘ inl ∘ prj1 ∥ inr ∘ inl ∘ prj1 ] ] MN
  
  Trm-is-set : ∀ n → isSet (Trm n)
  Trm-is-set n = HedbergThm (Trm-is-decid {n})

  lam-or-not : ∀ {n} M → Trm-is-lam {n} M + ¬ (Trm-is-lam M)
  lam-or-not {n} (var i) = inr (λ z → lam≠var _ _ (pj2 z))
  lam-or-not {n} (lam M) = inl (M ,, =rf)
  lam-or-not {n} (app M N) = inr (λ z → lam≠app _ _ _ (pj2 z))

  -- length of terms, i.e. number of symbols
  -- most likely useless
  # : ∀ {n} → Trm n → Nat
  # (var i) = one
  # (lam M) = suc (# M)
  # (app M N) = # M +N # N

  #≠0 : ∀ {n} {M : Trm n} → ¬ (# M == zero)
  #≠0 {n} {var i} = PA4
  #≠0 {n} {lam M} = PA4
  #≠0 {n} {app M N} = #≠0 {n} {M} ∘ sum-0-is-0⁻¹

  #-pos : ∀ {n} {M} → one ≤N # {n} M
  #-pos {n} {var i} = 0₁
  #-pos {n} {lam M} = 0₁
  #-pos {n} {app M N} = +N-≤ {one} {zero} {# M} {# N} (#-pos {n} {M}) 0₁

  -- context extension
  rename : ∀ {n m} → Trm n → (Fin n → Fin m) → Trm m
  rename (var x) f = var (f x)
  rename (lam M) f = lam (rename M (liftFin f))
  rename (app M N) f = app (rename M f) (rename N f)
  -- maps M(1,...,n) to M(f₁,...,fₙ)

  ext : ∀ {n} → Trm n → Trm (suc n)
  ext M = rename M fs
  -- maps M(1,...,n) to M(2,...,n+1)
  ext[_] : ∀ k {n} → Trm n → Trm (k +N n)
  ext[ zero ] = id
  ext[ suc k ] = ext ∘ ext[ k ]

  wlift : ∀ {n m} → (Fin n → Trm m) → Fin (suc n) → Trm (suc m)
  wlift f fz = var fz
  wlift f (fs i) = ext (f i)
  -- wlift f = [var fz ; ext ∘ f] : 1 + Fin n → Trm (suc m)

  wlift-ptw : ∀ {n m}{f f' : Fin n → Trm m}
                → (∀ i → f i == f' i) → ∀ i → wlift f i == wlift f' i
  wlift-ptw {f = f} pf fz = =ap var (=rf {a = fz})
  wlift-ptw {f = f} pf (fs i) = =ap ext (pf i)

  wlift-cmp : {n m k : Nat}(f : Fin n → Fin m)(g : Fin m → Trm k)
                → ∀ i → wlift g (liftFin f i) == wlift (g ∘ f) i
  wlift-cmp f g fz = =rf
  wlift-cmp f g (fs i) = =rf

  wlift-cmp⁻¹ : {n m k : Nat}(f : Fin n → Fin m)(g : Fin m → Trm k)
                → ∀ i → wlift (g ∘ f) i == wlift g (liftFin f i)
  wlift-cmp⁻¹ f g i = wlift-cmp f g i ⁻¹


  -- renaming is action  
  rename-id : ∀ {n} M {f} → (∀ i → f i == i) → rename {n} M f == M
  rename-id (var i) isid =
    =ap var (isid i)
  rename-id (lam M) isid =
    =ap lam (rename-id M (liftFin-id isid))
  rename-id (app M₁ M₂) isid =
    =ap₂ app (rename-id M₁ isid) (rename-id M₂ isid)
  rename-ptw :  {n m : Nat}(M : Trm n){f f' : Fin n → Fin m} → (∀ i → f i == f' i)
                     → rename M f == rename M f'
  rename-ptw (var x) {f} pf =
    =ap var (pf x)
  rename-ptw (lam M) {f} pf =
    =ap lam (rename-ptw M (liftFin-ap pf))
  rename-ptw (app M N) {f} pf =
    =ap₂ app (rename-ptw M pf) (rename-ptw N pf)
  rename-inj : ∀ {n m} {f : Fin n → Fin m} (finj : ∀ {x x'} → f x == f x' → x == x')
                  → ∀ {M M'} → rename M f == rename M' f → M == M'
  rename-inj finj {var i} {var i'} eq =
    =ap var (finj (var-inj eq))
  rename-inj finj {lam M} {lam M'} eq =
    =ap lam (rename-inj (liftFin-inj finj) (lam-inj eq))
  rename-inj finj {app M₁ M₂} {app M'₁ M'₂} eq =
    =ap₂ app (rename-inj finj (prj1 (app-inj eq))) (rename-inj finj (prj2 (app-inj eq)))
  rename-act : {n m k : Nat}(M : Trm n)(f : Fin n → Fin m)(g : Fin m → Fin k)
                   → rename (rename M f) g == rename M (g ∘ f)
  rename-act (var x) f g = =rf
  rename-act (lam M) f g =
    =ap lam (=proof
      rename (rename M (liftFin f)) (liftFin g)  ==[ rename-act M (liftFin f) (liftFin g) ] /
      rename M (liftFin g ∘ liftFin f)           ==[ rename-ptw M (liftFin-cmp f g) ]∎
      rename M (liftFin (g ∘ f)) ∎)
  rename-act (app M₁ M₂) f g = =ap₂ app (rename-act M₁ f g) (rename-act M₂ f g)

  ext-inj : ∀ {n M M'} → ext {n} M == ext M' → M == M'
  ext-inj = rename-inj fs-inj
  extk-inj : ∀ k {n M M'} → ext[ k ] {n} M == ext[ k ] M' → M == M'
  extk-inj zero = id
  extk-inj (suc k) = extk-inj k ∘ ext-inj
  

  -- renaming along a variables-projection is the same as iterated extension (weakening)
  rename-prj-is-ext : ∀ k {n} M → rename {n} M (Fin+N-inr {k}) == ext[ k ] M
  rename-prj-is-ext zero M = rename-id M (λ _ → =rf)
  rename-prj-is-ext (suc k) M = rename-act M (Fin+N-inr {k}) fs ⁻¹ • =ap ext (rename-prj-is-ext k M)

  rename-lam-is-lam : ∀ {n m M} (f : Fin n → Fin m) → Trm-is-lam M → Trm-is-lam (rename M f)
  rename-lam-is-lam f islam =
    rename (pj1 islam) (liftFin f)
    ,, =ap (λ x → rename x f) (pj2 islam)
  ext-lam-is-lam : ∀ {n M} → Trm-is-lam M → Trm-is-lam (ext {n} M)
  ext-lam-is-lam = rename-lam-is-lam fs

  rename-sq : {n m : Nat}(M : Trm n){f : Fin n → Fin m}{f' : Fin (suc n) → Fin (suc m)}
              {g : Fin n → Fin (suc n)}{g' : Fin m → Fin (suc m)}
                 → (∀ i → g' (f i) == f' (g i))
                   → rename M (g' ∘ f) == rename (rename M g) f'
  rename-sq (var x) {f} {f'} {g} {g'} pf =
    =ap var (pf x)
  rename-sq (lam M) {f} {f'} {g} {g'} pf =
    =ap lam (=proof
      rename M (liftFin (g' ∘ f))            ==[ rename-ptw M (liftFin-cmp⁻¹ f g') ] /
      rename M (liftFin g' ∘ liftFin f)      ==[ rename-sq M {liftFin f} {liftFin f'} {liftFin g}
                                                             {liftFin g'} (liftFin-sq pf ) ]∎
      rename (rename M (liftFin g)) (liftFin f')∎)
  rename-sq (app M₁ M₂) {f} {f'} {g} {g'} pf =
    =ap₂ app (rename-sq M₁ {g' = g'} pf) (rename-sq M₂ {g' = g'} pf)

  rename-sq⁻¹ : {n m : Nat}(M : Trm n){f : Fin n → Fin m}{f' : Fin (suc n) → Fin (suc m)}
                {g : Fin n → Fin (suc n)}{g' : Fin m → Fin (suc m)}
                 → (∀ i → g' (f i) == f' (g i))
                   → rename (rename M g) f' == rename M (g' ∘ f)
  rename-sq⁻¹ M {f} {g' = g'} pf = rename-sq M {f} {g' = g'} pf ⁻¹


  ext-rename : {n m : Nat}(M : Trm n)(f : Fin n → Fin m)
                  → ext (rename M f) == rename (ext M) (liftFin f)
  ext-rename M f = =proof
    ext (rename M f)             ==[ rename-act M f fs ] /
    rename M (fs ∘ f)            ==[ rename-sq M {f} {liftFin f} {fs} {fs}
                                                 (λ i → =rf {a = fs (f i)}) ]∎
    rename (ext M) (liftFin f) ∎

  wlift-liftFin : {n m k l : Nat}{f : Fin n → Fin k}{g : Fin k → Trm m}
                  {f' : Fin l → Fin m}{g' : Fin n → Trm l}
                    → (∀ i → g (f i) == rename (g' i) f')
                      →(i : Fin (suc n)) → wlift g (liftFin f i) == rename (wlift g' i) (liftFin f')
  wlift-liftFin pf fz = =rf
  wlift-liftFin {f' = f'} {g'} pf (fs i) = =ap ext (pf i) • ext-rename (g' i) f'

  wlift-fs-ptw : {n m : Nat}(f : Fin n → Trm m)
                   → (i : Fin (suc n)) → wlift (wlift f ∘ fs) i == rename (wlift f i) (liftFin fs)
  wlift-fs-ptw f fz = =rf {a = var fz}
  wlift-fs-ptw f (fs i) = ext-rename (f i) fs


  -- substitutes all variables in a term
  subst-all : ∀ {n m} → Trm n → (Fin n → Trm m) → Trm m
  subst-all (var x) f = f x
  subst-all (lam M) f =  lam (subst-all M (wlift f))
  subst-all (app M N) f = app (subst-all M f) (subst-all N f)
  -- maps M(1,...,n) to M(f₁(1,...,m),...,fₙ(1,...,m))
  -- ext M could be subst-all M (var ∘ fs), but need ext to define wlift

  -- every term defines a section to the dependent projection (that forgets the first variable)
  trmsect :  ∀ {n} → Trm n → Fin (suc n) → Trm n
  trmsect M fz = M
  trmsect M (fs i) = var i
  -- to substitute a single term (in the first variable) is to substitute a term section
  subst-0 : ∀ {n} → Trm (suc n) → Trm n → Trm n
  subst-0 M N = subst-all M (trmsect N)


  rename-trmsect : {n m : Nat}(M : Trm n)(f : Fin n → Fin m)
                     → ∀ i → trmsect (rename M f) (liftFin f i) == rename (trmsect M i) f
  rename-trmsect M f fz = =rf {a = rename M f}
  rename-trmsect M f (fs i) = =rf {a = var (f i)}

  subst-all-rename-sq : {n m k l : Nat}(M : Trm n){f : Fin n → Fin k}{g : Fin k → Trm m}
                        {f' : Fin l → Fin m}{g' : Fin n → Trm l}
                          → (∀ i → g (f i) == rename (g' i) f')
                            → subst-all (rename M f) g == rename (subst-all M g') f'
  subst-all-rename-sq (var x) pf =
    pf x
  subst-all-rename-sq (lam M) pf =
    =ap lam (subst-all-rename-sq M (wlift-liftFin pf))
  subst-all-rename-sq (app M₁ M₂) pf =
    =ap₂ app (subst-all-rename-sq M₁ pf) (subst-all-rename-sq M₂ pf)

  subst-all-rename-sq⁻¹ : {n m k l : Nat}(M : Trm n){f : Fin n → Fin k}{g : Fin k → Trm m}
                        {f' : Fin l → Fin m}{g' : Fin n → Trm l}
                          → (∀ i → g (f i) == rename (g' i) f')
                            → rename (subst-all M g') f' == subst-all (rename M f) g
  subst-all-rename-sq⁻¹ M pf = subst-all-rename-sq M pf ⁻¹


  subst-all-ptw : {n m : Nat}(M : Trm n){f f' : Fin n → Trm m}
                     → (∀ i → f i == f' i) → subst-all M f == subst-all M f'
  subst-all-ptw (var x) pf = pf x
  subst-all-ptw (lam M) pf = =ap lam (subst-all-ptw M (wlift-ptw pf))
  subst-all-ptw (app M N) pf = =ap₂ app (subst-all-ptw M pf) (subst-all-ptw N pf)


  subst-all-rename : {n m k : Nat}(M : Trm n)(f : Fin n → Fin m)(g : Fin m → Trm k)
                        → subst-all (rename M f) g == subst-all M (g ∘ f)
  subst-all-rename (var x) f g =
    =rf
  subst-all-rename (lam M) f g =
    =ap lam (=proof
      subst-all (rename M (liftFin f)) (wlift g)   ==[ subst-all-rename M (liftFin f) (wlift g) ] /
      subst-all M (wlift g ∘ liftFin f)            ==[ subst-all-ptw M (wlift-cmp f g) ]∎
      subst-all M (wlift (g ∘ f)) ∎)
  subst-all-rename (app M₁ M₂) f g =
    =ap₂ app (subst-all-rename M₁ f g) (subst-all-rename M₂ f g)


  subst-0-rename : {n m : Nat}(M : Trm (suc n))(N : Trm n)(f : Fin n → Fin m)
                      → subst-0 (rename M (liftFin f)) (rename N f) == rename (subst-0 M N) f
  subst-0-rename M N f = subst-all-rename-sq M {liftFin f} {trmsect (rename N f)} {f} {trmsect N}
                                               (rename-trmsect N f)

  subst-0-ext : {n : Nat}(M : Trm (suc n))(N : Trm n)
                   → subst-0 (rename M (liftFin fs)) (ext N) == ext (subst-0 M N)
  subst-0-ext M N = subst-0-rename M N fs


  -- lifting variables yields variables
  wlift-var :  {n : Nat} → ∀ i → wlift (var {n}) i == var i
  wlift-var fz = =rf
  wlift-var (fs i) = =rf

  wlift-var-fnv : ∀ {n m} → {f : Fin n → Fin m} → {f' : Fin (suc n) → Fin (suc m)}
                   → fz == f' fz → (∀ i → fs (f i) == f' (fs i))
                     → ∀ i → wlift (var ∘ f) i == (var ∘ f') i
  wlift-var-fnv eqz eqs fz = =ap var eqz
  wlift-var-fnv eqz eqs (fs i) = =ap var (eqs i)

  wlift-var-fn : ∀ {n m} → {f : Fin n → Fin m} → {g : Fin (suc n) → Trm (suc m)}
                   → var fz == g fz → (∀ i → var (fs (f i)) == g (fs i))
                     → ∀ i → wlift (var ∘ f) i == g i
  wlift-var-fn eqz eqs fz = eqz
  wlift-var-fn eqz eqs (fs i) = eqs i

  -- wlift (trmsect N) : Fin (suc (suc n)) → Trm (suc n)
  -- wlift (trmsect N) : fz ↦ var fz; fs fz ↦ ext N; fs (fs x) ↦ var (fs x)
  -- liftFin fs : fz ↦ fz; fs x ↦ fs (fs x)
  -- Therefore: wlift (trmsect N) ∘ liftFin fs == var
  wlift-trmsect-lift : {n : Nat}(N : Trm n) → ∀ i → wlift (trmsect N) (liftFin fs i) == var i
  wlift-trmsect-lift N fz = =rf
  wlift-trmsect-lift N (fs i) = =rf


  -- substituting variables is doing nothing
  subst-all-var : {n : Nat}(M : Trm (suc n))
                     → subst-all M var == M
  subst-all-var (var x) =
    =rf
  subst-all-var (lam M) =
    =ap lam (subst-all-ptw M wlift-var • subst-all-var M)
  subst-all-var (app M₁ M₂) =
    =ap₂ app (subst-all-var M₁) (subst-all-var M₂)
  

  subst-all-trmsect-lift : {n : Nat}(M : Trm (suc n))(N : Trm n)
                             → subst-all M (wlift (trmsect N) ∘ liftFin fs) == M
  subst-all-trmsect-lift M N = subst-all-ptw M (wlift-trmsect-lift N) • subst-all-var M


  -- if family is global section, substitution is left inverse to ext
  subst-0-inext : {n : Nat}(M N : Trm n) → subst-0 (ext M) N == M
  subst-0-inext (var x) N =
    =rf {a = var x}
  subst-0-inext (lam M) N =
    =ap lam (=proof
      subst-all (rename M (liftFin fs)) (wlift (trmsect N))   ==[ subst-all-rename M _ _ ] /
      subst-all M (wlift (trmsect N) ∘ liftFin fs)            ==[ subst-all-trmsect-lift M N ]∎
      M ∎)
  subst-0-inext (app M₁ M₂) N =
    =ap₂ app (subst-0-inext M₁ N) (subst-0-inext M₂ N)


  -- to extend the context of terms (f i | i : Fin n) and then substitute them into (ext M)
  -- is the same as substituting the f's into M and then extend the context
  subst-all-ext : {n m : Nat}(M : Trm n)(f : Fin n → Trm m)
                      → subst-all (ext M) (wlift f) == ext (subst-all M f)
  subst-all-ext M f = subst-all-rename-sq M {fs} {wlift f} {fs} {f} (λ _ → =rf)

  -- same for families of terms
  subst-ass-wlift : {n m k : Nat}(f : Fin n → Trm m)(g : Fin m → Trm k)(i : Fin (suc n))
                          → (subst-all (wlift f i) (wlift g)) == (wlift (λ i → subst-all (f i) g) i)
  subst-ass-wlift f g fz =       =rf {a = var fz}
  subst-ass-wlift f g (fs i) =   subst-all-ext (f i) g


  -- substitution distributes over substition
  subst-all-dist : {n m k : Nat}(M : Trm n)(f : Fin n → Trm m)(g : Fin m → Trm k)
             → subst-all (subst-all M f) g == subst-all M (λ i → subst-all (f i) g)
  subst-all-dist (var x) f g =
    =rf
  subst-all-dist (lam M) f g =
    =ap lam (=proof
      subst-all (subst-all M (wlift f)) (wlift g)          ==[ subst-all-dist M (wlift f) (wlift g) ] /
      subst-all M (λ i → subst-all (wlift f i) (wlift g)) ==[ subst-all-ptw M (subst-ass-wlift f g) ]∎
      subst-all M (wlift (λ i → subst-all (f i) g)) ∎)
  subst-all-dist (app M₁ M₂) f g =
    =ap₂ app (subst-all-dist M₁ f g) (subst-all-dist M₂ f g)

  -- commuting squares of substitutions
  subst-all-ext-wlift : {n m k : Nat}(M : Trm n)(M' : Trm k)(f : Fin n → Trm m)(f' : Fin k → Trm m)
                          → subst-all M f == subst-all M' f'
                            → subst-all (ext M) (wlift f) == subst-all (ext M') (wlift f')
  subst-all-ext-wlift M M' f f' pf = subst-all-ext M f • =ap ext pf • subst-all-ext M' f' ⁻¹

  subst-all-wlift-sq : {n m k l : Nat}{f : Fin n → Trm k}{g : Fin k → Trm m}
                     {f' : Fin l → Trm m}{g' : Fin n → Trm l}
                       → (∀ i → subst-all (f i) g == subst-all (g' i) f') → (i : Fin (suc n))
                       → subst-all (wlift f i) (wlift g) == subst-all (wlift g' i) (wlift f')
  subst-all-wlift-sq {f = f} {g} {f'} {g'} pf fz =
    =rf
  subst-all-wlift-sq {f = f} {g} {f'} {g'} pf (fs i) =
    subst-all-ext-wlift (f i) (g' i) g f' (pf i)


  subst-all-sq : {n m k l : Nat}(M : Trm n){f : Fin n → Trm k}{g : Fin k → Trm m}
                 {f' : Fin l → Trm m}{g' : Fin n → Trm l}
                   → (∀ i → subst-all (f i) g == subst-all (g' i) f')
                     → subst-all (subst-all M f) g == subst-all (subst-all M g') f'
  subst-all-sq (var x) {f} {g} {f'} {g'} pf =
    pf x
  subst-all-sq (lam M) {f} {g} {f'} {g'} pf =
    =ap lam (subst-all-sq M {wlift f} {wlift g} {wlift f'} {wlift g'} (subst-all-wlift-sq pf))
  subst-all-sq (app M₁ M₂) {f} {g} {f'} {g'} pf =
    =ap₂ app (subst-all-sq M₁ pf) (subst-all-sq M₂ pf)


  subst-0-dist-aux : {n m : Nat}(N : Trm n)(f : Fin n → Trm m)
                       → (i : Fin (suc n))
                         → subst-all (wlift f i) (trmsect (subst-all N f)) == subst-all (trmsect N i) f
  subst-0-dist-aux N f fz =
    =rf {a = subst-all N f}
  subst-0-dist-aux N f (fs i) =
    subst-0-inext (f i) _

  -- substition distributes over substitution in the first variable
  subst-0-dist : {n m : Nat}(M : Trm (suc n))(N : Trm n)(f : Fin n → Trm m)
                    → subst-0 (subst-all M (wlift f)) (subst-all N f) == subst-all (subst-0 M N) f
  subst-0-dist M N f = subst-all-sq M {wlift f} {trmsect (subst-all N f)} {f} {trmsect N}
                                    (subst-0-dist-aux N f)


  -- the length of a substitution (not so useful perhaps)
  #subst-all : {n m : Nat}(M : Trm n)(f : Fin n → Trm m) → Nat
  #subst-all (var i) f     = # (f i)
  #subst-all (lam M) f     = suc (#subst-all M (wlift f))
  #subst-all (app M N) f   = #subst-all M f +N #subst-all N f
  -- to be more explicit, I need to know whether a certain variable occurs in `M` or not

  subst-all-# : {n m : Nat}(M : Trm n)(f : Fin n → Trm m)
                   → # (subst-all M f) == #subst-all M f
  subst-all-# (var i) f     = =rf
  subst-all-# (lam M) f     = =ap suc (subst-all-# M (wlift f))
  subst-all-# (app M N) f   = =ap₂ _+N_ (subst-all-# M f) (subst-all-# N f)
                 

  --------------------
  -- Diamond property
  --------------------

  Sink : (R : {n : Nat} → Trm n → Trm n → Set)
               → ∀ {n} → (N L : Trm n) → Set
  Sink R {n} N L = Σ[ Trm n ] (λ x → R N x × R L x)

  ⋄trm : (R : {n : Nat} → Trm n → Trm n → Set)
            → {n : Nat} → {N L : Trm n} → Sink R N L → Trm n
  ⋄trm R = pj1
  ⋄red₁ : (R : {n : Nat} → Trm n → Trm n → Set)
             → {n : Nat} → {N L : Trm n} → (snk : Sink R N L)
               → R N (⋄trm R snk)
  ⋄red₁ R snk = prj1 (pj2 snk)
  ⋄red₂ : (R : {n : Nat} → Trm n → Trm n → Set)
             → {n : Nat} → {N L : Trm n} → (snk : Sink R N L)
               → R L (⋄trm R snk)
  ⋄red₂ R snk = prj2 (pj2 snk)
  opsink : (R : {n : Nat} → Trm n → Trm n → Set){n : Nat}{N L : Trm n}
              → Sink R N L → Sink R L N
  opsink R snk = ⋄trm R snk ,, (⋄red₂ R snk , ⋄red₁ R snk)
  sink-fun : {R S : ∀ {n} → Trm n → Trm n → Set}
                → (∀ {n M N} → R {n} M N → S M N)
                  → ∀ {n M N} →  Sink R {n} M N → Sink S M N
  sink-fun {R} {S} pf snkR = ⋄trm R snkR ,, (pf (⋄red₁ R snkR)  , pf (⋄red₂ R snkR))


  diamond-prop : (R : {n : Nat} → Trm n → Trm n → Set) → Set
  diamond-prop R = ∀ {n} {M} {N} {L} → R M N → R M L → Sink R {n} N L


  -- the transitive closure preserves the diamond property
  
  rtclosure-diamond-aux : (R : {n : Nat} → Trm n → Trm n → Set)
                             → diamond-prop R → ∀ {n M N L} → refl-trans-clos R M N → R M L
                               → Σ[ Trm n ] (λ x → R N x × refl-trans-clos R L x)
  rtclosure-diamond-aux R diam {N = M} {L} (tcrfl M) r =
    L ,, (r , tcrfl L)
  rtclosure-diamond-aux R diam {N = N} {L} (tccnc {M} {N'} red r') r =
    ⋄trm R snkR ,, (⋄red₁ R snkR , tccnc (prj2 (pj2 snk)) (⋄red₂ R snkR))
    where snk : Σ[ Trm _ ] (λ x → R N' x × refl-trans-clos R L x)
          snk = rtclosure-diamond-aux R diam red r 
          snkR : Sink R N (pj1 snk)
          snkR = diam r' (prj1 (pj2 snk))

  rtclosure-diamond : (R : {n : Nat} → Trm n → Trm n → Set)
                         → diamond-prop R → diamond-prop (refl-trans-clos R)
  rtclosure-diamond R diam {_} {M} {N} {M} red₁ (tcrfl M) =
    N ,, (tcrfl N , red₁)
  rtclosure-diamond R diam {_} {M} {N} {L} red₁ (tccnc {M} {N'} red₂ r) =
    pj1 snk2 ,, (tccnc {N = pj1 snk1} (⋄red₁ (refl-trans-clos R) snk1) (prj1 (pj2 snk2))
                , prj2 (pj2 snk2))
    where snk1 : Sink (refl-trans-clos R) N N'
          snk1 = rtclosure-diamond R diam red₁ red₂
          snk2 : Σ[ Trm _ ] (λ x → R (pj1 snk1) x × refl-trans-clos R L x)
          snk2 = rtclosure-diamond-aux R diam (prj2 (pj2 snk1)) r



  -----------------------
  -- Reduction relations
  -----------------------

  -- the one-step reduction relation
  infix 10 _⟶_ _⟶⋆_
  data _⟶_ {n : Nat} : Trm n → Trm n → Set where
    β :  ∀ M N → (app (lam M) N) ⟶ (subst-0 M N)
    βlam : ∀ {M N} → M ⟶ N → (lam M) ⟶ (lam N)
    βappₗ : ∀ {M P N} → M ⟶ P → (app M N) ⟶ (app P N)
    βappᵣ : ∀ {M N P} → N ⟶ P → (app M N) ⟶ (app M P)

  -- reflexive and transitive closure of the one-step reduction relation
  _⟶⋆_ :  {n : Nat} → Trm n → Trm n → Set
  _⟶⋆_ = refl-trans-clos _⟶_
  ⟶⋆rfl : ∀ {n} → (M : Trm n) → M ⟶⋆ M
  ⟶⋆rfl = tcrfl
  ⟶⋆cnc : ∀ {n} → {M N L : Trm n} → M ⟶⋆ N → N ⟶ L → M ⟶⋆ L
  ⟶⋆cnc = tccnc
  ⟶⋆in : {n : Nat}{M N : Trm n} → M ⟶ N  → M ⟶⋆ N
  ⟶⋆in = rtclos-in _⟶_
  ⟶⋆tr : {n : Nat}{M N L : Trm n} → M ⟶⋆ N → N ⟶⋆ L → M ⟶⋆ L
  ⟶⋆tr = rtclos-trans _⟶_

  -- the parallel reduction relation
  infix 10 _≡>_ _≡>⋆_
  data _≡>_ {n : Nat} : Trm n → Trm n → Set where
    ≡>rfl : ∀ {M} → M ≡> M
    ≡>red :  ∀ {M} {N} {M'} {N'} → M ≡> M' → N ≡> N' → (app (lam M) N) ≡> (subst-0 M' N')
    ≡>lam : ∀ {M} {M'} → M ≡> M' → (lam M) ≡> (lam M')
    ≡>app : ∀ {M} {N} {M'} {N'} → M ≡> M' → N ≡> N' → (app M N) ≡> (app M' N')

  -- and its reflexive and transitive closure
  _≡>⋆_ : {n : Nat} → Trm n → Trm n → Set
  _≡>⋆_ = refl-trans-clos _≡>_
  ≡>⋆rfl : ∀ {n} → (M : Trm n) → M ≡>⋆ M
  ≡>⋆rfl = tcrfl
  ≡>⋆cnc : ∀ {n} → {M N L : Trm n} → M ≡>⋆ N → N ≡> L → M ≡>⋆ L
  ≡>⋆cnc = tccnc
  ≡>⋆in : {n : Nat}{M N : Trm n} → M ≡> N  → M ≡>⋆ N
  ≡>⋆in = rtclos-in _≡>_
  ≡>⋆tr : {n : Nat}{M N L : Trm n} → M ≡>⋆ N → N ≡>⋆ L → M ≡>⋆ L
  ≡>⋆tr = rtclos-trans _≡>_

  -- variables do not reduce
  ¬var⟶ : ∀ {n} (i : Fin n) M → ¬ (var i ⟶ M)
  ¬var⟶ i M ()


  β-stp : ∀ {n} ({M} N : Trm n)
            → Trm-is-lam M → Σ[ Trm n ] (app M N ⟶_)
  β-stp N isl = 
    subst-0 (pj1 isl) N
    ,, ((_⟶ subst-0 (pj1 isl) N) ● =ap (λ x → app x N) (pj2 isl)) (β (pj1 isl) N)
  βlam-stp : ∀ {n} {M : Trm (suc n)}
                      → Σ[ Trm (suc n) ] (M ⟶_) → Σ[ Trm n ] (lam M ⟶_)
  βlam-stp {n} {M} = ⟨ lam ∘ pj1 ∣∣ (λ MM → βlam {n} (pj2 MM)) ⟩
  βappₗ-stp : ∀ {n} ({M} N : Trm n)
              → Σ[ Trm n ] (M ⟶_) → Σ[ Trm n ] (app M N ⟶_)
  βappₗ-stp N z = app (pj1 z) N ,, βappₗ (pj2 z) 
  βappᵣ-stp : ∀ {n} (M {N} : Trm n)
              → Σ[ Trm n ] (N ⟶_) → Σ[ Trm n ] (app M N ⟶_)
  βappᵣ-stp M z = app M (pj1 z) ,, βappᵣ (pj2 z)

  -- Inverting βlam
  
  βlam-inj : ∀ {n} {M N N' : Trm (suc n)}(stp : M ⟶ N)(stp' : M ⟶ N')
               → (eq : lam N == lam N') → ((lam M ⟶_)● eq) (βlam stp) == βlam stp'
                 → ((M ⟶_)● (lam-inj eq)) stp == stp'
  βlam-inj stp stp =rf =rf = =rf
  -- The second equation (not eq) is needed:
  -- without it, induction on eq would not unify stp and stp'.
  -- The same equation is needed below to invert βlam.

  βlam-inv : ∀ {n} {M : Trm (suc n)} {N : Trm n}(stp : lam M ⟶ N)
               → Σ[ Trm (suc n) ]
                   (λ x → Σ[ M ⟶ x × (lam x == N) ]
                            λ z → ((lam M ⟶_) ● prj2 z) (βlam (prj1 z)) == stp)
  βlam-inv {n} {M} {lam N'} (βlam stp) = N' ,, (stp , =rf) ,, =rf
  βlam-inv-trm : ∀ {n} {M : Trm (suc n)} {N : Trm n}(stp : lam M ⟶ N)
                   → Trm (suc n)
  βlam-inv-trm stp = pj1 (βlam-inv stp)
  βlam-inv-stp : ∀ {n} {M : Trm (suc n)} {N : Trm n}(stp : lam M ⟶ N)
                   → M ⟶ βlam-inv-trm stp
  βlam-inv-stp stp = prj1 (pj1 (pj2 (βlam-inv stp)))
  βlam-inv-eq : ∀ {n} {M : Trm (suc n)} {N : Trm n}(stp : lam M ⟶ N)
                   → lam (βlam-inv-trm stp) == N
  βlam-inv-eq stp = prj2 (pj1 (pj2 (βlam-inv stp)))
  βlam-inv-coh : ∀ {n} {M : Trm (suc n)} {N : Trm n}(stp : lam M ⟶ N)
                   → ((lam M ⟶_) ● βlam-inv-eq stp) (βlam (βlam-inv-stp stp)) == stp
  βlam-inv-coh stp = pj2 (pj2 (βlam-inv stp))

  βlam-inv-uq : ∀ {n} {M : Trm (suc n)} {N : Trm n}(stp : lam M ⟶ N)
                  → {N' : Trm (suc n)} → (stp' : M ⟶ N') → (eq' : lam N' == N)
                    → ((lam M ⟶_) ● eq') (βlam stp') == stp
                      → Σ[ N' == βlam-inv-trm stp ]
                          (λ x → ((M ⟶_) ● x) stp' == βlam-inv-stp stp)
  βlam-inv-uq (βlam stp) {N'} stp' eq' coh' = lam-inj eq' ,, βlam-inj stp' stp eq' coh'
  βlam-stp-inv : ∀ {n} {M : Trm (suc n)}
                          → Σ[ Trm n ] (lam M ⟶_) → Σ[ Trm (suc n) ] (M ⟶_)
  βlam-stp-inv NN = βlam-inv-trm (pj2 NN) ,, βlam-inv-stp (pj2 NN)

  βlam-iso : ∀ {n} {M : Trm (suc n)}
                      → is-iso-pair (βlam-stp {n} {M}) (βlam-stp-inv {n} {M})
  βlam-iso {n} {M} = eq1 , eq2
    where eq1 : (NN : Σ[ Trm (suc n) ] (M ⟶_)) → βlam-stp-inv (βlam-stp NN) == NN
          eq1 = Ση
          eq2 : (NN : Σ[ Trm n ] (lam M ⟶_)) → βlam-stp (βlam-stp-inv NN) == NN
          eq2 NN = =Σchar (βlam-inv-eq (pj2 NN)) (βlam-inv-coh (pj2 NN))

  βlam-eqv : ∀ {n} {M : Trm (suc n)} → is-equiv (βlam-stp {n} {M})
  βlam-eqv {n} {M} = invrt-is-eqv (βlam-stp-inv ,, βlam-iso {n} {M})

  -- A reduction from `app M N` can be `β`, `βappₗ`, or `βappᵣ`
  -- we proceed by cases on M using propositional equality
  -- if we try a direct induction on `M`, Agda complains about termination

  βapp-stp : ∀ {n} {M N : Trm n}
               → Trm-is-lam M
                 + Σ[ Trm n ] (M ⟶_)
                 + Σ[ Trm n ] (N ⟶_)
                   → Σ[ Trm n ] (app M N ⟶_)
  βapp-stp {n} {M} {N} =
    [ β-stp N
    ∥ βappₗ-stp N
    ∥ βappᵣ-stp M
    ]

  -- Inverting βapp when first term is var

  βappvar-stp-med : ∀ {n} {i} {N : Trm n} → Σ[ Trm n ] (N ⟶_)
                     → Trm-is-lam (var i) + Σ[ Trm n ] (var i ⟶_) + Σ[ Trm n ] (N ⟶_)
  βappvar-stp-med {n} {i} {N} = inr ∘ inr

  βappvar-stp-med-invrt : ∀ {n} {i} {N : Trm n} → is-invrt (βappvar-stp-med {n} {i} {N})
  βappvar-stp-med-invrt {n} {i} {N} = g ,, (iddom , idcod)
    where g : Trm-is-lam (var i) + Σ[ Trm n ] (var i ⟶_) + Σ[ Trm n ] (N ⟶_)
                         → Σ[ Trm n ] (N ⟶_)
          g = [ (λ z → N₀ind (lam≠var i (pj1 z) (pj2 z)))
              ∥ (λ z → N₀ind (¬var⟶ i (pj1 z) (pj2 z)))
              ∥ id ]
          iddom : ∀ z → g (βappvar-stp-med {n} {i} {N} z) == z
          iddom z = =rf
          idcod : ∀ v → βappvar-stp-med (g v) == v
          idcod = +ind3 (λ v → βappvar-stp-med (g v) == v)
                        (λ z → N₀ind {λ _ → inr (inr (g (inl z))) == inl z}
                                      (lam≠var i (pj1 z) (pj2 z)))
                        (λ z → N₀ind {λ _ → inr (inr (g (inrl z))) == inrl z}
                                      (¬var⟶ i (pj1 z) (pj2 z)))
                        (λ _ → =rf)
  
  βappvar-stp : ∀ {n} {i} {N : Trm n}
                   → Σ[ Trm n ] (N ⟶_) → Σ[ Trm n ] (app (var i) N ⟶_)
  βappvar-stp {n} {i} {N} = βapp-stp {M = var i} ∘ βappvar-stp-med {n} {i} {N}
  --                         = app (var _) (pj1 z) ,, βappᵣ (pj2 z)

  βappvar-inv : ∀ {n} {i} {M N : Trm n} (stp : app (var i) M ⟶ N)
                 → Σ[ Trm n ]
                     ( λ x → Σ[ M ⟶ x × (app (var i) x == N) ]
                       (λ z → ((app (var i) M ⟶_) ● prj2 z) (βappᵣ (prj1 z)) == stp))
  βappvar-inv {n} {i} {M} {.(app (var i) _)} (βappᵣ stp) = _ ,, (stp , =rf) ,, =rf
  βappvar-inv-trm : ∀ {n} {i} {M N : Trm n} (stp : app (var i) M ⟶ N)
                       → Trm n
  βappvar-inv-trm stp = pj1 (βappvar-inv stp)
  βappvar-inv-stp : ∀ {n} {i} {M N : Trm n} (stp : app (var i) M ⟶ N)
                 → M ⟶ βappvar-inv-trm stp
  βappvar-inv-stp stp = prj1 (pj1 (pj2 (βappvar-inv stp)))
  βappvar-inv-eq : ∀ {n} {i} {M N : Trm n} (stp : app (var i) M ⟶ N)
                    → app (var i) (βappvar-inv-trm stp) == N
  βappvar-inv-eq stp = prj2 (pj1 (pj2 (βappvar-inv stp)))
  βappvar-inv-coh : ∀ {n} {i} {M N : Trm n} (stp : app (var i) M ⟶ N)
    → ((app (var i) M ⟶_) ● βappvar-inv-eq stp) (βappᵣ (βappvar-inv-stp stp)) == stp
  βappvar-inv-coh stp = pj2 (pj2 (βappvar-inv stp))
  
  βappvar-stp-inv : ∀ {n} {i} {M : Trm n}
                   → Σ[ Trm n ] (app (var i) M ⟶_) → Σ[ Trm n ] (M ⟶_)
  βappvar-stp-inv z = βappvar-inv-trm (pj2 z) ,, βappvar-inv-stp (pj2 z)

  βappvar-stp-invrt : ∀ {n} {i} {M : Trm n} → is-invrt (βappvar-stp {n} {i} {M})
  βappvar-stp-invrt {n} {i} {M} = βappvar-stp-inv {n} {i} {M} ,, (eq1 , eq2)
    where eq1 : (NN : Σ[ Trm n ] (M ⟶_)) → βappvar-stp-inv {i = i} (βappvar-stp NN) == NN
          eq1 = Ση
          eq2 : (NN : Σ[ Trm n ] (app (var i) M ⟶_)) → βappvar-stp (βappvar-stp-inv NN) == NN
          eq2 NN = =Σchar (βappvar-inv-eq (pj2 NN)) (βappvar-inv-coh (pj2 NN))

  βappvar-invrt : ∀ {n} {i} {M : Trm n} → is-invrt (βapp-stp {n} {var i} {M})
  βappvar-invrt {n} {i} {M} = inv-trn-pre (λ _ → =rf)
                                             (βappvar-stp-med-invrt {n} {i} {M})
                                             (βappvar-stp-invrt {n} {i} {M})

  βappvar-eqv : ∀ {n} {i} {M : Trm n} → is-equiv (βapp-stp {n} {var i} {M})
  βappvar-eqv {n} {i} {M} = invrt-is-eqv (βappvar-invrt {n} {i} {M})

  -- Inverting βapp when first term is app

  βappapp-stp-med : ∀ {n} {M₁ M₂ N : Trm n}
                      → Σ[ Trm n ] (λ x → app M₁ M₂ ⟶ x + N ⟶ x)
                        → Σ[ Trm (suc n) ] (λ x → lam x == app M₁ M₂)
                             + Σ[ Trm n ] (app M₁ M₂ ⟶_) + Σ[ Trm n ] (N ⟶_)
  βappapp-stp-med {n} {M₁} {M₂} {N} =
    inr ∘ λ z → [ inl ∘ ⟨ (λ _ → pj1 z) ∣∣ id ⟩
                 ∣ inr ∘ ⟨ (λ _ → pj1 z) ∣∣ id ⟩ ] (pj2 z)

  βappapp-stp-med-invrt : ∀ {n} {M₁ M₂ N : Trm n}
                                → is-invrt (βappapp-stp-med {n} {M₁} {M₂} {N})
  βappapp-stp-med-invrt {n} {M₁} {M₂} {N} = g ,, (iddom , idcod)
    where g : Σ[ Trm (suc n) ] (λ x → lam x == app M₁ M₂)
                 + Σ[ Trm n ] (app M₁ M₂ ⟶_) + Σ[ Trm n ] (N ⟶_)
                   → Σ[ Trm n ] (λ x → app M₁ M₂ ⟶ x + N ⟶ x)
          g = [ (λ z → N₀ind (lam≠app _ _ _ (pj2 z)))
              ∥ ⟨ pj1 ∣∣ (λ z → inl (pj2 z)) ⟩
              ∥ ⟨ pj1 ∣∣ (λ z → inr (pj2 z)) ⟩ ]
          iddom : ∀ z → g (βappapp-stp-med {n} {M₁} {M₂} {N} z) == z
          iddom z = +ind (λ v → g (βappapp-stp-med {n} {M₁} {M₂} {N} (pj1 z ,, v)) == (pj1 z ,, v))
                         (λ _ → =rf)
                         (λ _ → =rf)
                         (pj2 z)
                    • Ση z
          idcod : ∀ v → βappapp-stp-med {n} {M₁} {M₂} {N} (g v) == v
          idcod = +ind3 (λ v → βappapp-stp-med {n} {M₁} {M₂} {N} (g v) == v)
                        (λ z → N₀ind {λ _ → βappapp-stp-med (g (inl z)) == inl z}
                                      (lam≠app _ _ _ (pj2 z)))
                        (λ z → =ap inrl (Ση z))
                        (λ z → =ap inrr (Ση z))

  βappapp-stp : ∀ {n} {M₁ M₂ N : Trm n}
                  → Σ[ Trm n ] (λ x → app M₁ M₂ ⟶ x + N ⟶ x)
                    → Σ[ Trm n ] (app (app M₁ M₂) N ⟶_)
  βappapp-stp {n} {M₁} {M₂} {N} = βapp-stp {M = app M₁ M₂} ∘ βappapp-stp-med

  βappapp-inv : ∀ {n} {M₁ M₂ N P : Trm n} (stp : app (app M₁ M₂) N ⟶ P)
                 → Σ[ Trm n ] (λ x → Σ[ app M₁ M₂ ⟶ x × (app x N == P) ]
                     (λ z → ((app (app M₁ M₂) N ⟶_) ● prj2 z) (βappₗ (prj1 z)) == stp))
                  + Σ[ Trm n ] (λ x → Σ[ N ⟶ x × (app (app M₁ M₂) x == P) ]
                    (λ z → ((app (app M₁ M₂) N ⟶_) ● prj2 z) (βappᵣ (prj1 z)) == stp))
  βappapp-inv {n} {M₁} {M₂} {N} {.(app _ N)} (βappₗ stp) =
    inl (_ ,, (stp , =rf) ,, =rf)
  βappapp-inv {n} {M₁} {M₂} {N} {.(app (app M₁ M₂) _)} (βappᵣ stp) =
    inr (_ ,, (stp , =rf) ,, =rf)

  βappapp-stp-inv : ∀ {n} {M₁ M₂ N : Trm n}
                  → Σ[ Trm n ] (app (app M₁ M₂) N ⟶_)
                    → Σ[ Trm n ] (λ x → app M₁ M₂ ⟶ x + N ⟶ x)
  βappapp-stp-inv {n} {M₁} {M₂} {N} z =
    [ ⟨ pj1 ∣∣ (λ u → inl (prj1 (pj1 (pj2 u)))) ⟩
    ∣ ⟨ pj1 ∣∣ (λ u → inr (prj1 (pj1 (pj2 u)))) ⟩ ]
    (βappapp-inv (pj2 z))

  βappapp-stp-invrt : ∀ {n} {M₁ M₂ N : Trm n} → is-invrt (βappapp-stp {n} {M₁} {M₂} {N})
  βappapp-stp-invrt {n} {M₁} {M₂} {N} = βappapp-stp-inv {n} {M₁} {M₂} {N} ,, (eq1 , eq2)
    where eq1 : ∀ z → βappapp-stp-inv (βappapp-stp z) == z
          eq1 (P ,, u) = +ind (λ v → βappapp-stp-inv (βappapp-stp (P ,, v)) == P ,, v)
                              (λ _ → =rf)
                              (λ _ → =rf)
                              u         
          eq2 : ∀ z → βappapp-stp (βappapp-stp-inv z) == z
          eq2 z = +ind (λ u → βappapp-stp ([ ⟨ pj1 ∣∣ (λ u → inl (prj1 (pj1 (pj2 u)))) ⟩
                                            ∣ ⟨ pj1 ∣∣ (λ u → inr (prj1 (pj1 (pj2 u)))) ⟩ ] u)
                               == z)
                       (λ w → =Σchar (prj2 (pj1 (pj2 w))) (pj2 (pj2 w)))
                       (λ w → =Σchar (prj2 (pj1 (pj2 w))) (pj2 (pj2 w)))
                       (βappapp-inv (pj2 z))

  βappapp-invrt : ∀ {n} {M₁ M₂ N : Trm n} → is-invrt (βapp-stp {n} {app M₁ M₂} {N})
  βappapp-invrt {n} {M₁} {M₂} {N} = inv-trn-pre (λ _ → =rf)
                                                (βappapp-stp-med-invrt {n} {M₁} {M₂} {N})
                                                (βappapp-stp-invrt {n} {M₁} {M₂} {N})

  βappapp-eqv : ∀ {n} {M₁ M₂ N : Trm n} → is-equiv (βapp-stp {n} {app M₁ M₂} {N})
  βappapp-eqv {n} {M₁} {M₂} {N} = invrt-is-eqv (βappapp-invrt {n} {M₁} {M₂} {N})

  -- Inverting βapp when first term is lam

  βapplam-stp-med : ∀ {n} {M : Trm (suc n)} {N : Trm n}
                  → N₁ + Σ[ Trm (suc n) ] (M ⟶_) + Σ[ Trm n ] (N ⟶_)
                         → Σ[ Trm (suc n) ] (λ x → lam x == lam M)
                             + Σ[ Trm n ] (lam M ⟶_) + Σ[ Trm n ] (N ⟶_)
  βapplam-stp-med {n} {M} {N} =
   [ inl ∘ (λ _ → (M ,, =rf))
   ∥ inrl ∘ βlam-stp -- = ⟨ lam ∘ pj1 ∣∣ (λ z → βlam (pj2 z)) ⟩
   ∥ inrr
   ]

  βapplam-stp-med-invrt : ∀ {n} {M : Trm (suc n)} {N : Trm n}
                            → is-invrt (βapplam-stp-med {n} {M} {N})
  βapplam-stp-med-invrt {n} {M} {N} =
    equiv-is-invrt (+eqv3 eqv₁ (βlam-eqv {n} {M}) id-is-eqv)
    where f₁ : N₁ → Σ[ Trm (suc n) ] (λ x → lam x == lam M)
          f₁ = λ _ → M ,, =rf
          lamaux : Σ[ Trm (suc n) ] (_== M) → Σ[ Trm (suc n) ] (λ x → lam x == lam M)
          lamaux = ⟨ pj1 ∣∣ (λ z → =ap lam (pj2 z)) ⟩
          lamaux-inv : is-invrt lamaux
          lamaux-inv = ⟨ pj1 ∣∣ (λ z → lam-inj (pj2 z)) ⟩
                       ,, ((λ z → =Σover (prj2 (pj2 lam-inj-inv) (pj2 z)))
                          , λ z → =Σover (prj1 (pj2 lam-inj-inv) (pj2 z)))
          eqv₁ : is-equiv f₁
          eqv₁ = cntr-N₁-fnc-is-eqv (eqv-cntr-is-cntr (=η⁻¹ M) (invrt-is-eqv lamaux-inv)) f₁

  βapplam-stp : ∀ {n} {M : Trm (suc n)} {N : Trm n}
                  → N₁ + Σ[ Trm (suc n) ] (M ⟶_) + Σ[ Trm n ] (N ⟶_)
                      → Σ[ Trm n ] (app (lam M) N ⟶_)
  βapplam-stp {n} {M} {N} = βapp-stp {M = lam M} ∘ βapplam-stp-med {n} {M} {N}

  βapplam-inv : ∀ {n M N P} (stp : app (lam {n} M) N ⟶ P)
                  → Σ[ subst-0 M N == P ]
                            (λ u → ((app (lam M) N ⟶_) ● u) (β M N) == stp)
                        + Σ[ Trm (suc n) ] ( λ x → Σ[ M ⟶ x × (app (lam x) N == P) ]
                    ( λ y → ((app (lam M) N ⟶_) ● (prj2 y)) (βappₗ (βlam (prj1 y))) == stp ))
                         + Σ[ Trm n ] ( λ x → Σ[ N ⟶ x × (app (lam M) x == P) ]
                           ( λ y → ((app (lam M) N ⟶_) ● (prj2 y)) (βappᵣ (prj1 y)) == stp ))
  βapplam-inv (β M N)              = inl (=rf ,, =rf)
  βapplam-inv (βappₗ (βlam stp))    = inr (inl (_ ,, (stp , =rf) ,, =rf))
  -- two induction steps are needed here to unify things
  βapplam-inv (βappᵣ stp)           = inr (inr (_ ,, (stp , =rf) ,, =rf))

  βapplam-stp-inv-aux : ∀ {n} {M : Trm (suc n)} {N P : Trm n} (stp : app (lam M) N ⟶ P)
                        → Σ[ subst-0 M N == P ]
                            (λ u → ((app (lam M) N ⟶_) ● u) (β M N) == stp)
                        + Σ[ Trm (suc n) ] ( λ x → Σ[ M ⟶ x × (app (lam x) N == P) ]
                    ( λ y → ((app (lam M) N ⟶_) ● (prj2 y)) (βappₗ (βlam (prj1 y))) == stp ))
                         + Σ[ Trm n ] ( λ x → Σ[ N ⟶ x × (app (lam M) x == P) ]
                           ( λ y → ((app (lam M) N ⟶_) ● (prj2 y)) (βappᵣ (prj1 y)) == stp ))
                        → N₁ + Σ[ Trm (suc n) ] (M ⟶_) + Σ[ Trm n ] (N ⟶_)
  βapplam-stp-inv-aux {n} {M} {N} {P} stp =
    [ inl ∘ (λ _ → 0₁) --∘ ⟨ (λ _ → P) ∣∣ pj1 ⟩
    ∥ inr ∘ inl ∘ ⟨ pj1 ∣∣ (λ w → prj1 (pj1 (pj2 w))) ⟩
    ∥ inr ∘ inr ∘ ⟨ pj1 ∣∣ (λ w → prj1 (pj1 (pj2 w))) ⟩
    ]

  βapplam-stp-inv : ∀ {n} {M : Trm (suc n)} {N : Trm n}
                      → Σ[ Trm n ] (app (lam M) N ⟶_)
                        → N₁ + Σ[ Trm (suc n) ] (M ⟶_) + Σ[ Trm n ] (N ⟶_)
  βapplam-stp-inv {n} {M} {N} z = βapplam-stp-inv-aux (pj2 z) (βapplam-inv (pj2 z))

  βapplam-stp-invrt : ∀ {n} {M : Trm (suc n)} {N : Trm n}
                  → is-invrt (βapplam-stp {n} {M} {N})
  βapplam-stp-invrt {n} {M} {N} = βapplam-stp-inv ,, (iddom , idcod)
    where iddom : ∀ v → βapplam-stp-inv (βapplam-stp {n} {M} {N} v) == v
          iddom = +ind3 (λ v → βapplam-stp-inv (βapplam-stp {n} {M} {N} v) == v)
                        (λ x → =ap inl (pj2 N₁-isContr x ⁻¹))
                        (λ z → =ap (inr ∘ inl) (Ση z))
                        (λ z → =ap (inr ∘ inr) (Ση z))
          idcod : ∀ z → βapplam-stp (βapplam-stp-inv {n} {M} {N} z) == z
          idcod z = +ind3 (λ v → βapplam-stp (βapplam-stp-inv-aux (pj2 z) v) == z)
                          (λ w  → =Σchar (pj1 w) (pj2 w))
                          (λ w → =Σchar (prj2 (pj1 (pj2 w))) (pj2 (pj2 w)))
                          (λ w → =Σchar (prj2 (pj1 (pj2 w))) (pj2 (pj2 w)))
                          (βapplam-inv (pj2 z))

  βapplam-invrt : ∀ {n} {M : Trm (suc n)} {N : Trm n} → is-invrt (βapp-stp {n} {lam M} {N})
  βapplam-invrt {n} {M} {N} = inv-trn-pre (λ _ → =rf)
                                          (βapplam-stp-med-invrt {n} {M} {N})
                                          (βapplam-stp-invrt {n} {M} {N})
  
  βapplam-eqv : ∀ {n} {M : Trm (suc n)} {N : Trm n} → is-equiv (βapp-stp {n} {lam M} {N})
  βapplam-eqv {n} {M} {N} = invrt-is-eqv (βapplam-invrt {n} {M} {N})

  -- patching the three cases toghether

  βapp-eqv : ∀ {n} {M N : Trm n} → is-equiv (βapp-stp {n} {M} {N})
  βapp-eqv {n} {M} {N} =
    [ (λ z → =transp (λ x → is-equiv (βapp-stp {M = x})) (pj2 z)
                                      (βappvar-eqv {n} {pj1 z} {N}))
    ∥ (λ z → =transp (λ x → is-equiv (βapp-stp {M = x})) (pj2 z)
                                      (βapplam-eqv {n} {pj1 z} {N}))
    ∥ (λ z → =transp (λ x → is-equiv (βapp-stp {M = x})) (pj2 z)
                                      (βappapp-eqv {n} {prj1 (pj1 z)} {prj2 (pj1 z)} {N}))
    ] (Trm-cases M)



  -- Some congruences of ⟶
  ⟶-rename : {n m : Nat}{M M' : Trm n}(f : Fin n → Fin m)
                 → M ⟶ M' → rename M f ⟶ rename M' f
  ⟶-rename f (β M N) =
    =transp (λ x → app (lam (rename M (liftFin f))) (rename N f) ⟶ x)
            (subst-0-rename M N f)
            (β (rename M (liftFin f)) (rename N f))
  ⟶-rename f (βlam redM) =
    βlam (⟶-rename (liftFin f) redM)
  ⟶-rename f (βappₗ redM) =
    βappₗ (⟶-rename f redM)
  ⟶-rename f (βappᵣ redM) =
    βappᵣ (⟶-rename f redM)
  ⟶-rename⁻¹ : ∀ {n m M} (f : Fin n → Fin m) {P} → rename M f ⟶ P
                 → Σ[ Trm n ] (λ x → (rename x f == P) × M ⟶ x)
  ⟶-rename⁻¹ {n} {m} {lam M} f {lam P} (βlam stp) =
    lam (pj1 (⟶-rename⁻¹ (liftFin f) stp))
    ,, (=ap lam (prj1 (pj2 (⟶-rename⁻¹ (liftFin f) stp)))
       , βlam (prj2 (pj2 (⟶-rename⁻¹ (liftFin f) stp))))
  ⟶-rename⁻¹ {n} {m} {app (var i) M₂} f {.(app (var (f i)) _)} (βappᵣ stp) =
    app (var i) (pj1 (⟶-rename⁻¹ f stp))
    ,, (=ap (app (var (f i))) (prj1 (pj2 (⟶-rename⁻¹ f stp)))
       , βappᵣ (prj2 (pj2 (⟶-rename⁻¹ f stp))))
  ⟶-rename⁻¹ {n} {m} {app (lam M₁) M₂} f {.(subst-all (rename M₁ (liftFin f)) (trmsect (rename M₂ f)))} (β .(rename M₁ (liftFin f)) .(rename M₂ f)) =
    subst-0 M₁ M₂
    ,, (subst-0-rename M₁ M₂ f ⁻¹
       , β M₁ M₂)
  ⟶-rename⁻¹ {n} {m} {app (lam M₁) M₂} f (βappₗ stp) =
    app (pj1 (⟶-rename⁻¹ f stp)) M₂
    ,, (=ap (λ x → app x (rename M₂ f)) (prj1 (pj2 (⟶-rename⁻¹ f stp)))
       , βappₗ (prj2 (pj2 (⟶-rename⁻¹ f stp))))
  ⟶-rename⁻¹ {n} {m} {app (lam M₁) M₂} f (βappᵣ stp) =
    app (lam M₁) (pj1 (⟶-rename⁻¹ f stp))
    ,, (=ap (app (lam (rename M₁ (liftFin f)))) (prj1 (pj2 (⟶-rename⁻¹ f stp)))
       , βappᵣ (prj2 (pj2 (⟶-rename⁻¹ f stp))))
  ⟶-rename⁻¹ {n} {m} {app (app M₁₁ M₁₂) M₂} f (βappₗ stp) =
    app (pj1 (⟶-rename⁻¹ f stp)) M₂
    ,, (=ap (λ x → app x (rename M₂ f)) (prj1 (pj2 (⟶-rename⁻¹ f stp)))
       , βappₗ (prj2 (pj2 (⟶-rename⁻¹ f stp))))
  ⟶-rename⁻¹ {n} {m} {app (app M₁₁ M₁₂) M₂} f (βappᵣ stp) =
    app (app M₁₁ M₁₂) (pj1 (⟶-rename⁻¹ f stp))
    ,, (=ap (app (app (rename M₁₁ f) (rename M₁₂ f))) (prj1 (pj2 (⟶-rename⁻¹ f stp)))
       , βappᵣ (prj2 (pj2 (⟶-rename⁻¹ f stp))))

  ⟶-ext : ∀ {n M M'} → M ⟶ M' → ext {n} M ⟶ ext M'
  ⟶-ext = ⟶-rename fs
  ⟶-extk : ∀ k {n M M'} → M ⟶ M' → ext[ k ] {n} M ⟶ ext[ k ] M'
  ⟶-extk zero = id
  ⟶-extk (suc k) = ⟶-ext ∘ ⟶-extk k
  ⟶-ext⁻¹g : ∀ {n M P} → ext {n} M ⟶ P → Σ[ Trm n ] (λ x → (ext x == P) × M ⟶ x)
  ⟶-ext⁻¹g stp = ⟶-rename⁻¹ fs stp
  ⟶-extk⁻¹g : ∀ k {n M P} → ext[ k ] {n} M ⟶ P → Σ[ Trm n ] (λ x → (ext[ k ] x == P) × M ⟶ x)
  ⟶-extk⁻¹g zero =
    λ s → _ ,, (=rf , s)
  ⟶-extk⁻¹g (suc k) {n} {M = M} {P} stp =
    N ,, (eq , (prj2 (pj2 (⟶-extk⁻¹g k (prj2 (pj2 (⟶-ext⁻¹g stp)))))))
    where N : Trm n
          N = pj1 (⟶-extk⁻¹g k (prj2 (pj2 (⟶-ext⁻¹g stp))))
          eq : ext (ext[ k ] N) == P
          eq = =ap ext (prj1 (pj2 (⟶-extk⁻¹g k (prj2 (pj2 (⟶-ext⁻¹g stp))))))
               • prj1 (pj2 (⟶-ext⁻¹g stp)) 
  ⟶-ext⁻¹ : ∀ {n M M'} → ext {n} M ⟶ ext {n} M' → M ⟶ M'
  ⟶-ext⁻¹ {n} {M} {M'} stp = ((M ⟶_) ● eq) (prj2 (pj2 (⟶-ext⁻¹g stp)))
    where eq : pj1 (⟶-ext⁻¹g stp) == M'
          eq = ext-inj (prj1 (pj2 (⟶-ext⁻¹g stp)))
  ⟶-extk⁻¹ : ∀ k {n M M'} → ext[ k ] {n} M ⟶ ext[ k ] {n} M' → M ⟶ M'
  ⟶-extk⁻¹ zero = id
  ⟶-extk⁻¹ (suc k) = ⟶-extk⁻¹ k ∘ ⟶-ext⁻¹

  ⟶-subst-all : {n m : Nat}(f : Fin n → Trm m){M M' : Trm n}
                    → M ⟶ M' → subst-all M f ⟶ subst-all M' f
  ⟶-subst-all f {app (lam M) N} (β M N) =
    =transp (λ x → app (lam (subst-all M (wlift f))) (subst-all N f) ⟶ x)
            (subst-0-dist M N f)
            (β (subst-all M (wlift f)) (subst-all N f))
  ⟶-subst-all f {lam M} (βlam redM) =
    βlam (⟶-subst-all (wlift f) redM)
  ⟶-subst-all f (βappₗ redM) =
    βappₗ (⟶-subst-all f redM)
  ⟶-subst-all f {app M N} (βappᵣ redM) =
    βappᵣ (⟶-subst-all f redM)
  -- making the term explicit in the third clause would make
  -- the last two clauses light grey,
  -- meaning that they do NOT hold definitionally
  -- this also happens in subject reduction (simpleTT.agda)

  ⟶-trmsect : {n : Nat}{N N' : Trm n} → N ⟶ N'
                → ∀ i → trmsect N i ⟶⋆ trmsect N' i
  ⟶-trmsect stpN fz = ⟶⋆in stpN
  ⟶-trmsect stpN (fs i) = ⟶⋆rfl (var i)


  -- Some congruences of ⟶⋆
  ⟶⋆-lam : {n : Nat}{M M' : Trm (suc n)} → M ⟶⋆ M' → lam M ⟶⋆ lam M'
  ⟶⋆-lam (tcrfl M) = ⟶⋆rfl (lam M)
  ⟶⋆-lam (tccnc red stp) = ⟶⋆cnc (⟶⋆-lam red) (βlam stp)
  ⟶⋆-app : {n : Nat}{M M' N N' : Trm n} → M ⟶⋆ M' → N ⟶⋆ N' → app M N ⟶⋆ app M' N'
  ⟶⋆-app (tcrfl M) (tcrfl N) = ⟶⋆rfl (app M N)
  ⟶⋆-app (tcrfl M) (tccnc redN stpN) = ⟶⋆tr (⟶⋆-app (⟶⋆rfl M) redN) (⟶⋆in (βappᵣ stpN))
  ⟶⋆-app (tccnc redM stpM) redN = ⟶⋆tr (⟶⋆-app redM redN) (⟶⋆in (βappₗ stpM))

  ⟶⋆-trmsect : {n : Nat}{N N' : Trm n} → N ⟶⋆ N'
                → ∀ i → trmsect N i ⟶⋆ trmsect N' i
  ⟶⋆-trmsect redN fz = redN
  ⟶⋆-trmsect redN (fs i) = ⟶⋆rfl (var i)

  ⟶⋆-rename : {n m : Nat}{M M' : Trm n}(f : Fin n → Fin m)
                 → M ⟶⋆ M' → rename M f ⟶⋆ rename M' f
  ⟶⋆-rename {M = M} {M} f (tcrfl M) =
    ⟶⋆rfl (rename M f)
  ⟶⋆-rename {M = M} {N} f (tccnc red stp) = tccnc (⟶⋆-rename f red) (⟶-rename f stp)

  ⟶⋆-ext : {n : Nat}{M M' : Trm n}
              → M ⟶⋆ M' → ext M ⟶⋆ ext M'
  ⟶⋆-ext {M = M} redM = ⟶⋆-rename fs redM

  ⟶⋆-wlift : {n m : Nat}{f f' : Fin n → Trm m}
                → (∀ i → f i ⟶⋆ f' i) → ∀ i → wlift f i ⟶⋆ wlift f' i
  ⟶⋆-wlift {f = f} redf fz = ⟶⋆rfl (var fz)
  ⟶⋆-wlift {f = f} redf (fs i) = ⟶⋆-ext (redf i)


  ⟶⋆-subst-allᵣ : {n m : Nat}(M : Trm n){f f' : Fin n → Trm m}
                    → (∀ i → f i ⟶⋆ f' i) → subst-all M f ⟶⋆ subst-all M f'
  ⟶⋆-subst-allᵣ (var x) {f} {f'} redf =
    redf x
  ⟶⋆-subst-allᵣ (lam M) {f} {f'} redf =
    ⟶⋆-lam (⟶⋆-subst-allᵣ M {wlift f} {wlift f'} (⟶⋆-wlift redf ))
  ⟶⋆-subst-allᵣ (app M N) {f} {f'} redf =
    ⟶⋆-app (⟶⋆-subst-allᵣ M redf) (⟶⋆-subst-allᵣ N redf)


  ⟶⋆-subst-all : {n m : Nat}{M M' : Trm n}{f f' : Fin n → Trm m}
                    → M ⟶⋆ M' → (∀ i → f i ⟶⋆ f' i)
                      → subst-all M f ⟶⋆ subst-all M' f'
  ⟶⋆-subst-all {M = M} {f = f} {f'} (tcrfl M) redf =
    ⟶⋆-subst-allᵣ M redf 
  ⟶⋆-subst-all {M = M} {f = f} {f'} (tccnc redM stpM) redf =
    ⟶⋆cnc (⟶⋆-subst-all redM redf) (⟶-subst-all f' stpM)


  ⟶⋆-subst-0 : {n : Nat}{M M' : Trm (suc n)}{N N' : Trm n} → M ⟶⋆ M' → N ⟶⋆ N'
                    → subst-0 M N ⟶⋆ subst-0 M' N'
  ⟶⋆-subst-0 redM redN = ⟶⋆-subst-all redM (⟶⋆-trmsect redN)


  -- Some congruences of ≡>
  ≡>-var : {n : Nat} → {i j : Fin n} → var i ≡> var j → i == j
  ≡>-var ≡>rfl = =rf

  ≡>-liftFin : {n m : Nat}{f f' : Fin n → Fin m}
                  → (∀ i → var (f i) ≡> var (f' i))
                    → ∀ i → var (liftFin f i) ≡> var (liftFin f' i)
  ≡>-liftFin redv fz =
    ≡>rfl {M = var fz}
  ≡>-liftFin {f = f} redv (fs i) =
    =transp (λ x → (var (fs (f i)) ≡> var (fs x))) (≡>-var (redv i)) ≡>rfl 

  ≡>-trmsect : {n : Nat}{M M' : Trm n} → M ≡> M'
                 → ∀ i → trmsect M i ≡> trmsect M' i
  ≡>-trmsect redM fz = redM
  ≡>-trmsect redM (fs i) = ≡>rfl

  -- It seems that Agda does not accet non-canonical terms as explicit arguments
  -- in inductive definitions (which makes sense),
  -- but this means that M' and N' cannot be named in the inductive definition
  -- of ≡>-rename as they appear in subst-0 M' N'.
  -- Therefore the followingterm is needed to make M' and N' explicit
  -- and avoid yellow in ≡>-rename.
  ≡>-rename-aux : {n m : Nat}{M M' : Trm (suc n)}{N N' : Trm n}(f f' : Fin n → Fin m)
                        → M ≡> M' → N ≡> N' → rename M (liftFin f) ≡> rename M' (liftFin f')
                          → rename N f ≡> rename N' f'
                            → app (lam (rename M (liftFin f))) (rename N f)
                                                                ≡> rename (subst-0 M' N') f'
  ≡>-rename-aux {M = M} {M'} {N} {N'} f f' redM redN redsM redsN =
    =transp (λ x → _ ≡> x) (subst-0-rename M' N' f') (≡>red redsM redsN)

  ≡>-rename : {n m : Nat}{M M' : Trm n}(f f' : Fin n → Fin m)
                 → M ≡> M' → (∀ i → var (f i) ≡> var (f' i))
                   → rename M f ≡> rename M' f'
  ≡>-rename {M = var x} f f' ≡>rfl redf =
    redf x
  ≡>-rename {M = lam M} f f' ≡>rfl redf =
    ≡>lam (≡>-rename (liftFin f) (liftFin f') ≡>rfl (≡>-liftFin redf))
  ≡>-rename {M = app M₁ M₂} f f' ≡>rfl redf =
    ≡>app (≡>-rename f f' ≡>rfl redf) (≡>-rename f f' ≡>rfl redf)
  ≡>-rename {M = app (lam M₁) M₂} f f' (≡>red redM₁ redM₂) redf =
    ≡>-rename-aux f f' redM₁ redM₂ (≡>-rename (liftFin f) (liftFin f') redM₁ (≡>-liftFin redf))
                                   (≡>-rename f f' redM₂ redf)
  ≡>-rename {M = lam M} f f' (≡>lam redM) redf =
    ≡>lam (≡>-rename (liftFin f) (liftFin f') redM (≡>-liftFin redf))
  ≡>-rename {M = app M₁ M₂} f f' (≡>app redM₁ redM₂) redf =
    ≡>app (≡>-rename f f' redM₁ redf) (≡>-rename f f' redM₂ redf)


  ≡>-ext : {n : Nat}{M M' : Trm n}
                 → M ≡> M' → ext M ≡> ext M'
  ≡>-ext {M = M} redM = ≡>-rename fs fs redM (λ i → ≡>rfl {M = var (fs i)})


  ≡>-wlift : {n m : Nat}{f f' : Fin n → Trm m}
                → (∀ i → f i ≡> f' i) → ∀ i → wlift f i ≡> wlift f' i
  ≡>-wlift {f = f} {f'} redf fz = ≡>rfl {M = var fz}
  ≡>-wlift {f = f} {f'} redf (fs i) = ≡>-ext (redf i)

  -- It seems that Agda does not accet non-canonical terms as explicit arguments
  -- in inductive definitions (which makes sense), but this means that M' and N' cannot be named
  -- in the inductive definition of ≡>-subst-all as they appear in subst-0 M' N'.
  -- This term is needed to make M' and N' explicit and avoid yellow in ≡>-subst-all.
  ≡>-subst-all-aux : {n m : Nat}{M M' : Trm (suc n)}{N N' : Trm n}{f f' : Fin n → Trm m}
                        → M ≡> M' → N ≡> N' → subst-all M (wlift f) ≡>  subst-all M' (wlift f')
                          → subst-all N f ≡>  subst-all N' f'
                            → app (lam (subst-all M (wlift f))) (subst-all N f)
                                                                ≡> subst-all (subst-0 M' N') f'
  ≡>-subst-all-aux {M = M} {M'} {N} {N'} {f} {f'} redM redN redsM redsN =
    =transp (λ x → _ ≡> x) (subst-0-dist M' N' f') (≡>red redsM redsN)

  ≡>-subst-all : {n m : Nat}{M M' : Trm n}{f f' : Fin n → Trm m}
                    → M ≡> M' → (∀ i → f i ≡> f' i)
                      → (subst-all M f) ≡> (subst-all M' f')
  ≡>-subst-all {M = var x} {_} {f} {f'} ≡>rfl redf =
    redf x
  ≡>-subst-all {M = lam M} {_} {f} {f'} ≡>rfl redf =
    ≡>lam (≡>-subst-all {f = wlift f} {wlift f'} (≡>rfl {M = M}) (≡>-wlift redf))
  ≡>-subst-all {M = app M₁ M₂} {_} {f} {f'} ≡>rfl redf =
    ≡>app (≡>-subst-all (≡>rfl {M = M₁}) redf) (≡>-subst-all (≡>rfl {M = M₂}) redf)
  ≡>-subst-all {M = app (lam M₁) M₂} {_} {f} {f'} (≡>red redM₁ redM₂) redf =
    ≡>-subst-all-aux redM₁ redM₂ (≡>-subst-all {f = wlift f} {wlift f'} redM₁ (≡>-wlift redf))
                                 (≡>-subst-all redM₂ redf)
  ≡>-subst-all {M = lam M} {_} {f} {f'} (≡>lam redM) redf =
    ≡>lam (≡>-subst-all {f = wlift f} {wlift f'} redM (≡>-wlift redf))
  ≡>-subst-all {M = app M₁ M₂} {_} {f} {f'} (≡>app redM₁ redM₂) redf =
    ≡>app (≡>-subst-all redM₁ redf) (≡>-subst-all redM₂ redf)

  ≡>-subst-0 : {n : Nat}{M M' : Trm (suc n)}{N N' : Trm n} → M ≡> M' → N ≡> N'
                  → subst-0 M N ≡> subst-0 M' N'
  ≡>-subst-0 {_} {M} red₁ red₂ = ≡>-subst-all red₁ (≡>-trmsect red₂)


  -- order between reduction relations
  ⟶<≡> : {n : Nat}{M N : Trm n} → M ⟶ N → M ≡> N
  ⟶<≡> {M = app (lam M) N} (β M N) =
    ≡>red (≡>rfl {M = M}) (≡>rfl {M = N})
  ⟶<≡> {M = lam M} {lam M'} (βlam stp) =
    ≡>lam (⟶<≡> stp)
  ⟶<≡> {M = _} {app _ N} (βappₗ stp) =
    ≡>app (⟶<≡> stp) (≡>rfl {M = N})
  ⟶<≡> {M = app M N} (βappᵣ stp) =
    ≡>app (≡>rfl {M = M}) (⟶<≡> stp)
  -- making the term `M` explicit in the third clause
  -- would make the last two light grey,
  -- meaning that they do NOT hold definitionally
  -- this also happens in `⟶-subst-all` (LambdaCalculus.agda)


  ≡><⟶⋆ : {n : Nat}{M N : Trm n} → M ≡> N → M ⟶⋆ N
  ≡><⟶⋆ {_} {M} ≡>rfl =
    ⟶⋆rfl M
  ≡><⟶⋆ {_} {app (lam M) N} (≡>red red₁ red₂) =
    ⟶⋆tr (⟶⋆in (β M N)) (⟶⋆-subst-0 (≡><⟶⋆ red₁) (≡><⟶⋆ red₂))
  ≡><⟶⋆ {_} {lam M} {lam M'} (≡>lam red) =
    ⟶⋆-lam (≡><⟶⋆ red)
  ≡><⟶⋆ {_} {app M N} (≡>app red₁ red₂) =
    ⟶⋆-app (≡><⟶⋆ red₁) (≡><⟶⋆ red₂)

  -- ⟶⋆ and ≡>⋆ are the same relation
  ≡>⋆<⟶⋆ : {n : Nat}{M N : Trm n} → M ≡>⋆ N → M ⟶⋆ N
  ≡>⋆<⟶⋆ = rtclos-min _≡>_ _⟶⋆_ (λ {M} → ⟶⋆rfl M) ⟶⋆tr ≡><⟶⋆
  ⟶⋆<≡>⋆ : {n : Nat}{M N : Trm n} → M ⟶⋆ N → M ≡>⋆ N
  ⟶⋆<≡>⋆ = rtclos-fun (λ M N → ⟶<≡> {M = M} {N})


  -- proof that the parallel reduction relation ≡> has the diamond property

  ≡>-Sink : ∀ {n} → (N L : Trm n) → Set
  ≡>-Sink = Sink _≡>_
  ≡>⋄trm : {n : Nat}{N L : Trm n} → ≡>-Sink N L → Trm n
  ≡>⋄trm = ⋄trm (_≡>_)
  ≡>⋄red₁ : {n : Nat}{N L : Trm n} → (snk : ≡>-Sink N L) → N ≡> (≡>⋄trm snk)
  ≡>⋄red₁ = ⋄red₁ (_≡>_)
  ≡>⋄red₂ : {n : Nat}{N L : Trm n} → (snk : ≡>-Sink N L) → L ≡> (≡>⋄trm snk)
  ≡>⋄red₂ = ⋄red₂ (_≡>_)

  -- some lemmas for proving that ≡> has the diamond property.
  -- (Mainly to avoid yellow, see comments above.)
  ≡>-has-diamond-aux-rfl : {n : Nat}{M M' : Trm (suc n)}{N N' : Trm n}
                              → M ≡> M' → N ≡> N' → ≡>-Sink (subst-0 M' N') (app (lam M) N)
  ≡>-has-diamond-aux-rfl {M = M} {M'} {N} {N'} redM redN =
    subst-0 M' N' ,, (≡>rfl , ≡>red redM redN)

  ≡>-has-diamond-aux-red : {n : Nat}{M M' M'' : Trm (suc n)}{N N' N'' : Trm n}
                              → M ≡> M' → N ≡> N' → M ≡> M'' → N ≡> N''
                                → ≡>-Sink M' M'' → ≡>-Sink N' N''
                                  → ≡>-Sink (subst-0 M' N') (subst-0 M'' N'')
  ≡>-has-diamond-aux-red redMₗ redNₗ redMᵣ redNᵣ snkM snkN =
    snk ,, ( ≡>-subst-0 (≡>⋄red₁ snkM) (≡>⋄red₁ snkN) , ≡>-subst-0 (≡>⋄red₂ snkM) (≡>⋄red₂ snkN) )
    where snk : Trm _
          snk = subst-0 (≡>⋄trm snkM) (≡>⋄trm snkN)

  ≡>-has-diamond-aux-apprfl : {n : Nat}{M M' : Trm (suc n)}{N N' N'' : Trm n}
                                 → M ≡> M' → N ≡> N' →  N ≡> N'' → ≡>-Sink N' N''
                                  → ≡>-Sink (subst-0 M' N') (app (lam M) N'')
  ≡>-has-diamond-aux-apprfl {M = M} {M'} redM redNₗ redNᵣ snkN =
    subst-0 M' (≡>⋄trm snkN) ,, (≡>-subst-0 (≡>rfl {M = M'}) (≡>⋄red₁ snkN)
                                , ≡>red redM (≡>⋄red₂ snkN) )

  ≡>-has-diamond-aux-applam : {n : Nat}{M M' M'' : Trm (suc n)}{N N' N'' : Trm n}
                                 → M ≡> M' → N ≡> N' → M ≡> M'' →  N ≡> N''
                                   → ≡>-Sink M' M'' → ≡>-Sink N' N''
                                  → ≡>-Sink (subst-0 M' N') (app (lam M'') N'')
  ≡>-has-diamond-aux-applam redMₗ redNₗ redMᵣ redNᵣ snkM snkN =
    subst-0 (≡>⋄trm snkM) (≡>⋄trm snkN) ,, (≡>-subst-0 (≡>⋄red₁ snkM) (≡>⋄red₁ snkN)
                                           , ≡>red (≡>⋄red₂ snkM) (≡>⋄red₂ snkN))
  

  -- ≡> has the diamond property
  ≡>-has-diamond : diamond-prop _≡>_
  -- by induction on the left ≡>-reduction
  -- rfl
  ≡>-has-diamond {_} {M} {_} {L}  ≡>rfl red =
    L ,, (red , ≡>rfl)
  -- red
  ≡>-has-diamond {_} {app (lam M₁) M₂} (≡>red red₁ red₂) ≡>rfl =
    ≡>-has-diamond-aux-rfl red₁ red₂
  ≡>-has-diamond {_} {app (lam M₁) M₂} (≡>red red₁₁ red₁₂) (≡>red red₂₁ red₂₂) =
    ≡>-has-diamond-aux-red red₁₁ red₁₂ red₂₁ red₂₂ (≡>-has-diamond red₁₁ red₂₁)
                                                   (≡>-has-diamond red₁₂ red₂₂)
  ≡>-has-diamond {_} {app (lam M₁) M₂} (≡>red red₁₁ red₁₂) (≡>app ≡>rfl red₂) =
    ≡>-has-diamond-aux-apprfl red₁₁ red₁₂ red₂ (≡>-has-diamond red₁₂ red₂)
  ≡>-has-diamond {_} {app (lam M₁) M₂} (≡>red red₁₁ red₁₂) (≡>app (≡>lam red₂₁) red₂₂) =
    ≡>-has-diamond-aux-applam red₁₁ red₁₂ red₂₁ red₂₂ (≡>-has-diamond red₁₁ red₂₁)
                                                      (≡>-has-diamond red₁₂ red₂₂)
  -- lam
  ≡>-has-diamond {_} {lam M} {lam M'} (≡>lam red₁) ≡>rfl =
    lam M' ,, (≡>rfl , ≡>lam red₁)
  ≡>-has-diamond {_} {lam M} {lam M'} {lam M''} (≡>lam red₁) (≡>lam red₂) =
    lam (≡>⋄trm M-snk) ,, (≡>lam (≡>⋄red₁ M-snk) , ≡>lam (≡>⋄red₂ M-snk))
    where M-snk : ≡>-Sink M' M''
          M-snk = ≡>-has-diamond red₁ red₂
  -- app
  ≡>-has-diamond {n} {app M₁ M₂} {app M₁' M₂'} (≡>app red₁ red₂) ≡>rfl =
    app M₁' M₂' ,, (≡>rfl , ≡>app red₁ red₂)
  ≡>-has-diamond {n} {app (lam M₁) M₂} (≡>app ≡>rfl red₁) (≡>red red₂₁ red₂₂) =
    opsink _≡>_ (≡>-has-diamond-aux-apprfl red₂₁ red₂₂ red₁ (≡>-has-diamond red₂₂ red₁))
  ≡>-has-diamond {n} {app (lam M₁) M₂} (≡>app (≡>lam red₁₁) red₁₂) (≡>red red₂₁ red₂₂) =
    opsink _≡>_ (≡>-has-diamond-aux-applam red₂₁ red₂₂ red₁₁ red₁₂ (≡>-has-diamond red₂₁ red₁₁)
                                                                   (≡>-has-diamond red₂₂ red₁₂))
  ≡>-has-diamond {n} {app M₁ M₂}{app M₁' M₂'}{app M₁'' M₂''} (≡>app red₁₁ red₁₂) (≡>app red₂₁ red₂₂) =
    app (≡>⋄trm M₁-snk) (≡>⋄trm M₂-snk) ,, (≡>app (≡>⋄red₁ M₁-snk) (≡>⋄red₁ M₂-snk)
                                           , ≡>app (≡>⋄red₂ M₁-snk) (≡>⋄red₂ M₂-snk))
    where M₁-snk : ≡>-Sink M₁' M₁''
          M₁-snk = ≡>-has-diamond red₁₁ red₂₁
          M₂-snk : ≡>-Sink M₂' M₂''
          M₂-snk = ≡>-has-diamond red₁₂ red₂₂

  -- ≡>⋆ has the diamond property
  ≡>⋆-has-diamond : diamond-prop _≡>⋆_
  ≡>⋆-has-diamond = rtclosure-diamond _≡>_ ≡>-has-diamond


  -------------------------
  -- Church-Rosser Theorem
  -------------------------
  Church-Rosser :  diamond-prop _⟶⋆_
  Church-Rosser {M = M} {N} {L} red₁ red₂ =
    pj1 ≡>⋆snk ,, (≡>⋆<⟶⋆ (prj1 (pj2 ≡>⋆snk)) , ≡>⋆<⟶⋆ (prj2 (pj2 ≡>⋆snk)))
    where ≡>⋆snk : Sink _≡>⋆_ N L
          ≡>⋆snk = ≡>⋆-has-diamond (⟶⋆<≡>⋆ red₁) (⟶⋆<≡>⋆ red₂)

  ----------------
  -- normal forms
  ----------------

  is-normal : ∀ {n} → Trm n → Set
  is-normal M = ∀ N → ¬ (M ⟶ N)

  -- a value is a canonical normal term
  data is-value {n : Nat} : Trm n → Set where
    val-lam : ∀ {M} → is-normal M → is-value (lam M)

  nrm-var : ∀ {n i} → is-normal (var {n} i)
  nrm-var {n} {i} = ¬var⟶ i
  nrm-lam : ∀ {n M} → is-normal {n} (lam M) → is-normal M
  nrm-lam nrm = λ N stp → nrm (lam N) (βlam stp)
  nrm-lam-inv : ∀ {n M} → is-normal {suc n} M → is-normal (lam M)
  nrm-lam-inv nrm (lam N) (βlam stp) = nrm N stp
  
  nrm-appₗ : ∀ {n M N} → is-normal {n} (app M N) → is-normal M
  nrm-appₗ nrm = λ M stp → nrm (app M _) (βappₗ stp)
  nrm-appᵣ : ∀ {n M N} → is-normal {n} (app M N) → is-normal N
  nrm-appᵣ nrm = λ N stp → nrm (app _ N) (βappᵣ stp)
  -- the converse holds only iff `M` is not `lam`

  nrm-rename : ∀ {n m} (f : Fin n → Fin m) {M} → is-normal (rename M f) → is-normal M
  nrm-rename f {M} fMnrm N stp = fMnrm (rename N f) (⟶-rename f stp)
  nrm-ext : ∀ {n M} → is-normal (ext {n} M) → is-normal M
  nrm-ext {n} = nrm-rename (fs {n})


  -- a term is strongly normalising if all its sequences of reductions terminate
  data isStrNrmₗₑᵥ {n : Nat} : Nat → Trm n → Set where
    strnrm-nrm : ∀ {M} → is-normal M → isStrNrmₗₑᵥ zero M
    strnrm-stp : ∀ {k M} → (∀ {N} → M ⟶ N → isStrNrmₗₑᵥ k N) → isStrNrmₗₑᵥ (suc k) M

  isStrNrm : ∀ {n} → Trm n → Set
  isStrNrm M = Σ[ Nat ] (λ x → isStrNrmₗₑᵥ x M)
  normal-isStrNrm : ∀ {n M} → is-normal {n} M → isStrNrm M
  normal-isStrNrm isnrm = zero ,, strnrm-nrm isnrm

  strnrmₗₑᵥ-rename : ∀ {n m} (f : Fin n → Fin m) {k M} → isStrNrmₗₑᵥ k (rename M f) → isStrNrmₗₑᵥ k M
  strnrmₗₑᵥ-rename f (strnrm-nrm isnrm) =
    strnrm-nrm (nrm-rename f isnrm)
  strnrmₗₑᵥ-rename f (strnrm-stp fnc) =
    strnrm-stp (λ {N} s → strnrmₗₑᵥ-rename f (fnc {rename N f} (⟶-rename f s)))
  strnrmₗₑᵥ-ext : ∀ {n k M} → isStrNrmₗₑᵥ k (ext {n} M) → isStrNrmₗₑᵥ k M
  strnrmₗₑᵥ-ext {n} = strnrmₗₑᵥ-rename (fs {n})

  strnrm-rename : ∀ {n m} (f : Fin n → Fin m) {M} → isStrNrm (rename M f) → isStrNrm M
  strnrm-rename f {M} fMsn = pj1 fMsn ,, strnrmₗₑᵥ-rename f (pj2 fMsn)
  strnrm-ext : ∀ {n M} → isStrNrm (ext {n} M) → isStrNrm M
  strnrm-ext {n} = strnrm-rename (fs {n})

  strnrm-upw : ∀ {n k M} → isStrNrmₗₑᵥ {n} k M → ∀ {l} → k ≤N l → isStrNrmₗₑᵥ l M
  strnrm-upw (strnrm-nrm nrmM) {zero} dq = strnrm-nrm nrmM
  strnrm-upw (strnrm-nrm nrmM) {suc l} dq = strnrm-stp (λ {N} stp → N₀ind (nrmM N stp))
  strnrm-upw (strnrm-stp snstp) {suc l} dq = strnrm-stp (λ {N} stp → strnrm-upw (snstp stp) dq)

  strnrm-⟶ₗₑᵥ : ∀ {k n M N} → isStrNrmₗₑᵥ {n} k M → M ⟶ N → isStrNrm N
  strnrm-⟶ₗₑᵥ {k} (strnrm-nrm nrmM) stp = N₀ind (nrmM _ stp) -- zero ,, 
  strnrm-⟶ₗₑᵥ {k = suc k} (strnrm-stp snstp) stp = k ,, snstp stp
  strnrm-⟶ : ∀ {n M N} → isStrNrm {n} M → M ⟶ N → isStrNrm N
  strnrm-⟶ {n} snM = strnrm-⟶ₗₑᵥ (pj2 snM)

  strnrmₗₑᵥ-lam : ∀ {n k M} → isStrNrmₗₑᵥ k (lam {n} M) → isStrNrmₗₑᵥ k M
  strnrmₗₑᵥ-lam (strnrm-nrm isnrm) = strnrm-nrm (nrm-lam isnrm)
  strnrmₗₑᵥ-lam (strnrm-stp fnc) = strnrm-stp (λ s → strnrmₗₑᵥ-lam (fnc (βlam s)))
  strnrmₗₑᵥ-appₗ : ∀ {n k M N} → isStrNrmₗₑᵥ k (app {n} M N) → isStrNrmₗₑᵥ k M
  strnrmₗₑᵥ-appₗ (strnrm-nrm isnrm) = strnrm-nrm (nrm-appₗ isnrm)
  strnrmₗₑᵥ-appₗ (strnrm-stp fnc) = strnrm-stp (λ s → strnrmₗₑᵥ-appₗ (fnc (βappₗ s)))
  strnrmₗₑᵥ-appᵣ : ∀ {n k M N} → isStrNrmₗₑᵥ k (app {n} M N) → isStrNrmₗₑᵥ k N
  strnrmₗₑᵥ-appᵣ (strnrm-nrm isnrm) = strnrm-nrm (nrm-appᵣ isnrm)
  strnrmₗₑᵥ-appᵣ (strnrm-stp fnc) = strnrm-stp (λ s → strnrmₗₑᵥ-appᵣ (fnc (βappᵣ s)))
  strnrm-lam : ∀ {n M} → isStrNrm (lam {n} M) → isStrNrm M
  strnrm-lam sn = pj1 sn ,, strnrmₗₑᵥ-lam (pj2 sn)
  strnrm-appₗ : ∀ {n M N} → isStrNrm (app {n} M N) → isStrNrm M
  strnrm-appₗ sn = pj1 sn ,, strnrmₗₑᵥ-appₗ (pj2 sn)
  strnrm-appᵣ : ∀ {n M N} → isStrNrm (app {n} M N) → isStrNrm N
  strnrm-appᵣ sn = pj1 sn ,, strnrmₗₑᵥ-appᵣ (pj2 sn)


  -- number of one step β-reductions from a term
  ⟶# : ∀ {n} → Trm n → Nat
  ⟶# (var i) = zero
  ⟶# (lam M) = ⟶# M
  ⟶# (app (var i) M₂) = ⟶# M₂
  ⟶# (app (lam M₁) M₂) = suc (⟶# M₁ +N ⟶# M₂)
  ⟶# (app (app M₁ N₁) M₂) = ⟶# (app M₁ N₁) +N ⟶# M₂
  -- the last clause looks fishy, but it seems OK for Agda
    
  ⟶#-lam= : ∀ {n} {P : Trm (suc n)} {M : Trm n} → lam P == M → ⟶# P == ⟶# M
  ⟶#-lam= {n} {P} {M} eq = =transp (λ x → ⟶# P == ⟶# x) eq =rf

  ⟶#app+lam : ∀ {n} ({M} N : Trm n)
                → Trm-is-lam M → ⟶# (app M N) == suc (⟶# M +N ⟶# N)
  ⟶#app+lam {n} {var i} N islam =          N₀ind (lam≠var _ _ (pj2 islam))
  ⟶#app+lam {n} {lam M} N islam =          =rf
  ⟶#app+lam {n} {app M₁ M₂} N islam =      N₀ind (lam≠app _ _ _ (pj2 islam))

  ⟶#app+not-lam : ∀ {n} ({M} N : Trm n)
                    → ¬ (Trm-is-lam M) → ⟶# M +N ⟶# N == ⟶# (app M N)
  ⟶#app+not-lam {n} {var i} N nlam =           =rf
  ⟶#app+not-lam {n} {lam M} N nlam =           N₀ind (nlam (M ,, =rf))
  ⟶#app+not-lam {n} {app M₁ M₂} N nlam =       =rf


  -- exact enumeration of one-step reductions of a term
  ⟶enmex : ∀ {n} M → Σ[ (Fin (⟶# M) → Σ[ Trm n ] (M ⟶_)) ] is-equiv

  -- enumeration of one step reductions from `var i`
  ⟶enmex {n} (var i) =
    venm ,, prop-eqv venm N₀-is-prop
                    (λ x y → N₀ind {λ _ → x == y} (empty y))
                    empty
    where venm :  Fin zero → Σ[ Trm n ] (var i ⟶_)
          venm = N₀ind
          empty :  Σ[ Trm n ] (var i ⟶_) → Fin zero
          empty (_ ,, ())

  -- enumeration of one step reductions from `lam M`
  ⟶enmex {n} (lam M) =
    lenm ,, leqv
    where ihf : Fin (⟶# M) → Σ[ Trm (suc n) ] (M ⟶_)
          ihf = pj1 (⟶enmex M)
          iheqv : is-equiv ihf
          iheqv = pj2 (⟶enmex M)
          lenm : Fin (⟶# (lam M)) → Σ[ Trm n ] (lam M ⟶_)
          lenm = βlam-stp {n} {M} ∘ ihf
          leqv : is-equiv lenm
          leqv = ∘eqv iheqv βlam-eqv

  -- enumeration of one step reductions from `app M N`
  -- doing induction on `M` is fishy (and Agda complains about termination if we do)
  -- since we would need to enumerate reductions from `app M₁ M₂` in the case `M = app M₁ M₂`
  -- hence try propositionally instead
  ⟶enmex {n} (app M N) =
    aenm ,, aeqv
    where ihNf : Fin (⟶# N) → Σ[ Trm n ] (N ⟶_)
          ihNf = pj1 (⟶enmex N)
          ihNeqv : is-equiv ihNf
          ihNeqv = pj2 (⟶enmex N)
          ihMf : Fin (⟶# M) → Σ[ Trm n ] (M ⟶_)
          ihMf = pj1 (⟶enmex M)
          ihMeqv : is-equiv ihMf
          ihMeqv = pj2 (⟶enmex M)
          Mlam-or-not : Trm-is-lam {n} M + ¬ (Trm-is-lam M)
          Mlam-or-not = lam-or-not M
          Dom-stp : Trm n → Set
          Dom-stp x =  Trm-is-lam x + Σ[ Trm n ] (x ⟶_) + Σ[ Trm n ] (N ⟶_)
          aux : Trm-is-lam {n} M + ¬ (Trm-is-lam M)
                  → Fin (⟶# (app M N)) → Dom-stp M
          aux (inl z) =
            Fin+N-fnc (λ (_ : N₁) → inl z) (inr ∘ Fin+N-fnc (inl ∘ ihMf) (inr ∘ ihNf))
            ∘ Fin-=to→ (⟶#app+lam N z)
          aux (inr z) =
            inr ∘ Fin+N-fnc (inl ∘ ihMf) (inr ∘ ihNf)
            ∘ Fin-=to→ (⟶#app+not-lam N z ⁻¹)

          aux-inv : is-invrt (aux Mlam-or-not)
          aux-inv =
            +ind (λ v → is-invrt (aux v))
                 (λ z → invrt-cmp-rf {f = Fin-=to→ (⟶#app+lam N z)}
                                        {Fin+N-fnc (λ (_ : N₁) → inl z)
                                                   (inr ∘ Fin+N-fnc (inl ∘ ihMf) (inr ∘ ihNf))}
                                        (Fin-=to→-invrt (⟶#app+lam N z))
                                        (Fin+N-fnc-invrt (equiv-is-invrt
                                                           (cntr-N₁-fnc-is-eqv (true-prop-is-contr
                                                              (idfull-fib-is-prop lam-inj-all M) z)
                                                                (λ _ → z)))
                                                         (Fin+N-fnc-invrt (equiv-is-invrt ihMeqv)
                                                                          (equiv-is-invrt ihNeqv))))
                 (λ z → invrt-cmp-rf {f = Fin-=to→ (⟶#app+not-lam N z ⁻¹)}
                                      {inr ∘ Fin+N-fnc (inl ∘ ihMf) (inr ∘ ihNf)}
                                      (Fin-=to→-invrt (⟶#app+not-lam N z ⁻¹))
                                      (+N₀invrtr z (Fin+N-fnc-invrt (equiv-is-invrt ihMeqv)
                                                                    (equiv-is-invrt ihNeqv)) ))
                 Mlam-or-not
          aenm : Fin (⟶# (app M N)) → Σ[ Trm n ] (app M N ⟶_)
          aenm = βapp-stp {n} {M} {N} ∘ aux Mlam-or-not
          aeqv : is-equiv aenm
          aeqv = ∘eqv (invrt-is-eqv aux-inv) (βapp-eqv {n} {M} {N})
  -- end of enumeration

  ⟶enm : ∀ {n} M → Fin (⟶# M) → Σ[ Trm n ] (M ⟶_)
  ⟶enm M = pj1 (⟶enmex M)
  ⟶enm-invrt : ∀ {n} M → is-invrt (⟶enm {n} M)
  ⟶enm-invrt M = equiv-is-invrt (pj2 (⟶enmex M))
  ⟶enm⁻¹ : ∀ {n} M → ∀ {N} → M ⟶ N → Fin (⟶# {n} M)
  ⟶enm⁻¹ M {N} stp = pj1 (⟶enm-invrt M) (N ,, stp)
  ⟶enm-idFin : ∀ {n} M i → ⟶enm⁻¹ {n} M (pj2 (⟶enm M i)) == i
  ⟶enm-idFin M i = =proof
    ⟶enm⁻¹ M (pj2 (⟶enm M i))       ==[ =ap (pj1 (⟶enm-invrt M)) (Ση (⟶enm M i)) ] /
    pj1 (⟶enm-invrt M) (⟶enm M i)   ==[ prj1 (pj2 (⟶enm-invrt M)) i ]∎
    i ∎
  ⟶enm-idTrm : ∀ {n} M {N} (stp : M ⟶ N) → ⟶enm {n} M (⟶enm⁻¹ M stp) == (N ,, stp)
  ⟶enm-idTrm M {N} stp = prj2 (pj2 (⟶enm-invrt M)) (N ,, stp)

  ⟶#0-¬Σ⟶ : ∀ {n M} → zero == ⟶# {n} M → ¬ (Σ[ Trm n ] (M ⟶_))
  ⟶#0-¬Σ⟶ {n} {M} eq = Fin-=to→ (eq ⁻¹) ∘ pj1 (⟶enm-invrt M)
  ⟶#0-is-nrm : ∀ {n M} → zero == ⟶# {n} M → is-normal M
  ⟶#0-is-nrm {n} {M} = ¬Σ→Π¬ ∘ ⟶#0-¬Σ⟶ {M = M}
  is-nrm-⟶#0 : ∀ {n M} → is-normal M → zero == ⟶# {n} M
  is-nrm-⟶#0 {n} {M} nrm =
    [ id
    ∣ (λ z → N₀ind (nrm _ (pj2 (⟶enm M (Fin-=to→ (pj2 z) fz)))))
    ] (Nat-dicot (⟶# M))
  ¬Σ⟶-⟶#0 : ∀ {n M} → ¬ (Σ[ Trm n ] (M ⟶_)) → zero == ⟶# {n} M
  ¬Σ⟶-⟶#0 {n} {M} = (is-nrm-⟶#0 {n} {M} ∘ ¬Σ→Π¬)

  Σ⟶-⟶#suc : ∀ {n M} → Σ[ Trm n ] (M ⟶_) → Σ[ Nat ] (λ x → suc x == ⟶# M)
  Σ⟶-⟶#suc {n} {M} z = Fin-inhab-is-suc (pj1 (⟶enm-invrt M) z)
  ⟶#suc-Σ⟶ : ∀ {n M} → Σ[ Nat ] (λ x → suc x == ⟶# M) → Σ[ Trm n ] (M ⟶_)
  ⟶#suc-Σ⟶ {n} {M} z = ⟶enm M (Fin-suc-is-inhab (pj2 z))

  -- it is decideble whether a term reduces or not
  ⟶Cases : ∀ {n} (M : Trm n) → Set
  ⟶Cases {n} M = is-normal M + Σ[ Trm n ] (M ⟶_)
  ⟶cases : ∀ {n} (M : Trm n) → ⟶Cases M
  ⟶cases {n} M =
    [ inl ∘ ⟶#0-is-nrm
    ∣ inr ∘ (λ z → ⟶enm M (Fin-=to→ (pj2 z) fz))
    ] (Nat-dicot (⟶# M))


  -- if all reducts of a term `M` are strongly normalising, then so is `M`
  -- first a couple of lemmas
  strnrm-bound-red : ∀ {n} {M N : Trm n} → (stp : M ⟶ N)
                       → (nn : (z : Σ[ Trm n ] (M ⟶_)) → isStrNrm {n} (pj1 z))
                         → Σ[ Nat ] (λ x → ∀ {N} → M ⟶ N → isStrNrmₗₑᵥ {n} x N)
  strnrm-bound-red {n} {M} {N} stp nn =
    (enm-#stps (pj1 mx)
    ,, λ {N} s → strnrm-upw (pj2 (nn (N ,, s)))
                     (=≤N {enm-#stps (pj1 (⟶enm-invrt M) (N ,, s))} {pj1 (nn (N ,, s))}
                          (=ap (λ z → pj1 (nn z)) (prj2 (pj2 (⟶enm-invrt M)) (N ,, s)))
                          (pj2 mx (⟶enm⁻¹ M s))))
    where k : Σ[ Nat ] (λ x → suc x == ⟶# M)
          k = Σ⟶-⟶#suc (N ,, stp)
          -- number of reduction steps for each reduct of `M`
          enm-#stps : Fin (⟶# M) → Nat
          enm-#stps i = pj1 (nn (⟶enm M i))
          enmk-#stps : Fin (suc (pj1 k)) → Nat
          enmk-#stps = enm-#stps ∘ Fin-=to→ (pj2 k)
          Fin-invrt : is-invrt (Fin-=to→ (pj2 k))
          Fin-invrt = Fin-=to→-invrt (pj2 k)
          mxsuc :  Σ[ Fin (suc (pj1 k)) ] (is-max≤N-Fin enmk-#stps)
          mxsuc = max≤N-Finsuc enmk-#stps
          mx : Σ[ Fin (⟶# M) ] (is-max≤N-Fin enm-#stps)
          mx = Fin-=to→ (pj2 k) (pj1 mxsuc)
               ,, λ i → =≤N {enmk-#stps (pj1 Fin-invrt i)} {enm-#stps i}
                             (=ap enm-#stps (prj2 (pj2 Fin-invrt) i))
                             (pj2 mxsuc (pj1 Fin-invrt i)) 

  strnrm-stp-any-red : ∀ {n} {M N : Trm n} → (stp : M ⟶ N)
                       → (nn : (z : Σ[ Trm n ] (M ⟶_)) → isStrNrm {n} (pj1 z))
                         → isStrNrm M
  strnrm-stp-any-red {n} {M} {N} stp nn =
    suc (pj1 allstps)
    ,, strnrm-stp (pj2 allstps)
    where allstps : Σ[ Nat ] (λ x → ∀ {N} → M ⟶ N → isStrNrmₗₑᵥ {n} x N)
          allstps = strnrm-bound-red stp nn

  strnrm-stp-any : ∀ {n M} → (∀ {N} → M ⟶ N → isStrNrm {n} N)
                      → isStrNrm M 
  strnrm-stp-any {n} {M} nn =
    [ (λ Mnrm → zero ,, strnrm-nrm Mnrm)
    ∣ (λ Ns → strnrm-stp-any-red (pj2 Ns) (λ z → nn (pj2 z)))
    ] (⟶cases M)

          

-- end of file
