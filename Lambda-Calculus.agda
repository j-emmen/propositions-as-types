{-# OPTIONS --allow-unsolved-metas #-}

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
                • prdη pp)

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
  #≠0 {n} {app M N} = #≠0 {n} {M} ∘ sum-0-is-0

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
  rename-ptw :  {n m : Nat}(M : Trm n){f f' : Fin n → Fin m}
                   → (∀ i → f i == f' i)
                     → rename M f == rename M f'
  rename-ptw (var x) {f} pf = =ap var (pf x)
  rename-ptw (lam M) {f} pf = =ap lam (rename-ptw M (liftFin-ptw pf))
  rename-ptw (app M N) {f} pf = =ap₂ app (rename-ptw M pf) (rename-ptw N pf)
  
  rename-act : {n m k : Nat}(M : Trm n)(f : Fin n → Fin m)(g : Fin m → Fin k)
                   → rename (rename M f) g == rename M (g ∘ f)
  rename-act (var x) f g = =rf
  rename-act (lam M) f g =
    =ap lam (=proof
      rename (rename M (liftFin f)) (liftFin g)  ==[ rename-act M (liftFin f) (liftFin g) ] /
      rename M (liftFin g ∘ liftFin f)           ==[ rename-ptw M (liftFin-cmp f g) ]∎
      rename M (liftFin (g ∘ f)) ∎)
  rename-act (app M₁ M₂) f g = =ap₂ app (rename-act M₁ f g) (rename-act M₂ f g)

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
  βlam-inv {n} {M} {lam N'} (βlam stp) = N' ,, ((stp , =rf) ,, =rf)
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

  βlam-stp : ∀ {n} {M : Trm (suc n)}
                      → Σ[ Trm (suc n) ] (M ⟶_) → Σ[ Trm n ] (lam M ⟶_)
  βlam-stp {n} {M} = ⟨ lam ∘ pj1 ∣∣ (λ MM → βlam {n} (pj2 MM)) ⟩
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
  -- we proceed by cases on M using propositional euality
  -- if we try a direct induction on `M`, Agda complains about termination

  βapp-stp : ∀ {n} {M N : Trm n}
               → Trm-is-lam M
                 + Σ[ Trm n ] (M ⟶_)
                 + Σ[ Trm n ] (N ⟶_)
                   → Σ[ Trm n ] (app M N ⟶_)
  βapp-stp {n} {M} {N} =
    [ (λ z → subst-0 (pj1 z) N
             ,, ((_⟶ subst-0 (pj1 z) N) ● =ap (λ x → app x N) (pj2 z)) (β (pj1 z) N))
    ∥ (λ z → app (pj1 z) N ,, βappₗ (pj2 z))
    ∥ (λ z → app M (pj1 z) ,, βappᵣ (pj2 z))
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
  βappvar-inv {n} {i} {M} {.(app (var i) _)} (βappᵣ stp) = _ ,, ((stp , =rf) ,, =rf)
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
    inl (_ ,, ((stp , =rf) ,, =rf))
  βappapp-inv {n} {M₁} {M₂} {N} {.(app (app M₁ M₂) _)} (βappᵣ stp) =
    inr (_ ,, ((stp , =rf) ,, =rf))

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
    eqv-is-invrt (+eqv3 eqv₁ (βlam-eqv {n} {M}) id-is-eqv)
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
  βapplam-inv (βappₗ (βlam stp))    = inr (inl (_ ,, ((stp , =rf) ,, =rf)))
  -- two induction steps are needed here to unify things
  βapplam-inv (βappᵣ stp)           = inr (inr (_ ,, ((stp , =rf) ,, =rf)))

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



{-
  βapp-case-β : ∀ {n} {M N P : Trm n} (stp : app M N ⟶ P) → Set
  βapp-case-β {n} {M} {N} {P} stp =
    Σ[ Trm (suc n) ]
     ( λ x → Σ[ (subst-0 x N == P) × (lam x == M) ]
           ( λ u → =transp₂ (λ x → app x N ⟶_) (prj2 u) (prj1 u) (β x N)
               ==  stp ))

  βapp-case-l : ∀ {n} {M N P : Trm n} (stp : app M N ⟶ P) → Set
  βapp-case-l {n} {M} {N} {P} stp =
    Σ[ Trm n ]
     ( λ x → Σ[ (app x N == P) × M ⟶ x ]
               ( λ z → ((app M N ⟶_) ● (prj1 z)) (βappₗ (prj2 z)) == stp ))

  βapp-case-r : ∀ {n} {M N P : Trm n} (stp : app M N ⟶ P) → Set
  βapp-case-r {n} {M} {N} {P} stp =
    Σ[ Trm n ]
     ( λ x → Σ[ (app M x == P) × N ⟶ x ]
               ( λ z → ((app M N ⟶_) ● (prj1 z)) (βappᵣ (prj2 z)) == stp ))

  -- βapp-inv will be defined as the map induced by `Trm-cases M : Trm-Cases M`
  βapp-inv-var : ∀ {n} {M N : Trm n} {i : Fin n} (eq : var i == M)
                       → {P : Trm n} → (stp : app M N ⟶ P)
                         → βapp-case-β stp + βapp-case-l stp + βapp-case-r stp
  βapp-inv-var {n} {M} {N} {i} eq {.(app _ N)} (βappₗ stp) =
    N₀ind (¬var⟶ i _ (((_⟶ _) ● (eq ⁻¹)) stp))
  βapp-inv-var {n} {M} {N} {i} eq {.(app M _)} (βappᵣ stp) =
    inr (inr (_ ,, ((=rf , stp) ,, =rf )))

  βapp-inv-lam-def : ∀ {n} {M : Trm (suc n)} {N : Trm n} {P : Trm n}
                   → (stp : app (lam M) N ⟶ P)
                       → βapp-case-β stp + βapp-case-l stp + βapp-case-r stp
  βapp-inv-lam-def {n} {M} {N} {.(subst-0 M N)} (β M N) =
    inl (M ,, ((=rf , =rf) ,, =rf))
  βapp-inv-lam-def {n} {M} {N} {.(app _ N)} (βappₗ stp) =
    inr (inl (_ ,, ((=rf , stp) ,, =rf)))
  βapp-inv-lam-def {n} {M} {N} {.(app (lam M) _)} (βappᵣ stp) =
    inr (inr (_ ,, ((=rf , stp) ,, =rf)))

  βapp-inv-lam : ∀ {n} {M N : Trm n} {M' : Trm (suc n)} (eq : lam M' == M)
                          → {P : Trm n} → (stp : app M N ⟶ P)
                            → βapp-case-β stp + βapp-case-l stp + βapp-case-r stp
  βapp-inv-lam {n} {M} {N} {M'} eq =
    =transp (λ x → ∀ {P} (stp : app x N ⟶ P)
                     → βapp-case-β stp + βapp-case-l stp + βapp-case-r stp)
            eq
            (βapp-inv-lam-def {n} {M'} {N})

  βapp-inv-app : ∀ {n} {M N : Trm n} {M₁ M₂ : Trm n} (eq : app M₁ M₂ == M)
                   → {P : Trm n} → (stp : app M N ⟶ P)
                     → βapp-case-β stp + βapp-case-l stp + βapp-case-r stp
  βapp-inv-app {n} {M} {N} {M₁} {M₂} eq {.(app _ N)} (βappₗ stp) =
    inr (inl (_ ,, ((=rf , stp) ,, =rf)))
  βapp-inv-app {n} {M} {N} {M₁} {M₂} eq {.(app M _)} (βappᵣ stp) =
    inr (inr (_ ,, ((=rf , stp) ,, =rf)))
  -- here `eq` is needed to exclude the case `β` when doing induction on `stp`

  βapp-inv-aux : ∀ {n} {M N P : Trm n} (stp : app M N ⟶ P)
                   → Trm-Cases M
                     → βapp-case-β stp + βapp-case-l stp + βapp-case-r stp
  βapp-inv-aux {n} {M} {N} {P} stp =
    [ (λ z → βapp-inv-var (pj2 z) stp)
    ∥ (λ z → βapp-inv-lam (pj2 z) stp)
    ∥ (λ z → βapp-inv-app (pj2 z) stp)
    ]

  βapp-inv : ∀ {n} {M N P : Trm n} (stp : app M N ⟶ P)
                   → βapp-case-β stp + βapp-case-l stp + βapp-case-r stp
  βapp-inv {n} {M} {N} {P} stp = βapp-inv-aux stp (Trm-cases M)

{-
In the definition of `βapp-inv` by direct induction
 `βapp-inv {n} {lam M} {N} {.(subst-all M (trmsect N))} (β M N) =
    inl (M ,, ((=rf , =rf) ,, =rf))
  βapp-inv {n} {M} {N} {.(app _ N)} (βappₗ stp) =
    inr (inl (_ ,, ((=rf , stp) ,, =rf)))
  βapp-inv (βappᵣ stp) =
    inr (inr (_ ,, ((=rf , stp) ,, =rf)))`
the last two clauses do NOT hold definitionally
-}

  βapp-stp-inv-aux : ∀ {n} {M N P : Trm n} (stp : app M N ⟶ P)
                       → βapp-case-β stp + βapp-case-l stp + βapp-case-r stp
                         → Σ[ Trm (suc n) ] (λ x → lam x == M)
                           + Σ[ Trm n ] (M ⟶_)
                           + Σ[ Trm n ] (N ⟶_)
  βapp-stp-inv-aux {n} {M} {N} stp =
    [ inl ∘ ⟨ pj1 ∣∣ (λ c → prj2 (pj1 (pj2 c))) ⟩
    ∥ inr ∘ inl ∘ ⟨ pj1 ∣∣ (λ c → prj2 (pj1 (pj2 c))) ⟩
    ∥ inr ∘ inr ∘ ⟨ pj1 ∣∣ (λ c → prj2 (pj1 (pj2 c))) ⟩
    ]

  βapp-stp-inv : ∀ {n} {M N : Trm n}
                   → Σ[ Trm n ] (app M N ⟶_)
                     → Σ[ Trm (suc n) ] (λ x → lam x == M)
                       + Σ[ Trm n ] (M ⟶_)
                       + Σ[ Trm n ] (N ⟶_)
  βapp-stp-inv {n} {M} {N} z = βapp-stp-inv-aux (pj2 z) (βapp-inv (pj2 z))

  βapp-idcod : ∀ {n} {M N : Trm n} → (z : Σ[ Trm n ] (app M N ⟶_))
                 → βapp-stp (βapp-stp-inv z) == z
  βapp-idcod z = {!+ind3 (λ _ → βapp-stp (βapp-stp-inv z) == z)!}

  -->> need to have an iso for each of the three Trm-Cases
  βapp-iso-var : ∀ {n i} {M N : Trm n} → var i == M
                   → is-iso-pair (βapp-stp {n} {M} {N}) βapp-stp-inv
  βapp-iso-var {n} {i} {M} {N} eq =
    =transp (λ x → is-iso-pair (βapp-stp {n} {x} {N}) βapp-stp-inv)
            eq
            (+ind3 (λ u → βapp-stp-inv (βapp-stp u) == u)
                   ( λ (z : Trm-is-lam (var i))
                       → N₀ind {λ _ → βapp-stp-inv (βapp-stp (inl z)) == inl z}
                                (lam≠var i (pj1 z) (pj2 z)) )
                   ( λ (z : Σ[ Trm n ] (var i ⟶_))
                       → N₀ind {λ _ → βapp-stp-inv (βapp-stp (inr (inl z))) == inr (inl z)}
                                (¬var⟶ i (pj1 z) (pj2 z)))
                   (λ z → =ap (inr ∘ inr) (Ση z))
            , λ z → =Σchar {!βapp-inv {M = var i} (pj2 z)!} {!!})

  βapp-iso : ∀ {n} {M N : Trm n} → is-iso-pair (βapp-stp {n} {M} {N}) βapp-stp-inv
  βapp-iso {n} {M} {N} = {!!}
    where --caseβ : (z : Σ[ Trm (suc n) ] (λ x → lam x == M))
            --         → βapp-stp-inv (βapp-stp (inl z)) == inl z
          --caseβ z = {!=ap {Trm n} (λ x → βapp-stp-inv {M = x} {N} (M ,, ?))!}
          -- =Σchar,, ? {b' = β (pj1 z) N} ?
          iddom-β : (z : Σ[ Trm (suc n) ] (λ x → lam x == M))
                       → βapp-stp-inv (βapp-stp (inl z)) == inl z
          iddom-β z =
            +ind3 (λ v → βapp-stp-inv-aux (pj2 βstp) (βapp-inv-aux (pj2 βstp) v) == inl z)
                  {!!}
                  (λ z' → {!=J (λ x u → βapp-inv-lam u)!})
                  {!!}
                  (Trm-cases M)
            where βstp : Σ[ Trm n ] (app M N ⟶_)
                  βstp = βapp-stp (inl z)
                  βeq-def : (stp : app (lam (pj1 z)) N ⟶ subst-0 (pj1 z) N)
                                → βapp-stp-inv-aux stp (βapp-inv-lam-def stp) == inl (pj1 z ,, =rf)
                  βeq-def stp = {!!}


          iddom : (u : Σ[ Trm (suc n) ] (λ x → lam x == M)
                          + Σ[ Trm n ] (M ⟶_) + Σ[ Trm n ] (N ⟶_))
                                   → βapp-stp-inv (βapp-stp u) == u
          iddom =
            +ind3 (λ u → βapp-stp-inv (βapp-stp u) == u)
                  (λ z → {!!})
                  (λ z → {!!})
                  (λ z → {!!})
              where aux : (z : Σ[ Trm n ] (N ⟶_))
                             → βapp-inv (βappᵣ (pj2 z))
                                        == inr (inr (_ ,, ((=rf , pj2 z) ,, =rf)))
                    aux z = {!!}
-}

{-
    ⟨ apptrm ∣∣ appstp ⟩
    where apptrm : Σ[ Trm n ] (λ x → app M₁ M₂ ⟶ x + N ⟶ x) → Trm n
          apptrm z = [ (λ s → app (pj1 z) N) ∣ (λ _ → app (app M₁ M₂) (pj1 z)) ] (pj2 z)
          appstp : (z : Σ[ Trm n ] (λ x → app M₁ M₂ ⟶ x + N ⟶ x))
                      → app (app M₁ M₂) N ⟶ apptrm z
          appstp (P ,, stp) = +ind (λ s → app (app M₁ M₂) N ⟶ apptrm (P ,, s))
                                   βappₗ βappᵣ stp

  βappapp-stp-restr : ∀ {n} {M₁ M₂ N : Trm n}
                        → (z : Σ[ Trm n ] (λ x → app M₁ M₂ ⟶ x + N ⟶ x))
                          → βappapp-stp z == βapp-stp {M = app M₁ M₂} (βappapp-stp-med z)
  βappapp-stp-restr {n} {M₁} {M₂} {N} z =
    =ap βappapp-stp (Ση⁻¹ z)
    • +ind (λ u → βappapp-stp (pj1 z ,, u) == βapp-stp (βappapp-stp-med (pj1 z ,, u)))
           (λ _ → =rf)
           (λ _ → =rf)
           (pj2 z)
-}

{-
  βapplam'-stp-med : ∀ {n} {M : Trm (suc n)} {N : Trm n}
                  → Σ[ Trm n ] (λ x → (x == subst-0 M N) + N ⟶ x)
                      + Σ[ Trm (suc n) ] (M ⟶_)
                      → Σ[ Trm (suc n) ] (λ x → lam x == lam M)
                           + Σ[ Trm n ] (lam M ⟶_) + Σ[ Trm n ] (N ⟶_)
  βapplam'-stp-med {n} {M} {N} =
    [ (λ z → [ (λ _ → inl (M ,, =rf))
              ∣ inr ∘ inr ∘ ⟨ (λ _ → pj1 z) ∣∣ id ⟩
              ] (pj2 z))
    ∣ inr ∘ inl ∘ ⟨ lam ∘ pj1 ∣∣ (λ z → βlam (pj2 z)) ⟩
    ]

  βapplam'-stp : ∀ {n} {M : Trm (suc n)} {N : Trm n}
                  → Σ[ Trm n ] (λ x → (x == subst-0 M N) + N ⟶ x)
                      + Σ[ Trm (suc n) ] (M ⟶_)
                      → Σ[ Trm n ] (app (lam M) N ⟶_)
  βapplam'-stp {n} {M} {N} = βapp-stp {M = lam M} ∘ βapplam'-stp-med {n} {M} {N}

{-
    [ ⟨ trmn ∣∣ stpn ⟩
    ∣ ⟨ (λ z → app (lam (pj1 z)) N) ∣∣ (λ z → βappₗ (βlam (pj2 z))) ⟩ ]
    where trmn : Σ[ Trm n ] (λ x → (x == subst-0 M N) + N ⟶ x) → Trm n
          trmn z = [ (λ _ → pj1 z) ∣ (λ _ → app (lam M) (pj1 z)) ] (pj2 z)
          stpn : (z : Σ[ Trm n ] (λ x → (x == subst-0 M N) + N ⟶ x))
                    → app (lam M) N ⟶ trmn z
          stpn z = +ind (λ u → app (lam M) N ⟶ [ (λ _ → pj1 z)
                                                 ∣ (λ _ → app (lam M) (pj1 z)) ] u)
                        (λ p → ((app (lam M) N ⟶_) ● p ⁻¹) (β M N))
                        βappᵣ
                        (pj2 z)
-}

  βapplam'-inv : ∀ {n M N P} (stp : app (lam {n} M) N ⟶ P)
                  → Σ[ P == subst-0 M N ] (λ u → β M N == ((app (lam M) N ⟶_) ● u) stp)
                   + Σ[ Trm (suc n) ] ( λ x → Σ[ M ⟶ x × (P == app (lam x) N) ]
                    ( λ y → ((app (lam M) N ⟶_) ● (prj2 y)) stp == βappₗ (βlam (prj1 y)) ))
                   + Σ[ Trm n ] ( λ x → Σ[ N ⟶ x × (P == app (lam M) x) ]
                      ( λ y → ((app (lam M) N ⟶_) ● (prj2 y)) stp == βappᵣ (prj1 y) ))
  βapplam'-inv (β M N)              = inl (=rf ,, =rf)
  βapplam'-inv (βappₗ (βlam stp))    = inr (inl (_ ,, ((stp , =rf) ,, =rf)))
  βapplam'-inv (βappᵣ stp)           = inr (inr (_ ,, ((stp , =rf) ,, =rf)))

  βapplam'-stp-inv : ∀ {n} {M : Trm (suc n)} {N : Trm n}
                      → Σ[ Trm n ] (app (lam M) N ⟶_)
                        → (Σ[ Trm n ] (λ x → (x == subst-0 M N) + N ⟶ x)
                            + Σ[ Trm (suc n) ] (M ⟶_))
  βapplam'-stp-inv {n} {M} {N} z =
    [ inl ∘ ⟨ (λ _ → pj1 z) ∣∣ inl ∘ pj1 ⟩
    ∥ inr ∘ ⟨ pj1 ∣∣ (λ w → prj1 (pj1 (pj2 w))) ⟩
    ∥ inl ∘ ⟨ pj1 ∣∣ (λ w → inr (prj1 (pj1 (pj2 w)))) ⟩
    ] (βapplam'-inv (pj2 z)) 

  βapplam'-iso : ∀ {n} {M : Trm (suc n)} {N : Trm n}
                  → is-iso-pair (βapplam'-stp {n} {M} {N}) (βapplam'-stp-inv)
  βapplam'-iso {n} {M} {N} = {!!} , eq2
    where {-eq1-aux : ∀ {P} (p : P == subst-0 M N)
                     → (P ,, ((app (lam M) N ⟶_) ● p ⁻¹) (β M N)) == (subst-0 M N ,, β M N)
          eq1-aux {P} p = =Σchar,, p (transp-back-forth-ptw _ p (β M N))
          βeq1-aux : ∀ {P} (p : P == subst-0 M N)
            → βapplam'-stp-inv (βapplam'-stp (inl (P ,, inl p)))
            -- = βapplam'-stp-inv (P ,, ((app (lam M) N ⟶_) ● p ⁻¹) (β M N))
                            == inl (subst-0 M N ,, inl =rf)
          βeq1-aux p = =ap βapplam'-stp-inv  (eq1-aux p)
          eq1 : ∀ z → βapplam'-stp-inv (βapplam'-stp {n} {M} {N} z) == z
          eq1 =
            +ind (λ z → βapplam'-stp-inv (βapplam'-stp z) == z)
                 (λ w → +ind (λ v → βapplam'-stp-inv (βapplam'-stp (inl (pj1 w ,, v))) == inl (pj1 w ,, v))
                              (λ p → =proof
               βapplam'-stp-inv (βapplam'-stp (inl (pj1 w ,, inl p)))   ==[ βeq1-aux p ] /
               inl (subst-0 M N ,, inl =rf)
                   ==[ =ap inl (=Σchar (p ⁻¹)
                                       (transp-inl-ptw _ _ (p ⁻¹) =rf
                                        • =ap inl (=transp-precmp-rf p))) ]∎
               inl (pj1 w ,, inl p) ∎)
                              (λ _ → =ap inl =rf)
                              (pj2 w)
                          • =ap inl (Ση w))
                 (λ w → =ap inr (Ση w))-}

          arg2 : (z : Σ[ Trm n ] (app (lam M) N ⟶_)) →
               Σ[ pj1 z == subst-0 M N ] (λ u → β M N == ((app (lam M) N ⟶_) ● u) (pj2 z))
              + Σ[ Trm (suc n) ] ( λ x → Σ[ M ⟶ x × (pj1 z == app (lam x) N) ]
               ( λ y → ((app (lam M) N ⟶_) ● (prj2 y)) (pj2 z) == βappₗ (βlam (prj1 y)) ))
              + Σ[ Trm n ] ( λ x → Σ[ N ⟶ x × (pj1 z == app (lam M) x) ]
                 ( λ y → ((app (lam M) N ⟶_) ● (prj2 y)) (pj2 z) == βappᵣ (prj1 y) ))
                   → Σ[ Trm n ] (app (lam M) N ⟶_)
          arg2 z = [ (λ _ → subst-0 M N ,, β M N)
                  ∥ (λ w → app (lam (pj1 w)) N ,, βappₗ (βlam (prj1 (pj1 (pj2 w)))))
                  ∥ (λ w → app (lam M) (pj1 w) ,, βappᵣ (prj1 (pj1 (pj2 w)))) ]
          arg2-eq : (z : Σ[ Trm n ] (app (lam M) N ⟶_))
                      → z == arg2 z (βapplam'-inv (pj2 z))
          arg2-eq (.(subst-0 M N) ,, β M N)              = =rf
          arg2-eq (.(app (lam _) N) ,, βappₗ (βlam stp))  = =rf
          arg2-eq (.(app (lam M) _) ,, βappᵣ stp)         = =rf
          eq2 : ∀ z → βapplam'-stp (βapplam'-stp-inv {n} {M} {N} z) == z
          eq2 z = =proof
            βapplam'-stp (βapplam'-stp-inv z)
              ==[ =ap (βapplam'-stp ∘ βapplam'-stp-inv) (arg2-eq z) ] /
            βapplam'-stp (βapplam'-stp-inv (arg2 z (βapplam'-inv (pj2 z))))
              ==[ +ind3 (λ u → βapplam'-stp (βapplam'-stp-inv {n} {M} {N} (arg2 z u)) == z)
                        (λ w → =Σchar (pj1 w ⁻¹)
                                       (=ap ((app (lam M) N ⟶_) ● pj1 w ⁻¹) (pj2 w)
                                        • transp-forth-back-ptw _ (pj1 w) (pj2 z)))
                        (λ w → =Σchar (prj2 (pj1 (pj2 w)) ⁻¹)
                          (=ap ((app (lam M) N ⟶_) ● prj2 (pj1 (pj2 w)) ⁻¹) (pj2 (pj2 w) ⁻¹)
                           • transp-forth-back-ptw _ (prj2 (pj1 (pj2 w))) (pj2 z)))
                        (λ w → =Σchar (prj2 (pj1 (pj2 w)) ⁻¹)
                          (=ap ((app (lam M) N ⟶_) ● prj2 (pj1 (pj2 w)) ⁻¹) (pj2 (pj2 w) ⁻¹)
                           • transp-forth-back-ptw _ (prj2 (pj1 (pj2 w))) (pj2 z)))
                        (βapplam'-inv (pj2 z)) ]∎
            z ∎

  βapplam'-eqv : ∀ {n} {M : Trm (suc n)} {N : Trm n} → is-equiv (βapplam'-stp {n} {M} {N})
  βapplam'-eqv {n} {M} {N} = invrt-is-eqv (βapplam'-stp-inv ,, βapplam'-iso)
-}

{----------------------
  ⟶-prop-aux : ∀ {n M N N'} → app {n} (lam M) N == subst-0 M N' → ¬ (N' ⟶ N)
  ⟶-prop-aux {n} {M} {N} p stp = {!!}

  applam-to-subst : ∀ {n M N P} → (p : P == subst-0 M N) → (stp : app (lam {n} M) N ⟶ P)
                      → β M N == ((app (lam M) N ⟶_) ● p) stp
  applam-to-subst {n} p stp = [ (λ z → pj2 z • ●irrelₚₜ (Trm-is-set n) (pj1 z) p stp)
                              ∥ {!!} ∥ {!!} ] (βapplam-inv stp)

  -- this may be false (i.e. M ⟶ N is set and not prop)
  ⟶-is-prop : ∀ {n} {M N : Trm n} → isProp (M ⟶ N)
  ⟶-is-prop {n} (β M N) stp2 = {!!}
    where aux : ∀ {P} (stp : app (lam M) N ⟶ P) → (p : P == subst-0 M N)
                      → β M N == ((app (lam M) N ⟶_) ● p) stp
          aux (β M N) p = ●loop=idₚₜ (Trm-is-set n) p (β M N) ⁻¹
          -- in the other two cases p should yield N₀
          aux (βappₗ stp) p = {!stp!}
          aux (βappᵣ stp) p = {!!}
  ⟶-is-prop (βlam stp1) (βlam stp2) = =ap βlam (⟶-is-prop stp1 stp2)
  ⟶-is-prop (βappₗ stp1) stp2 = {!!}
  ⟶-is-prop (βappᵣ stp1) stp2 = {!!}
---------------}

{-
  -- the one step reduction reduces the length (number of symbols)
  ⟶-low# : ∀ {n} {M N : Trm n} → M ⟶ N → # N <N # M
  -- not true for β: (λx.xxx)(yz) ⟶ (yz)(yz)(yz), but
  -- # (yz)(yz)(yz) = 6 ≮ 6 = 4+2 = # (λx.xxx)(yz)
  ⟶-low# (β M N) = {!!}
  ⟶-low# (βlam stp) = ⟶-low# stp
  ⟶-low# (βappₗ stp) = {!!}
  ⟶-low# (βappᵣ stp) = {!!}
-}


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

  ⟶-subst-all : {n m : Nat}(f : Fin n → Trm m){M M' : Trm n}
                    → M ⟶ M' → subst-all M f ⟶ subst-all M' f
  ⟶-subst-all f {app (lam M) N} (β M N) =
    =transp (λ x → app (lam (subst-all M (wlift f))) (subst-all N f) ⟶ x)
            (subst-0-dist M N f)
            (β (subst-all M (wlift f)) (subst-all N f))
  ⟶-subst-all f {lam M} (βlam redM) =
    βlam (⟶-subst-all (wlift f) redM)
  ⟶-subst-all f {app M N} (βappₗ redM) =
    βappₗ (⟶-subst-all f redM)
  ⟶-subst-all f {app M N} (βappᵣ redM) =
    βappᵣ (⟶-subst-all f redM)

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
{-
  ⟶⋆-rename {M = M} {.(subst-all M₁ (trmsect N))} f (tccnc redM (β M₁ N)) =
    ⟶⋆cnc (⟶⋆-rename f redM)
           (=transp (λ x → app (lam (rename M₁ (liftFin f))) (rename N f) ⟶ x)
                    (subst-0-rename M₁ N f) (β _ _))
  ⟶⋆-rename {M = M} {lam M'} f (tccnc redM (βlam stpM)) =
    ⟶⋆cnc (⟶⋆-rename f redM)
           (βlam (⟶-rename (liftFin f) stpM))
  ⟶⋆-rename {M = M} {app M' N'} f (tccnc redM (βappₗ stpM)) =
    ⟶⋆cnc (⟶⋆-rename f redM)
           (βappₗ (⟶-rename f stpM))
  ⟶⋆-rename {M = M} {app M' N'} f (tccnc redM (βappᵣ stpM)) =
    ⟶⋆cnc (⟶⋆-rename f redM)
           (βappᵣ (⟶-rename f stpM))
-}

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
  -- but this means that M' and N' cannot be named in the inductive definition of ≡>-rename
  -- as they appear in subst-0 M' N'.
  -- Therefore this term is needed to make M' and N' explicit and avoid yellow in ≡>-rename.
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
  ⟶<≡> {_} {app (lam M) N} (β M N) =
    ≡>red (≡>rfl {M = M}) (≡>rfl {M = N})
  ⟶<≡> {_} {lam M} {lam M'} (βlam stp) =
    ≡>lam (⟶<≡> stp)
  ⟶<≡> {_} {app M N} (βappₗ stp) =
    ≡>app (⟶<≡> stp) (≡>rfl {M = N})
  ⟶<≡> {_} {app M N} (βappᵣ stp) =
    ≡>app (≡>rfl {M = M}) (⟶<≡> stp)

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
  is-normal M = ∀ N → M ⟶ N → N₀

  -- a value is a canonical normal term
  data is-value {n : Nat} : Trm n → Set where
    val-lam : ∀ {M} → is-normal M → is-value (lam M)

  nrm-lam : ∀ {n M} → is-normal {n} (lam M) → is-normal M
  nrm-lam nrm = λ N stp → nrm (lam N) (βlam stp)
  nrm-lam-inv : ∀ {n M} → is-normal {suc n} M → is-normal (lam M)
  nrm-lam-inv nrm (lam N) (βlam stp) = nrm N stp
  
  nrm-appₗ : ∀ {n M N} → is-normal {n} (app M N) → is-normal M
  nrm-appₗ nrm = λ M stp → nrm (app M _) (βappₗ stp)
  nrm-appᵣ : ∀ {n M N} → is-normal {n} (app M N) → is-normal N
  nrm-appᵣ nrm = λ N stp → nrm (app _ N) (βappᵣ stp)

  -- a term is strongly normalising if all its sequences of reductions terminate
  data isStrNrmₗₑᵥ {n : Nat} : Nat → Trm n → Set where
    strnrm-nrm : ∀ {M} → is-normal M → isStrNrmₗₑᵥ zero M
    strnrm-stp : ∀ {k M} → (∀ {N} → M ⟶ N → isStrNrmₗₑᵥ k N) → isStrNrmₗₑᵥ (suc k) M

  isStrNrm : ∀ {n} → Trm n → Set
  isStrNrm M = Σ[ Nat ] (λ x → isStrNrmₗₑᵥ x M)

  strnrm-upw : ∀ {n k M} → isStrNrmₗₑᵥ {n} k M → ∀ {l} → k ≤N l → isStrNrmₗₑᵥ l M
  strnrm-upw (strnrm-nrm nrmM) {zero} dq = strnrm-nrm nrmM
  strnrm-upw (strnrm-nrm nrmM) {suc l} dq = strnrm-stp (λ {N} stp → N₀ind (nrmM N stp))
  strnrm-upw (strnrm-stp snstp) {suc l} dq = strnrm-stp (λ {N} stp → strnrm-upw (snstp stp) dq)

  strnrm-⟶ₗₑᵥ : ∀ {k n M N} → isStrNrmₗₑᵥ {n} k M → M ⟶ N → isStrNrm N
  strnrm-⟶ₗₑᵥ (strnrm-nrm nrmM) stp = N₀ind (nrmM _ stp)
  strnrm-⟶ₗₑᵥ {k = suc k} (strnrm-stp snstp) stp = k ,, snstp stp

  strnrm-⟶ : ∀ {n M N} → isStrNrm {n} M → M ⟶ N → isStrNrm N
  strnrm-⟶ {n} snM = strnrm-⟶ₗₑᵥ (pj2 snM)

  -- number of one step β-reductions from a term
  ⟶# : ∀ {n} → Trm n → Nat
  ⟶# (var i) = zero
  ⟶# (lam M) = ⟶# M
  ⟶# (app (var i) M₂) = ⟶# M₂
  ⟶# (app (lam M₁) M₂) = suc (⟶# M₁ +N ⟶# M₂)
  ⟶# (app (app M₁ N₁) M₂) = ⟶# (app M₁ N₁) +N ⟶# M₂
    
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

  -- enumeration of one-step reductions of a term
  ⟶enm : ∀ {n} M → Fin (⟶# M) → Σ[ Trm n ] (M ⟶_)
  ⟶enm {n} (lam M) i =
    lam (pj1 (ih i)) ,, βlam (pj2 (ih i))
    where ih : Fin (⟶# M) → Σ[ Trm (suc n) ] (M ⟶_)
          ih = ⟶enm M
  ⟶enm {n} (app M₁ M₂) = +rec3 (λ z → fv (pj2 z))
                                 (λ z → fl (pj2 z))
                                 (λ z → fa (pj2 z))
                                 M₁EM
    -- Agda complains if we try induction on M₁, so try propositionally instead.
    where M₁EM : Trm-Cases M₁
          M₁EM = Trm-cases M₁
          enmM₁ : Fin (⟶# M₁) → Σ[ Trm n ] (M₁ ⟶_)
          enmM₁ = ⟶enm M₁
          enmM₂ : Fin (⟶# M₂) → Σ[ Trm n ] (M₂ ⟶_)
          enmM₂ = ⟶enm M₂
          -- if var i == M₁, only the reductions of M₂ matter
          enmM₂v : ∀ {i} → var i == M₁ → Fin (⟶# (app M₁ M₂)) → Σ[ Trm n ] (M₂ ⟶_)
          enmM₂v eq j = enmM₂ (=transp (λ x → Fin (⟶# (app x M₂))) (eq ⁻¹) j)
          fv : ∀ {i} → var i == M₁ → Fin (⟶# (app M₁ M₂)) → Σ[ Trm n ] (app M₁ M₂ ⟶_)
          fv eq j = app M₁ (pj1 (enmM₂v eq j)) ,, βappᵣ (pj2 (enmM₂v eq j))
          -- if lam M == M₁, we have to count β in addition to the reductions of M and M₂
          -- reductions M ⟶_ are in bijections with reductions M₁ ⟶
          bjlF : ∀ {M} → lam M == M₁ → Fin (⟶# M) → Fin (⟶# M₁)
          bjlF = =transp (λ x → Fin (⟶# x))
          bjlT : ∀ {M} → lam M == M₁ → Σ[ Trm n ] (M₁ ⟶_) → Σ[ Trm (suc n) ] (M ⟶_)
          bjlT {M} eq (N ,, stp) = βlam-inv-trm (((_⟶ N) ● eq ⁻¹) stp)
                                   ,, βlam-inv-stp (((_⟶ N) ● eq ⁻¹) stp)
          -- so we can enumerate the reductions of M without using ⟶enm
          enmM₁l : ∀ {M} → lam M == M₁ → Fin (⟶# M) → Σ[ Trm (suc n) ] (M ⟶_)
          enmM₁l eq = bjlT eq ∘ enmM₁ ∘ bjlF eq
          -- the reductions are β, those of M and those of M₂
          enm-al : ∀ {M} → lam M == M₁ → Fin (suc (⟶# M +N ⟶# M₂)) → Σ[ Trm n ] ((app M₁ M₂ ⟶_))
          enm-al {M} eq fz =
            subst-0 M M₂ ,, =transp (λ x → app x M₂ ⟶ subst-0 M M₂) eq (β M M₂)
          enm-al {M} eq (fs j) =
            Fin+N-fnc (λ x → app (lam (pj1 (enmM₁l eq x))) M₂
                             ,, βappₗ (((_⟶ lam (pj1 (enmM₁l eq x)))● eq)
                                                           (βlam (pj2 (enmM₁l eq x)))))
                      (λ x → app M₁ (pj1 (enmM₂ x))
                             ,, βappᵣ (pj2 (enmM₂ x)))
                      j
          fl : ∀ {M} → lam M == M₁ → Fin (⟶# (app M₁ M₂)) → Σ[ Trm n ] (app M₁ M₂ ⟶_)
          fl eq j = enm-al eq (=transp (λ x → Fin (⟶# (app x M₂))) (eq ⁻¹) j)
          -- if app M N == M₁, only the reductions of M₁ and M₂ matter
          bjaF : ∀ {M N} → app M N == M₁ → Fin (⟶# (app M N)) → Fin (⟶# M₁)
          bjaF = =transp (λ x → Fin (⟶# x))
          bjaFa : ∀ {M N} → app M N == M₁ → Fin (⟶# (app (app M N) M₂)) → Fin (⟶# (app M₁ M₂))
          bjaFa = =transp (λ x → Fin (⟶# (app x M₂)))
          bjaFa⁻¹ : ∀ {M N} → app M N == M₁ → Fin (⟶# (app M₁ M₂)) → Fin (⟶# (app (app M N) M₂))
          bjaFa⁻¹ eq = =transp (λ x → Fin (⟶# (app x M₂))) (eq ⁻¹)
          fa : ∀ {M N} → app M N == M₁ → Fin (⟶# (app M₁ M₂)) → Σ[ Trm n ] (app M₁ M₂ ⟶_)
          fa {M} {N} eq = Fin+N-fnc (f₁ ∘ bjaF eq) f₂ ∘ bjaFa⁻¹ eq
            where f₁ : Fin (⟶# M₁) → Σ[ Trm n ] (app M₁ M₂ ⟶_)
                  f₁ j = app (pj1 (enmM₁ j)) M₂ ,, βappₗ (pj2 (enmM₁ j))
                  f₂ : Fin (⟶# M₂) → Σ[ Trm n ] (app M₁ M₂ ⟶_)
                  f₂ j = app M₁ (pj1 (enmM₂ j)) ,, βappᵣ (pj2 (enmM₂ j))


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
                 (λ z → ∘is-invrt {f = Fin-=to→ (⟶#app+lam N z)}
                                  {Fin+N-fnc (λ (_ : N₁) → inl z)
                                             (inr ∘ Fin+N-fnc (inl ∘ ihMf) (inr ∘ ihNf))}
                                  (Fin-=to→-inv (⟶#app+lam N z))
                                  (Fin+N-fnc-invrt (eqv-is-invrt
                                          (cntr-N₁-fnc-is-eqv (true-prop-is-contr
                                                   (idfull-fib-is-prop lam-inj-all M) z)
                                                              (λ _ → z)))
                                                   (Fin+N-fnc-invrt (eqv-is-invrt ihMeqv)
                                                                    (eqv-is-invrt ihNeqv))))
                 (λ z → ∘is-invrt {f = Fin-=to→ (⟶#app+not-lam N z ⁻¹)}
                                   {inr ∘ Fin+N-fnc (inl ∘ ihMf) (inr ∘ ihNf)}
                                   (Fin-=to→-inv (⟶#app+not-lam N z ⁻¹))
                                   (eqv-is-invrt (+N₀eqvr z (invrt-is-eqv
                                          (Fin+N-fnc-invrt (eqv-is-invrt ihMeqv)
                                                           (eqv-is-invrt ihNeqv))))))
                 Mlam-or-not
          aenm : Fin (⟶# (app M N)) → Σ[ Trm n ] (app M N ⟶_)
          aenm = βapp-stp {n} {M} {N} ∘ aux Mlam-or-not
          aeqv : is-equiv aenm
          aeqv = ∘eqv (invrt-is-eqv aux-inv) (βapp-eqv {n} {M} {N})
  -- end of enumeration


  ⟶enm-inv : ∀ {n} M → (NN : Σ[ Trm n ] (M ⟶_)) → fib (⟶enm M) NN
  ⟶enm-inv M NN = {!!}

  strnrm-bound : ∀ {n} {M : Trm n} → (nn : ∀ {N} → M ⟶ N → isStrNrm {n} N)
                 → Σ[ Nat ] (λ x → ∀ {N} → M ⟶ N → isStrNrmₗₑᵥ {n} x N)
                 --nn {N} stp ≤N nn (pj2 x)
  strnrm-bound {n} {M} nn = mx ,, {!!}
    where nnFN : Fin (⟶# M) → Nat
          nnFN i = pj1 (nn {pj1 (⟶enm M i)} (pj2 (⟶enm M i)))
          mxnn : (Fin (⟶# M) → N₀) + Σ[ Fin (⟶# M) ] (is-max≤N-Fin-ext nnFN)
          mxnn = max≤N-Fin-ext nnFN
          mx : Nat
          mx = [ (λ _ → zero)        -- zero if there are no reductions from M
               ∣ (λ z → nnFN (pj1 z)) -- the max of nnFN otherwise
               ] mxnn
          mxismx : ∀ {N} stp → (pj1 (nn {N} stp)) ≤N mx
          mxismx stp = [ (λ h → N₀ind (h {!!})) ∣ {!!} ] mxnn
              


  strnrm-any-stp : ∀ {n M} → (∀ {N} → M ⟶ N → isStrNrm {n} N)
                     → ∀ {N} → M ⟶ N → isStrNrm M
  strnrm-any-stp {n} snstp stp =
    suc (pj1 (snstp stp)) ,, strnrm-stp {!!}
    -- strnrm-stp (λ stp' → {!pj2 (snstp stp)!})
    where aux :  ∀ M → (∀ {N} → M ⟶ N → isStrNrm {n} N) → Nat
          aux = {!!}

{-
  -- need to take the max of a finite set
  strnrm-⟶-inv : ∀ {n M} → (∀ {N} → M ⟶ N → isStrNrm N) → isStrNrm {n} M
  strnrm-⟶-inv pf = {!!}

  ⟶-is-fin : ∀ {n} → (M : Trm n) → is-finite (Σ[ Trm n ] (M ⟶_))
  ⟶-is-fin {n} (var i) =
    zero ,, (N₀ind ,, λ stp → N₀ind {λ _ → isContr (fib N₀ind stp)} (var⟶⊥ (pj2 stp)))
    where var⟶⊥ : ∀ {i N} → var {n} i ⟶ N → N₀
          var⟶⊥ ()
  ⟶-is-fin {n} (lam M) =
    pj1 ih ,, ((λ i → lam (pj1 (enm i)) ,, βlam (pj2 (enm i)))
           ,, λ z → (pj1 (pj1 (cntr z)) ,, =Σchar,, {!prj2 (pj2 (lftN z))!} {!!} ⁻¹)
                     ,, {!!})
    where ih : is-finite (Σ[ Trm (suc n) ] (M ⟶_))
          ih = ⟶-is-fin M
          enm : Fin (pj1 ih) → Σ[ Trm (suc n) ] (M ⟶_)
          enm = pj1 (pj2 ih)
          enm-eqv : is-equiv enm
          enm-eqv = pj2 (pj2 ih)
          lftN : (z : Σ[ Trm n ] (lam M ⟶_)) → Σ[ Trm (suc n) ] (λ x → M ⟶ x × (pj1 z == lam x))
          lftN z = βlam-inv (pj2 z)
          cntr : (z : Σ[ Trm n ] (lam M ⟶_))
                    → isContr (fib enm (pj1 (lftN z) ,, prj1 (pj2 (lftN z))))
          cntr z = enm-eqv (pj1 (lftN z) ,, prj1 (pj2 (lftN z)))

  ⟶-is-fin (app M₁ M₂) = {!M₁!}

  ⟶-is-bound : ∀ {n} → (M : Trm n) → is-finite-bound (Σ[ Trm n ] (M ⟶_))
  ⟶-is-bound {n} (var i) = {!!}
  ⟶-is-bound {n} (lam M) =
    pj1 ih ,, ({!!} ,, {!!})
    where ih : is-finite-bound (Σ[ Trm (suc n) ] (M ⟶_))
          ih = ⟶-is-bound M
          r : Fin (pj1 ih) → Σ[ Trm (suc n) ] (M ⟶_)
          r = prj1 (pj1 (pj2 ih))
          s : Σ[ Trm (suc n) ] (M ⟶_) → Fin (pj1 ih)
          s = prj2 (pj1 (pj2 ih))
          rs=id : ∀ z → r (s z) == z
          rs=id = pj2 (pj2 ih)
  ⟶-is-bound {n} (app M₁ M₂) = {!!}


  strnrm-upw-fin : ∀ {n l} → (NN : Fin (suc l) → Σ[ Trm n ] isStrNrm)
                       → Σ[ Nat ] (λ x → ∀ i → isStrNrmₗₑᵥ x (pj1 (NN i)))
  strnrm-upw-fin {n} {zero} NN =
    pj1 (pj2 (NN 0₁)) ,, λ i → =transp (λ x → isStrNrmₗₑᵥ (pj1 (pj2 (NN 0₁))) (pj1 (NN x)))
                                       (pj2 N₁-isContr i ⁻¹)
                                       (pj2 (pj2 (NN 0₁)))
  strnrm-upw-fin {n} {suc l} NN =
    pj1 mx ,, snd
    where NNz : Σ[ Trm n ] isStrNrm
          NNz = NN fz
          NNs : Fin (suc l) → Σ[ Trm n ] isStrNrm
          NNs = NN ∘ fs
          ih : Σ[ Nat ] (λ x → ∀ i → isStrNrmₗₑᵥ x (pj1 (NNs i)))
          ih = strnrm-upw-fin NNs
          mx : Σ[ Nat ] (is-maxN-2 (pj1 (pj2 NNz)) (pj1 ih))
          mx = max≤N-2 (pj1 (pj2 NNz)) (pj1 ih)
          snd : (i : Fin (suc (suc l))) → isStrNrmₗₑᵥ (pj1 mx) (pj1 (NN i))
          snd fz = strnrm-upw (pj2 (pj2 NNz)) (prj1 (pj2 mx))
          snd (fs i) = strnrm-upw (pj2 ih i) (prj1 (prj2 (pj2 mx)))          
-}

-- end of file
