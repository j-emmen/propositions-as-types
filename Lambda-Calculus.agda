

module Lambda-Calculus where
  open import Basic-Inductives


  -- canonical lift of a function between finite sets
  liftFin :  ∀ {n m} → (Fin n → Fin m) → Fin (suc n) → Fin (suc m)
  liftFin f fz = fz
  liftFin f (fs i) = fs (f i)
  -- listFin f = [fx ; fs ∘ f] : 1 + Fin n → Fin (suc m)

  -- some properties of it
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


-- Lambda Terms in De Bruijn notation
-- a variable var i is bound by the i-th closest abstraction if any
-- lam (app (var 0) (var 1)) : Trm 2 (var 0 is bound while var 1 is free)

  data Trm : Nat → Set where
    var : ∀ {n} → Fin n → Trm n
    lam : ∀ {n} → Trm (suc n) → Trm n
    app : ∀ {n} → Trm n → Trm n → Trm n


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

  βlam-inv : ∀ {n} {M N : Trm (suc n)} → lam M ⟶ lam N → M ⟶ N
  βlam-inv (βlam stp) = stp
  βlam-uq :  ∀ {n} {M : Trm (suc n)} {N : Trm n} → lam M ⟶ N
               → Σ[ Trm (suc n) ] (λ x → M ⟶ x × (N == lam x))
  βlam-uq {n} {M} {lam N'} (βlam stp) = N' ,, (stp , =rf)
  βlam-uqg :  ∀ {n} {M : Trm (suc n)} {P N : Trm n} → lam M == P → P ⟶ N
               → Σ[ Trm (suc n) ] (λ x → M ⟶ x × (N == lam x))
  βlam-uqg {n} {M} {lam M} {N} =rf = βlam-uq {M = M} {N}


--  βappₗ-inv : ∀ {n} {M P N : Trm n} → (app M N) ⟶ (app P N) → M ⟶ P
--  βappₗ-inv stp = {!stp!}

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

  -- can use names given by Agda for variables in non-canonical arguments
  -- of inductive definitions (everything within a dot...).
  ⟶⋆-rename : {n m : Nat}{M M' : Trm n}(f : Fin n → Fin m)
                 → M ⟶⋆ M' → rename M f ⟶⋆ rename M' f
  ⟶⋆-rename {M = M} {M} f (tcrfl M) =
    ⟶⋆rfl (rename M f)
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
  -- in inductive definitions (which makes sense), but this means that M' and N' cannot be named
  -- in the inductive definition of ≡>-rename as they appear in subst-0 M' N'.
  -- This term is needed to make M' and N' explicit and avoid yellow in ≡>-rename.
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
    snk ,, (≡>-subst-0 (≡>⋄red₁ snkM) (≡>⋄red₁ snkN) , ≡>-subst-0 (≡>⋄red₂ snkM) (≡>⋄red₂ snkN))
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
          lftN z = βlam-uq (pj2 z)
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

  -- number of one step β-reductions from a term
  ⟶# : ∀ {n} → Trm n → Nat
  ⟶# (var i) = zero
  ⟶# (lam M) = ⟶# M
  ⟶# (app (var i) M₂) = ⟶# M₂
  ⟶# (app (lam M₁) M₂) = suc (⟶# M₁ +N ⟶# M₂)
  ⟶# (app (app M₁ N₁) M₂) = ⟶# (app M₁ N₁) +N ⟶# M₂

  ⟶#-lam= : ∀ {n} {P : Trm (suc n)} {M : Trm n} → lam P == M → ⟶# P == ⟶# M
  ⟶#-lam= {n} {P} {M} eq = =transp (λ x → ⟶# P == ⟶# x) eq =rf 

  Trm-EM : ∀ {n} → (M : Trm n) → Σ[ Fin n ] (λ x → var x == M)
                                    + Σ[ Trm (suc n) ] (λ x → lam x == M)
                                    + Σ[ Trm n × Trm n ] (λ x → app (prj1 x) (prj2 x) == M)
  Trm-EM (var i)             = inl (i ,, =rf)
  Trm-EM (lam M)             = inr (inl (M ,, =rf))
  Trm-EM (app M₁ M₂)         = inr (inr ((M₁ , M₂) ,, =rf))


  -- enumeration of one-step reductions of a term
  ⟶enm : ∀ {n M} → Fin (⟶# M) → Σ[ Trm n ] (M ⟶_)

  ⟶enm {n} {lam M} i =
    lam (pj1 (ih i)) ,, βlam (pj2 (ih i))
    where ih : Fin (⟶# M) → Σ[ Trm (suc n) ] (M ⟶_)
          ih = ⟶enm {M = M}
  ⟶enm {n} {app M₁ M₂} = +rec3 (λ z → fv (pj2 z))
                                 (λ z → fl (pj2 z))
                                 (λ z → fa (pj2 z))
                                 M₁EM
    -- Agda complains if we try induction on M₁, so need to take a different route.
    where M₁EM : Σ[ Fin n ] (λ x → var x == M₁) + Σ[ Trm (suc n) ] (λ x → lam x == M₁)
                    + Σ[ Trm n × Trm n ] (λ x → app (prj1 x) (prj2 x) == M₁)
          M₁EM = Trm-EM M₁
          enmM₁ : Fin (⟶# M₁) → Σ[ Trm n ] (M₁ ⟶_)
          enmM₁ = ⟶enm {M = M₁}
          enmM₂ : Fin (⟶# M₂) → Σ[ Trm n ] (M₂ ⟶_)
          enmM₂ = ⟶enm {M = M₂}
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
          bjlT {M} eq NN = pj1 aux ,, prj1 (pj2 aux)
            where aux : Σ[ Trm (suc n) ] (λ x → M ⟶ x × (pj1 NN == lam x))
                  aux = βlam-uqg eq (pj2 NN)
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

{-
  -- Agda complains that the definition does not terminate if I try induction on M₁

  ⟶enm {n} {app (var j) M₂} i =
    app (var j) (pj1 (ih i)) ,, βappᵣ (pj2 (ih i))
    where ih : Fin (⟶# M₂) → Σ[ Trm n ] (M₂ ⟶_)
          ih = ⟶enm {M = M₂}

  ⟶enm {n} {app (lam M₁) M₂} fz =
    subst-0 M₁ M₂ ,, β M₁ M₂

  ⟶enm {n} {app (lam M₁) M₂} (fs i) =
    Fin+N-fnc f₁ f₂ i
    ,, Fin+N-ind (λ x → app (lam M₁) M₂ ⟶ Fin+N-fnc f₁ f₂ x)
                 (λ j → =transp (app (lam M₁) M₂ ⟶_)
                                 (Fin+N-trl f₁ f₂ j ⁻¹)
                                 (βappₗ (βlam (pj2 (ih₁ j)))) )
                 (λ j → =transp (app (lam M₁) M₂ ⟶_)
                                 (Fin+N-trr f₁ f₂ j ⁻¹)
                                 (βappᵣ (pj2 (ih₂ j))) )
                 i
    where ih₁ : Fin (⟶# M₁) → Σ[ Trm (suc n) ] (M₁ ⟶_)
          ih₁ = ⟶enm {M = M₁}
          ih₂ : Fin (⟶# M₂) → Σ[ Trm n ] (M₂ ⟶_)
          ih₂ = ⟶enm {M = M₂}
          f₁ : Fin (⟶# M₁) → Trm n
          f₁ j = app (lam (pj1 (ih₁ j))) M₂
          f₂ : Fin (⟶# M₂) → Trm n
          f₂ j = app (lam M₁) (pj1 (ih₂ j))

  ⟶enm {n} {app (app M₁ N₁) M₂} i =
    Fin+N-fnc f₁ f₂ i
    ,, Fin+N-ind (λ x → app (app M₁ N₁) M₂ ⟶ Fin+N-fnc f₁ f₂ x)
                 (λ j → =transp (app (app M₁ N₁) M₂ ⟶_)
                                 (Fin+N-trl f₁ f₂ j ⁻¹)
                                 (βappₗ {!!}) ) -- (βappₗ (pj2 (ih₁ j)))
                 (λ j → =transp (app (app M₁ N₁) M₂ ⟶_)
                                 (Fin+N-trr f₁ f₂ j ⁻¹)
                                 (βappᵣ {M = app M₁ N₁} (pj2 (ih₂ j))) )
                 i
    where --ih₁ : Fin (⟶# (app M₁ N₁)) → Σ[ Trm n ] (app M₁ N₁ ⟶_)
          --ih₁ = ⟶enm {M = app M₁ N₁}
          ih₁₁ : Fin (⟶# M₁) → Σ[ Trm n ] (M₁ ⟶_)
          ih₁₁ = ⟶enm {M = M₁}
          ih₁₂ : Fin (⟶# N₁) → Σ[ Trm n ] (N₁ ⟶_)
          ih₁₂ = ⟶enm {M = N₁}
          ih₂ : Fin (⟶# M₂) → Σ[ Trm n ] (M₂ ⟶_)
          ih₂ = ⟶enm {M = M₂}
          f₁ : Fin (⟶# (app M₁ N₁)) → Trm n
          f₁ j = {!!}
          --app (app (pj1 (ih₁₁ j)) (pj1 (ih₁₂ j))) M₂
          f₂ : Fin (⟶# M₂) → Trm n
          f₂ j = app (app M₁ N₁) (pj1 (ih₂ j))
-}

  ⟶-fambound :  ∀ {n} {M : Trm n} → (nn : ∀ {N} → M ⟶ N → Nat)
                      → Σ[ Nat ] (λ x → ∀ {N} stp → nn {N} stp ≤N x)
  ⟶-fambound {n} {var i} nn = {!!}
  ⟶-fambound {n} {lam M} nn = {!!}
  ⟶-fambound {n} {app (var i) M₂} nn = {!!}
  ⟶-fambound {n} {app (lam M₁) M₂} nn = {!⟶-fambound!}
  ⟶-fambound {n} {app (app M₁ N₁) M₂} nn = {!!}

  strnrm-bound : ∀ {n} {M : Trm n} → (nn : ∀ {N} → M ⟶ N → isStrNrm {n} N)
                 → Σ[ Nat ] (λ x → ∀ {N} → M ⟶ N → isStrNrmₗₑᵥ {n} x N)
                 --nn {N} stp ≤N nn (pj2 x)
  strnrm-bound nn = {!sum-succNat!}
    


  strnrm-any-stp : ∀ {n M} → (∀ {N} → M ⟶ N → isStrNrm {n} N)
                     → ∀ {N} → M ⟶ N → isStrNrm M
  strnrm-any-stp {n} snstp stp =
    suc (pj1 (snstp stp)) ,, strnrm-stp {!!}
    -- strnrm-stp (λ stp' → {!pj2 (snstp stp)!})
    where aux :  ∀ M → (∀ {N} → M ⟶ N → isStrNrm {n} N) → Nat
          aux = {!!}


-- end file
