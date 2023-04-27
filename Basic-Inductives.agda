
module Basic-Inductives where


  -- Identity and composite functions

  id : {A : Set} → A → A
  id = λ x → x

  infixr 2 _∘_
  _∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
  g ∘ f = λ x → g (f x)


  -- Identity type

  infix 1 _==_
  data _==_ {A : Set} (a : A) : A → Set where
    =rf : a == a


  -- Binary products and Σ-types

  infixr 3 _,_ _×_
  data _×_ (A : Set) (B : Set) : Set where
    _,_ : A → B → A × B
  prj1 : {A : Set} → {B : Set}  → A × B → A
  prj1 (a , b) = a
  prj2 : {A : Set} → {B : Set}  → A × B → B
  prj2 (a , b) = b

  infix 3 _,,_ Σ[_]_
  data Σ[_]_ (A : Set) (B : A → Set) : Set where
    _,,_ : (a : A) → B a → Σ[ A ] B
  pj1 : {A : Set} → {B : A → Set} → Σ[ A ] B → A
  pj1 (a ,, b) = a
  pj2 : {A : Set} → {B : A → Set}  → (u : Σ[ A ] B) → (B (pj1 u))
  pj2 (a ,, b) = b

  -- sums
  infix 3 _+_ [_,_]
  data _+_ (A : Set) (B : Set) : Set where
    inl : A → A + B
    inr : B → A + B

  [_,_] : ∀ {A B C : Set} → (A → C) → (B → C) → A + B → C
  [ f , g ] (inl a) = f a
  [ f , g ] (inr b) = g b

  +ind : ∀ {A B : Set} → (C : A + B → Set ) → (∀ a → C (inl a)) → (∀ b → C (inr b))
           → ∀ x → C x
  +ind C ls rs (inl a) = ls a
  +ind C ls rs (inr b) = rs b
    

  -- Natural numbers and its initial segments

  data Nat : Set where
    zero : Nat
    suc : Nat → Nat

  data Fin : Nat → Set where
    fz : ∀ {n} → Fin (suc n)
    fs : ∀ {n} → Fin n → Fin (suc n)

  N₀ N₁ : Set
  N₀ = Fin zero
  N₁ = Fin (suc zero)
  0₁ : N₁
  0₁ = fz
  N₀ind : {C : N₀ → Set} → (x : N₀) → C x
  N₀ind {C} ()
  N₁ind : {C : N₁ → Set}(c : C 0₁) → (x : N₁) → C x
  N₁ind {C} c fz = c


  --------------------------------
  -- Some stuff on identity types
  --------------------------------

  -- Paulin-Mohring eliminator

  =J : {A : Set}{a₀ : A}(B : (a : A) → a₀ == a → Set)
          → B a₀ =rf → {a : A} → (p : a₀ == a) → B a p
  =J B b₀ =rf = b₀


  -- Some useful properties

  =ap : {A B : Set}(f : A → B){a a' : A} → a == a' → f a == f a'
  =ap f = =J (λ x _ → f _ == f x) =rf

  =ap₂ : {A₁ A₂ B : Set}(f : A₁ → A₂ → B){a₁ a₁' : A₁}{a₂ a₂' : A₂}
             → a₁ == a₁' → a₂ == a₂' → f a₁ a₂ == f a₁' a₂'
  =ap₂ f {a₁} {a₁'} {a₂} {a₂'} = =J (λ x _ → (a₂ == a₂' → f a₁ a₂ == f x a₂'))
                                    (=ap (f a₁))

  =transp : {A : Set}(B : A → Set){a a' : A} → a == a' → B a → B a'
  =transp B {a} = =J (λ x _ → B a → B x) id

  infix 40 _●_
  _●_ : {A : Set}(B : A → Set) {a a' : A} → a == a' → B a → B a'
  B ● p = =transp B p

  =transpcnst : {A : Set}(B : Set){a a' : A}(p : a == a')(b : B) → ((λ _ → B) ● p) b == b
  =transpcnst B p b = =J (λ x q → ( ((λ _ → B) ● q) b == b )) =rf p

  =apd : {A : Set}{B : A → Set}(f : (a : A) → B a){a a' : A}(p : a == a') → (B ● p) (f a) == f a'
  =apd f p = =J (λ x p → (_ ● p) (f _) == f x) =rf p

  =sym : {A : Set}{a a' : A} → a == a' → a' == a
  =sym p = ((λ x → x == _) ● p) =rf

  =tra : {A : Set}{a₁ a₂ a₃ : A} → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
  =tra p q = ((λ x → _ == x) ● q) p


  -- Equational reasoning

  --infix 3 /_==[_]∎_∎
  --infix  3 _∎
  infixr 2 /_==[_]_
  infixr 1 =proof_==[_]_

  =proof_==[_]_ : {A : Set}(a₁ {a₂ a₃} : A) → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
  =proof a ==[ pf ] pf' = =tra pf pf'

  --_∎ : {A : Set}(a : A) → a == a
  --a ∎ = =rf

  /_==[_]_ : {A : Set}(a₁ {a₂ a₃} : A) → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
  / a₁ ==[ pf ] pf' = =tra pf pf'

  =eqreasend =eqreasend' : {A : Set}(a₁ a₂ : A) → a₁ == a₂ → a₁ == a₂
  =eqreasend _ _ pf = pf
  =eqreasend' _ _ pf = pf

  syntax =eqreasend a b pf = / a ==[ pf ]∎ b ∎
  syntax =eqreasend' a b pf = a ==[ pf ] b

  -- Notation for inverses and concatenation

  infix 60 _⁻¹

  _⁻¹ : {A : Set}{a a' : A} → a == a' → a' == a
  p ⁻¹ = =sym p

  infixr 50 _•_

  _•_ : {A : Set}{a₁ a₂ a₃ : A} → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
  p • q = =tra p q


  -- Groupoid laws

  •tr : {A : Set}(B : A → Set){a₁ a₂ a₃ : A}(p₁ : a₁ == a₂)(p₂ : a₂ == a₃)(b : B a₁)
           → (B ● (p₁ • p₂)) b == (B ● p₂) ((B ● p₁) b)
  •tr B p₁ p₂ b = =J (λ x u → (B ● p₁ • u) b == (B ● u) ((B ● p₁) b)) =rf p₂

  •idr : {A : Set}{a a' : A}(p : a == a') → p • =rf == p
  •idr p = =rf

  •idl : {A : Set}{a a' : A}(p : a == a') → =rf • p == p
  •idl p = =J (λ _ u → =rf • u == u) =rf p

  •invr : {A : Set}{a a' : A}(p : a == a') → p • p ⁻¹ == =rf
  •invr = =J (λ _ u → u • u ⁻¹ == =rf) =rf

  •invl : {A : Set}{a a' : A}(p : a == a') → p ⁻¹ • p == =rf
  •invl = =J (λ _ u → u ⁻¹ • u == =rf) =rf

  •ass : {A : Set}{a₁ a₂ a₃ a₄ : A}(p₁ : a₁ == a₂)(p₂ : a₂ == a₃)(p₃ : a₃ == a₄)
             → p₁ • (p₂ • p₃) == (p₁ • p₂) • p₃
  •ass p₁ p₂ p₃ = •tr _ p₂ p₃ p₁

  •ass⁻¹ : {A : Set}{a₁ a₂ a₃ a₄ : A}(p₁ : a₁ == a₂)(p₂ : a₂ == a₃)(p₃ : a₃ == a₄)
  --(p₁ : a₁ == a₂)(p₂ : a₂ == a₃)(p₃ : a₃ == a₄)
             → (p₁ • p₂) • p₃ == p₁ • (p₂ • p₃)
  •ass⁻¹ p₁ p₂ p₃ = •ass p₁ p₂ p₃ ⁻¹


  -- Some equations between proof of equations

  •extl : {A : Set}{a₁ a₂ : A}(p : a₁ == a₂){a₃ : A}{p₁ : a₂ == a₃}{p₂ : a₂ == a₃}
             → p₁ == p₂ → p • p₁ == p • p₂
  •extl p = =ap (λ u → p • u)

  •extr : {A : Set}{a₂ a₃ : A}(p : a₂ == a₃){a₁ : A}{p₁ : a₁ == a₂}{p₂ : a₁ == a₂}
             → p₁ == p₂ → p₁ • p == p₂ • p
  •extr p = =ap (λ u → u • p)


  •idlg : {A : Set}{a₁ a₂ a₃ : A}{p₁ : a₁ == a₁}{p₂ : a₁ == a₂}{p₃ : a₁ == a₂}
           → p₁ == =rf → p₁ • p₂ == p₃ → p₂ == p₃
  •idlg {p₁ = p₁} {p₂} {p₃} hrf h = =proof p₂         ==[ •idl p₂ ⁻¹ ] /
                                         =rf • p₂   ==[ •extr p₂ (hrf ⁻¹) ] /
                                         p₁ • p₂    ==[ h ]∎
                                         p₃ ∎

  •idrg : {A : Set}{a₁ a₂ a₃ : A}{p₁ : a₁ == a₂}{p₂ : a₂ == a₂}{p₃ : a₁ == a₂}
           → p₂ == =rf → p₁ • p₂ == p₃ → p₁ == p₃
  •idrg {p₁ = p₁} {p₂} {p₃} hrf h = =proof p₁         ==[ •idr p₁ ⁻¹ ] /
                                           p₁ • =rf   ==[ •extl p₁ (hrf ⁻¹) ] /
                                           p₁ • p₂    ==[ h ]∎
                                           p₃ ∎


  •lc : {A : Set}{a₁ a₂ : A}{p : a₁ == a₂}{a₃ : A}{p₁ : a₂ == a₃}{p₂ : a₂ == a₃}
            → p • p₁ == p • p₂ → p₁ == p₂
  •lc {p = p} {_} {p₁} {p₂} h = =proof p₁           ==[ (•idl p₁ ⁻¹ • •extr p₁ (•invl p ⁻¹)) • •ass⁻¹ _ _ p₁ ] /
                                   p ⁻¹ • p • p₁    ==[ •extl (p ⁻¹) h ] /
                                   p ⁻¹ • p • p₂    ==[ •ass _ _ p₂ • •extr p₂ (•invl p) • •idl p₂ ]∎
                                   p₂ ∎

  •rc : {A : Set}{a₁ a₂ a₃ : A}{p : a₂ == a₃}{a₁ : A}{p₁ : a₁ == a₂}{p₂ : a₁ == a₂}
            → p₁ • p == p₂ • p → p₁ == p₂
  •rc {p = p} {_} {p₁} {p₂} h = =proof p₁           ==[ •idr p₁ ⁻¹ • •extl p₁ (•invr p ⁻¹) ] /
                                   p₁ • p • p ⁻¹    ==[ •ass _ _ (p ⁻¹)  • •extr (p ⁻¹) h • •ass⁻¹ _ _ (p ⁻¹)  ] /
                                   p₂ • p • p ⁻¹    ==[ •extl p₂ (•invr p) • •idr p₂ ]∎
                                   p₂ ∎


  -- Equal functions are homotopic

  =2htpy : {A : Set}{B : A → Set}{f g : (a : A) → B a} → f == g → (a : A) → f a == g a
  =2htpy {f = f} p a = ((λ x → f a == x a) ● p) =rf


  --part of Lemma 2.9.6 in HoTT book

  HoTTLemma2-9-6 : {A : Set}{B C : A → Set}{a a' : A}(p : a == a')
                   {f : B a → C a}{g : B a' → C a'}
                     → ((λ x → B x → C x) ● p) f == g → (y : B a) → (C ● p) (f y) == g ((B ● p) y)
  HoTTLemma2-9-6 {A} {B} {C} {a} {a'} p = =J JEl JElrf p
    where JEl : (x : A) → a == x → Set
          JEl x u = {f : B a → C a}{g : B x → C x} →
                       ((λ x → B x → C x) ● u) f == g → (y : B a) → (C ● u) (f y) == g ((B ● u) y)
          JElrf : JEl a =rf
          JElrf = =2htpy


  {-
  -- transport of fibrewise functions is pointwise
  ●ptw : {A : Set}{B C : A → Set}(f : (a : A) → B a → C a)
         {a a' : A}(p : a == a')(b : B a')
            → ((λ x → B x → C x) ● p) (f a) b == (C ● p) (f a ((B ● p ⁻¹) b))
  ●ptw f p b = let ψ : _
                   ψ = {!!}
               in {!!}
  -}


  -- Contractibility & Co.
  isContr : (A : Set) → Set
  isContr A = Σ[ A ] (λ a₀ → (a : A) → a == a₀ )

  contr₀ : {A : Set} → isContr A → A
  contr₀ = pj1

  contr= : {A : Set}(cnt : isContr A)(a : A) → a == contr₀ cnt
  contr= = pj2

  N₁-isContr : isContr N₁
  N₁-isContr = 0₁ ,, N₁ind =rf

  isProp : (A : Set) → Set
  isProp A = (a a' : A) → a == a'

{-
  -- need function extensionality
  ∀isprop : ∀ {A} (B : A → Set) → (∀ a → isProp (B a)) → isProp (∀ a → B a)
  ∀isprop B isp b b' = {!!}
    where ptw : ∀ a → b a == b' a
          ptw a = isp a (b a) (b' a)
-}

  isContr→isProp : {A : Set} → isContr A → isProp A
  isContr→isProp cnt = λ a a' → (contr= cnt a) • (contr= cnt a' ⁻¹)

  isContr→=isContr : {A : Set} → isContr A → {a a' : A} → isContr (a == a')
  isContr→=isContr cnt = isContr→isProp cnt _ _ ,, =J (λ x u → u == isContr→isProp cnt _ _) (•invr (contr= cnt _) ⁻¹)


  -- the fibre of a function
  fib : ∀ {A B} → (f : A → B) → B → Set
  fib {A} f b = Σ[ A ] (λ x → f x == b)

  -- equivalences
  is-equiv : ∀ {A B} → (f : A → B) → Set
  is-equiv f = ∀ b → isContr (fib f b)

{-
  -- need function extensionality
  is-equiv-is-Prop : ∀ {A B f} → isProp (is-equiv {A} {B} f)
  is-equiv-is-Prop {A} {B} {f} = {! ∀isprop!}
-}  

  -- Identities of products
  prdη : {A B : Set}(z : A × B) → (prj1 z) , (prj2 z) == z
  prdη (a , b) = =rf

  prdη⁻¹ : {A B : Set}(z : A × B) → z == (prj1 z) , (prj2 z)
  prdη⁻¹ (a , b) = =rf

  =prdchar : {A B : Set}{z z' : A × B}
               → prj1 z == prj1 z' → prj2 z == prj2 z'
                 → z == z'
  =prdchar pf₁ pf₂ = auxAB pf₁ _ pf₂ • prdη _ where

                     auxB : {A B : Set}{z : A × B}(b : B)
                               → prj2 z == b → z == (prj1 z) , b
                     auxB {z = z} b pf = =J (λ b' pf' → z == (prj1 z) , b') (prdη⁻¹ _) pf

                     auxAB : {A B : Set}{z : A × B}{a : A} → prj1 z == a
                                 → (b : B) → prj2 z == b → z == (a , b)
                     auxAB {z = z} pf₁ = =J (λ a' pf' → (b' : _) → prj2 z == b' → z == (a' , b'))
                                            (auxB) pf₁

  -- UIP stuff
  UIP UIPrf  : (A : Set) → Set
  UIP A = {a a' : A} → isProp (a == a')
  UIPrf A = {a : A} (p : a == a) → p == =rf

  UIP→UIPrf : {A : Set} → UIP A → UIPrf A
  UIP→UIPrf {A} uip p = uip p =rf

  UIPrf→UIP : {A : Set} → UIPrf A → UIP A
  UIPrf→UIP {A} uiprf {a} = λ p q → =J (λ x u → (v : a == x) → v == u) uiprf q p


  HoTT-Thm7-2-2-aux : {A : Set} {R : A → A → Set} (Rrf : ∀ a → R a a)
                  (Risprop : ∀ a a' → isProp (R a a')) (R→== : ∀ a a' → R a a' → a == a')
                   → UIPrf A
  HoTT-Thm7-2-2-aux {A} {R} Rrf Risprop R→== {a} p = •lc {p = R→== a a (Rrf a)} (q' (Rrf a) • •idr _ ⁻¹)
    where D : A → Set
          D x = R a x → a == x
          q : (D ● p) (R→== a a) == R→== a a
          q = =apd {B = D} (R→== a) p
          q' : (e : R a a) → ((_==_ a) ● p) (R→== a a e) == R→== a a e --(((R a) ● p) e)
          q' e = HoTTLemma2-9-6 p q e • =ap (R→== a a) (Risprop a a _ _)


  HoTT-Thm7-2-2 : {A : Set} {R : A → A → Set} (Rrf : ∀ a → R a a)
                  (Risprop : ∀ a a' → isProp (R a a')) (R→== : ∀ a a' → R a a' → a == a')
                   → UIP A
  HoTT-Thm7-2-2 Rrf Risprop R→== = UIPrf→UIP (HoTT-Thm7-2-2-aux Rrf Risprop R→==)



  -------------------
  -- Some arithmetic
  -------------------

  one two three four five : Nat
  one = suc zero
  two = suc one
  three = suc two
  four = suc three
  five = suc four
  
  PA4 : ∀ {n} → suc n == zero → N₀
  PA4 p = =transp fam4 p 0₁ 
        where fam4 : Nat → Set
              fam4 zero = N₀
              fam4 (suc n) = N₁

  prdc : Nat → Nat
  prdc zero = zero
  prdc (suc n) = n

  suc-inj : ∀ {n m} → suc n == suc m → n == m
  suc-inj {n} {m} p = =ap prdc p

  infix 5 _≤N_
  _≤N_ : Nat → Nat → Set
  zero ≤N m = N₁
  suc n ≤N zero = N₀
  suc n ≤N suc m = n ≤N m

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
  
  ≤N-trn : ∀ {n m l} → n ≤N m → m ≤N l → n ≤N l
  ≤N-trn {zero} dq₁ dq₂ = 0₁
  ≤N-trn {suc n} {suc m} {suc l} dq₁ dq₂ = ≤N-trn {n} {m} {l} dq₁ dq₂

  suc-≤-0 : ∀ n → n ≤N suc n
  suc-≤-0 zero = 0₁
  suc-≤-0 (suc n) = suc-≤-0 n

  suc-≤ : ∀ {n m} → n ≤N m → n ≤N suc m
  suc-≤ {n} {m} dq = ≤N-trn {n} dq (suc-≤-0 m)

  ≤anti-sym : ∀ {n m} → n ≤N m → m ≤N n → n == m
  ≤anti-sym {zero} {zero} fz m≤n = =rf
  ≤anti-sym {suc n} {suc m} n≤m m≤n = =ap suc (≤anti-sym n≤m m≤n)

  ≤N-EM : ∀ n m → n ≤N m + m ≤N n
  ≤N-EM zero m = inl 0₁
  ≤N-EM (suc n) zero = inr 0₁
  ≤N-EM (suc n) (suc m) = ≤N-EM n m


  -- finite sets
  
  pdcFin : ∀ {n} → Fin (suc (suc n)) → Fin (suc n)
  pdcFin fz = fz
  pdcFin (fs i) = i

  fs-inj : ∀ {n}{i j : Fin n} → fs i == fs j → i == j
  fs-inj {_} {fz} {fz} eq = =rf
  fs-inj {_} {fs i} {fs j} eq = =ap pdcFin eq

  PA4-Fin : ∀ {n}{i : Fin n} → fz == fs i → N₀
  PA4-Fin {n} {i} eq = =transp fam4 eq 0₁
                     where fam4 : Fin (suc n) → Set
                           fam4 fz = N₁
                           fam4 (fs i) = N₀

  is-finite : Set → Set
  is-finite A = Σ[ Nat ] (λ n → Σ[ (Fin n → A) ] is-equiv)

  is-maxN-2 : ∀ n m → Nat → Set
  is-maxN-2 n m = λ x → n ≤N x × m ≤N x × (∀ {l} → n ≤N l → m ≤N l → x ≤N l)

--  suc-maxN-2 : ∀ {n m} → is-maxN-2 (suc n) (suc m) (suc )
  
  is-maxN-Fin : ∀ {n} → (f : Fin (suc n) → Nat) → (iₘₓ : Fin (suc n)) → Set
  is-maxN-Fin f iₘₓ = (∀ i → f i ≤N f iₘₓ)

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


  max≤N-Fin : ∀ {n} → (f : Fin (suc n) → Nat) → Σ[ Fin (suc n) ] (is-maxN-Fin f)
  max≤N-Fin {zero} f = fz ,, λ i → =2≤N (=ap f (pj2 (N₁-isContr) i))
  max≤N-Fin {suc n} f = {!max≤N-2 (f (fs (pj1 (max≤N-Fin (f ∘ fs))))) (f fz)!} ,, {!!}
    where mxN : Σ[ Nat ] (is-maxN-2 (f (fs (pj1 (max≤N-Fin (f ∘ fs))))) (f fz))
          mxN = max≤N-2 (f (fs (pj1 (max≤N-Fin (f ∘ fs))))) (f fz)
          iₘₓ : Σ[ Fin (suc (suc n)) ] (λ x → f x == pj1 mxN)
          iₘₓ = {!!}
          -- need to do it by induction on n, so not here
          

{-
  sup-Fin : ∀ {n} → (f : Fin (suc n) → Nat) → Σ (Fin (suc n)) (is-maxN-of f)
  sup-Fin {zero} f = fz ,, {!!} --N₁ind (≤N-rfl {f fz})
  sup-Fin {suc n} f = {!pj1 sup-ffs!} ,, {!!}
    where sup-ffs : Σ (Fin (suc n)) (λ x → (i : Fin (suc n)) → f (fs i) ≤N f (fs x))
          sup-ffs = {!!} --sup-Fin (f ∘ fs)
-}          



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

  -------------------------------------------------------------
  -- The reflexive and transitive closure of a binary relation
  ------------------------------------------------------------

  -- transitive closure
  data trans-clos {A : Set}(R : A → A → Set) : A → A → Set where
    tcin : ∀ {M N} → R M N → trans-clos R M N
    tccnc : ∀ {M N L} → trans-clos R M N → R N L → trans-clos R M L

  -- the transitive closure is transitive
  trnclos-trans : {A : Set}(R : A → A → Set){M N L : A}
                    → trans-clos R M N → trans-clos R N L → trans-clos R M L
  trnclos-trans R red (tcin stp) =           tccnc red stp
  trnclos-trans R red₁ (tccnc red₂ stp) =    tccnc (trnclos-trans R red₁ red₂) stp

  -- and it is the minimal such
  trnclos-min : {A : Set}(R S : A → A → Set)
                  → (∀ {M N L} → S M N → S N L → S M L) → (∀ {M N} → R M N → S M N)
                      → ∀ {M N} → trans-clos R M N → S M N
  trnclos-min R S trnS inS {M} (tcin stp) =     inS stp
  trnclos-min R S trnS inS (tccnc red stp) =    trnS (trnclos-min R S trnS inS red) (inS stp)

  -- it is also functorial wrt the order of binary relation
  trnclos-fun : {A : Set}{R S : A → A → Set}
                  → (∀ {M N} → R M N → S M N)
                    → ∀ {M N} → trans-clos R M N → trans-clos S M N
  trnclos-fun inS (tcin r) =                               tcin (inS r)
  trnclos-fun inS {N = N} (tccnc {M} {M'} {N} red r) =     tccnc (trnclos-fun inS red) (inS r)



  -- the reflexive and transitive closure
  data refl-trans-clos {A : Set}(R : A → A → Set) : A → A → Set where
    tcrfl : ∀ M → refl-trans-clos R M M
    tccnc : ∀ {M N L} → refl-trans-clos R M N → R N L → refl-trans-clos R M L

  -- the refl-trans closure is transitive
  rtclos-trans : {A : Set}(R : A → A → Set){M N L : A}
                    → refl-trans-clos R M N → refl-trans-clos R N L → refl-trans-clos R M L
  rtclos-trans R {M} {N} red₁ (tcrfl N) = red₁
  rtclos-trans R red₁ (tccnc red₂ stp) = tccnc (rtclos-trans R red₁ red₂) stp

  -- it contains the orignal relation
  rtclos-in : {A : Set}(R : A → A → Set){M N : A}
                    → R M N → refl-trans-clos R M N
  rtclos-in R {M} r  = tccnc (tcrfl M) r

  -- and it is the minimal such
  rtclos-min : {A : Set}(R S : A → A → Set)
                  → (∀ {M} → S M M) → (∀ {M N L} → S M N → S N L → S M L)
                    → (∀ {M N} → R M N → S M N)
                      → ∀ {M N} → refl-trans-clos R M N → S M N
  rtclos-min R S rflS trnS inS {M} (tcrfl M) =
    rflS {M = M}
  rtclos-min R S rflS trnS inS (tccnc red r) =
    trnS (rtclos-min R S rflS trnS inS red) (inS r)

  -- it is also functorial wrt the order of binary relation
  rtclos-fun : {A : Set}{R S : A → A → Set}
                  → (∀ M N → R M N → S M N)
                    → ∀ {M N} → refl-trans-clos R M N → refl-trans-clos S M N
  rtclos-fun pf (tcrfl M) =
    tcrfl M
  rtclos-fun pf {N = N} (tccnc {M} {M'} {N} red r) =
    tccnc (rtclos-fun pf red) (pf M' N r)


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

  fnct-to-List : ∀ {A n} → (Fin n → A) → Σ[ List A ] (λ x → n == lenList x)
  fnct-to-List {A} {zero} f = [] ,, =rf
  fnct-to-List {A} {suc n} f = f fz ∣ pj1 ih ,, =ap suc (pj2 ih)
    where ih : Σ[ List A ] (λ x → n == lenList x)
          ih = fnct-to-List {A} {n} (f ∘ fs)

  -- lists up to the order of their elements (= multi-sets)
  infix 15 _≡_ _≡⋆_
  data _≡_ {A : Set} : List A → List A → Set where
    ≡[] : [] ≡ []
    ≡cnc : ∀ {α α'} a → α ≡ α' → a ∣ α ≡ a ∣ α'
    ≡swp : ∀ {α α'} a b → α ≡ α' → a ∣ b ∣ α ≡ b ∣ a ∣ α'

  ≡rfl : {A : Set} → {α : List A} → α ≡ α
  ≡rfl {α = []} = ≡[]
  ≡rfl {α = a ∣ α} = ≡cnc a ≡rfl

  -- transitive closure, i.e. the actual equivalence relation
  _≡⋆_ : {A : Set} → List A → List A → Set
  _≡⋆_ = trans-clos _≡_
  ≡⋆rfl : {A : Set} → {α : List A} → α ≡⋆ α
  ≡⋆rfl = tcin ≡rfl
  ≡⋆cnc : {A : Set} → {α β γ : List A} → α ≡⋆ β → β ≡ γ → α ≡⋆ γ
  ≡⋆cnc = tccnc
  ≡⋆in : {A : Set} → {α β : List A} → α ≡ β  → α ≡⋆ β
  ≡⋆in = tcin
  ≡⋆tr : {A : Set} → {α β γ : List A} → α ≡⋆ β → β ≡⋆ γ → α ≡⋆ γ
  ≡⋆tr = trnclos-trans _≡_

  ≡⋆ext : {A : Set} → {α β : List A} → (a : A) → α ≡⋆ β → a ∣ α ≡⋆ a ∣ β
  ≡⋆ext a (tcin eqv) =                   ≡⋆in (≡cnc a eqv)
  ≡⋆ext a (tccnc {α} {α'}  ch eqv) =     ≡⋆cnc (≡⋆ext a ch) (≡cnc a eqv)  

  ≡swpcnc : {A : Set} → {α α' : List A} → {a b : A} → α ≡ b ∣ α' → a ∣ α ≡⋆ b ∣ a ∣ α'
  ≡swpcnc {a = a} {b} (≡cnc b eqv) =  tcin (≡swp a b eqv)
  ≡swpcnc {a = a} (≡swp c b eqv) =    tccnc (tcin (≡cnc a (≡swp c b ≡rfl))) (≡swp a b (≡cnc c eqv))

  ≡⋆swpcnc : {A : Set} → {α α' : List A} → {a b : A} → α ≡⋆ b ∣ α' → a ∣ α ≡⋆ b ∣ a ∣ α'
  ≡⋆swpcnc {a = a} {b} (tcin eqv) =               ≡swpcnc eqv
  ≡⋆swpcnc {a = a} {b} (tccnc {α} {β} ch eqv) =   ≡⋆tr (≡⋆ext a ch) (≡swpcnc eqv)

  ≡-∋ : {A : Set} → {α α' : List A} → {a : A} → α ≡ α' → α ∋ a → α' ∋ a
  ≡-∋ (≡cnc a eqv) here = here
  ≡-∋ (≡cnc c eqv) (there inp) = there (≡-∋ eqv inp)
  ≡-∋ (≡swp a b eqv) here = there here
  ≡-∋ (≡swp c a eqv) (there here) = here
  ≡-∋ (≡swp c b eqv) (there (there inp)) = there (there (≡-∋ eqv inp))

  ≡⋆-∋ : {A : Set} → {α α' : List A} → {a : A} → α ≡⋆ α' → α ∋ a → α' ∋ a
  ≡⋆-∋ (tcin eqv) inp = ≡-∋ eqv inp
  ≡⋆-∋ (tccnc {α} {β} ch eqv) inp = ≡-∋ eqv (≡⋆-∋ ch inp)

-- end file
