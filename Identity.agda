{-# OPTIONS --without-K #-}

module Identity where
  open import Basic-Inductives public

  -- need function extensionality
  postulate FunExtd : {A : Set}{B : A → Set}{f g : ∀ a → B a}
                         → (∀ a → f a == g a) → f == g
  FunExt : {A B : Set}{f g : A → B} → (∀ a → f a == g a) → f == g
  FunExt = FunExtd

  -- Paulin-Mohring eliminator
  =J : {A : Set}{a₀ : A}(B : (a : A) → a₀ == a → Set)
          → B a₀ =rf → {a : A} → (p : a₀ == a) → B a p
  =J B b₀ =rf = b₀


  -- Transport & friends

  =ap : {A B : Set}(f : A → B){a a' : A} → a == a' → f a == f a'
  =ap f = =J (λ x _ → f _ == f x) =rf

  =ap∘ : {A B C : Set}(f : A → B)(g : B → C){a a' : A}
            → (p : a == a') → =ap g (=ap f p) == =ap (g ∘ f) p
  =ap∘ f g = =J (λ _ u → =ap g (=ap f u) == =ap (g ∘ f) u) =rf

  =ap₂ : {A₁ A₂ B : Set}(f : A₁ → A₂ → B){a₁ a₁' : A₁}{a₂ a₂' : A₂}
             → a₁ == a₁' → a₂ == a₂' → f a₁ a₂ == f a₁' a₂'
  =ap₂ f {a₁} {a₁'} {a₂} {a₂'} = =J (λ x _ → (a₂ == a₂' → f a₁ a₂ == f x a₂'))
                                    (=ap (f a₁))

  =transp : {A : Set}(B : A → Set){a a' : A} → a == a' → B a → B a'
  =transp B {a} = =J (λ x _ → B a → B x) id

  =transp₂ : {A B : Set}(C : A → B → Set){a a' : A}{b b' : B}
                → a == a' → b == b' → C a b → C a' b'
  =transp₂ C {a} {a'} {b} {b'} p q = =transp (C a') q ∘ =transp (λ x → C x b) p

  infix 40 _●_
  _●_ : {A : Set}(B : A → Set) {a a' : A} → a == a' → B a → B a'
  B ● p = =transp B p

  =ptw : {A : Set}{B : A → Set}{f g : (a : A) → B a} → f == g → (a : A) → f a == g a
  =ptw {f = f} p a = ((λ x → f a == x a) ● p) =rf

  =transpcnst : {A : Set}(B : Set){a a' : A}(p : a == a')(b : B) → ((λ _ → B) ● p) b == b
  =transpcnst B p b = =J (λ x q → ( ((λ _ → B) ● q) b == b )) =rf p

  =apd : {A : Set}{B : A → Set}(f : (a : A) → B a){a a' : A}(p : a == a') → (B ● p) (f a) == f a'
  =apd f p = =J (λ x p → (_ ● p) (f _) == f x) =rf p

  =sym : {A : Set}{a a' : A} → a == a' → a' == a
  =sym p = ((λ x → x == _) ● p) =rf

  =tra : {A : Set}{a₁ a₂ a₃ : A} → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
  =tra p q = ((λ x → _ == x) ● q) p

  ●=ap-is-● : {A' A : Set}(B : A → Set) (f : A' → A) {a a' : A'} → (u : a == a')
                  → ∀ b → (B ● (=ap f u)) b == ((B ∘' f) ● u) b
  ●=ap-is-● B f = =J (λ x u → ∀ b → (B ● =ap f u) b == ((B ∘' f) ● u) b)
                     (λ _ → =rf)

  ●=ap-is-●⁻¹ : {A' A : Set}(B : A → Set) (f : A' → A) {a a' : A'} → (u : a == a')
                  → ∀ b → ((B ∘' f) ● u) b == (B ● (=ap f u)) b
  ●=ap-is-●⁻¹ B f = =J (λ x u → ∀ b → ((B ∘' f) ● u) b == (B ● =ap f u) b)
                       (λ _ → =rf)

  =ap₂-rfr :  {A₁ A₂ B : Set}(f : A₁ → A₂ → B){a₁ : A₁}{a₂ a₂' : A₂}
                  → (q : a₂ == a₂') → =ap₂ f =rf q == =ap (f a₁) q
  =ap₂-rfr {A₁} {A₂} {B} f q = =rf
  =ap₂-rfr⁻¹ :  {A₁ A₂ B : Set}(f : A₁ → A₂ → B){a₁ : A₁}{a₂ a₂' : A₂}
                  → (q : a₂ == a₂') → =ap (f a₁) q == =ap₂ f =rf q
  =ap₂-rfr⁻¹ f q = =sym (=ap₂-rfr f q)
  =ap₂-rfl :  {A₁ A₂ B : Set}(f : A₁ → A₂ → B){a₁ a₁' : A₁}{a₂ : A₂}
                  → (p : a₁ == a₁') → =ap₂ f p =rf == =ap (λ x → f x a₂) p
  =ap₂-rfl {A₁} {A₂} {B} f {a₂ = a₂} = =J (λ _ u → =ap₂ f u =rf == =ap (λ x → f x a₂) u)
                                          =rf
  =ap₂-rfl⁻¹ :  {A₁ A₂ B : Set}(f : A₁ → A₂ → B){a₁ a₁' : A₁}{a₂ : A₂}
                  → (p : a₁ == a₁') → =ap (λ x → f x a₂) p == =ap₂ f p =rf
  =ap₂-rfl⁻¹ f p = =sym (=ap₂-rfl f p)
 


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

  =ap• : {A B : Set}(f : A → B){a a' a'' : A}(p : a == a')(p' : a' == a'')
            → =ap f (p • p') == =ap f p • =ap f p'
  =ap• f p = =J (λ x u → =ap f (p • u) == =ap f p • =ap f u) =rf
  =ap•⁻¹ : {A B : Set}(f : A → B){a a' a'' : A}(p : a == a')(p' : a' == a'')
            → =ap f p • =ap f p' == =ap f (p • p')
  =ap•⁻¹ f p p' = =ap• f p p' ⁻¹
  =ap-sym : {A B : Set}(f : A → B){a a' : A}(p : a == a')
               → =ap f (p ⁻¹) == =ap f p ⁻¹
  =ap-sym f = =J (λ x u → =ap f (u ⁻¹) == =ap f u ⁻¹) =rf
  =ap-sym⁻¹ : {A B : Set}(f : A → B){a a' : A}(p : a == a')
               → =ap f p ⁻¹ == =ap f (p ⁻¹)
  =ap-sym⁻¹ f p = =ap-sym f p ⁻¹
  =ap∘⁻¹ : {A B C : Set}(f : A → B)(g : B → C){a a' : A}
            → (p : a == a') → =ap (g ∘ f) p == =ap g (=ap f p)
  =ap∘⁻¹ f g p = =ap∘ f g p ⁻¹

  -- functions are functors
  •=ap : {A B : Set} → (f : A → B) → ∀ {a₁ a₂ a₃} → (p : a₁ == a₂) → (q : a₂ == a₃)
           → =ap f (p • q) == =ap f p • =ap f q
  •=ap f p = =J (λ x u → =ap f (p • u) == =ap f p • =ap f u) =rf

  ⁻¹=ap : {A B : Set} → (f : A → B) → ∀ {a₁ a₂} → (p : a₁ == a₂)
           → =ap f (p ⁻¹) == =ap f p ⁻¹
  ⁻¹=ap f = =J (λ x u → =ap f (u ⁻¹) == =ap f u ⁻¹) =rf


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

  •⁻¹ : {A : Set}{a₁ a₂ a₃ : A}(p₁ : a₁ == a₂)(p₂ : a₂ == a₃)
           → (p₁ • p₂) ⁻¹ == p₂ ⁻¹ • p₁ ⁻¹
  •⁻¹ p₁ = =J (λ x u → (p₁ • u) ⁻¹ == u ⁻¹ • p₁ ⁻¹) (•idl (p₁ ⁻¹) ⁻¹)

  •⁻¹g : {A : Set}{a₁ a₂ a₃ : A}{p₁ : a₁ == a₂}{p₂ : a₂ == a₃}{p₃ : a₁ == a₃}
           → p₃ == p₁ • p₂ → p₃ ⁻¹ == p₂ ⁻¹ • p₁ ⁻¹
  •⁻¹g {A} {a₁} {p₁ = p₁} {p₂} =
    =J (λ x u → ∀ {y u'} {u'' : a₁ == y} → u'' == u • u' → u'' ⁻¹ == u' ⁻¹ • u ⁻¹)
       (λ {_} {u'} {u''} tr → =ap =sym (tr • •idl u'))
       p₁
       {_} {p₂}

  •⁻¹g⁻¹ : {A : Set}{a₁ a₂ a₃ : A}{p₁ : a₁ == a₂}{p₂ : a₂ == a₃}{p₃ : a₁ == a₃}
           → p₁ • p₂ == p₃ → p₂ ⁻¹ • p₁ ⁻¹ == p₃ ⁻¹
  •⁻¹g⁻¹ {A} {a₁} {p₁ = p₁} {p₂} =
    =J (λ x u → ∀ {y u'} {u'' : a₁ == y} → u • u' == u'' → u' ⁻¹ • u ⁻¹ == u'' ⁻¹)
       (λ {_} {u'} {u''} tr → =ap =sym (•idl u' ⁻¹ • tr))
       p₁
       {_} {p₂}

  •⁻¹-⁻¹ : {A : Set}{a₁ a₂ a₃ : A}(p₁ : a₁ == a₂)(p₂ : a₂ == a₃)
           → p₂ ⁻¹ • p₁ ⁻¹ == (p₁ • p₂) ⁻¹
  •⁻¹-⁻¹ p₁ = =J (λ x u → u ⁻¹ • p₁ ⁻¹ == (p₁ • u) ⁻¹) (•idl (p₁ ⁻¹))

  ⁻¹⁻¹=id : {A : Set}{a₁ a₂ : A}(p : a₁ == a₂) → (p ⁻¹) ⁻¹ == p
  ⁻¹⁻¹=id p = =J (λ _ u → (u ⁻¹) ⁻¹ == u) =rf p

  =ap-sq : {A B : Set}{f g : A → B} → (eq : ∀ a → f a == g a)
              → ∀ {a a'} → (p : a == a') → =ap f p • eq a' == eq a • =ap g p
  =ap-sq {f = f} {g} eq {a} = =J (λ a' p → =ap f p • eq a' == eq a • =ap g p) (•idl (eq a))


  -- Some equations between proofs of equations

  •extl : {A : Set}{a₁ a₂ : A}(p : a₁ == a₂){a₃ : A}{p₁ p₂ : a₂ == a₃}
             → p₁ == p₂ → p • p₁ == p • p₂
  •extl p = =ap (p •_)

  •extr : {A : Set}{a₂ a₃ : A}(p : a₂ == a₃){a₁ : A}{p₁ p₂ : a₁ == a₂}
             → p₁ == p₂ → p₁ • p == p₂ • p
  •extr p = =ap (_• p)

  •extlr : {A : Set}{a₁ a₂ a₃ : A}{p₁ p₂ : a₁ == a₂}{q₁ q₂ : a₂ == a₃}
             → p₁ == p₂ → q₁ == q₂ → p₁ • q₁ == p₂ • q₂
  •extlr = =ap₂ _•_

  •idlg : {A : Set}{a₁ a₂ : A}{p₁ : a₁ == a₁}{p₂ : a₁ == a₂}{p₃ : a₁ == a₂}
           → p₁ == =rf → p₁ • p₂ == p₃ → p₂ == p₃
  •idlg {p₁ = p₁} {p₂} {p₃} hrf h = =proof p₂         ==[ •idl p₂ ⁻¹ ] /
                                         =rf • p₂     ==[ •extr p₂ (hrf ⁻¹) ] /
                                         p₁ • p₂      ==[ h ]∎
                                         p₃ ∎

  •idlg-inv : {A : Set}{a₁ a₂ : A}{p₁ : a₁ == a₁}{p₂ : a₁ == a₂}{p₃ : a₁ == a₂}
           → p₁ == =rf → p₂ == p₃ → p₁ • p₂ == p₃
  •idlg-inv {p₁ = p₁} {p₂} {p₃} hrf h = =proof p₁ • p₂     ==[ •extr p₂ hrf ] /
                                                =rf • p₂   ==[ •idl p₂ • h ]∎
                                                p₃ ∎


  •idrg : {A : Set}{a₁ a₂ : A}{p₁ : a₁ == a₂}{p₂ : a₂ == a₂}{p₃ : a₁ == a₂}
           → p₂ == =rf → p₁ • p₂ == p₃ → p₁ == p₃
  •idrg {p₁ = p₁} {p₂} {p₃} hrf h = =proof p₁         ==[ •idr p₁ ⁻¹ ] /
                                           p₁ • =rf   ==[ •extl p₁ (hrf ⁻¹) ] /
                                           p₁ • p₂    ==[ h ]∎
                                           p₃ ∎

  •idrg-inv : {A : Set}{a₁ a₂ : A}{p₁ : a₁ == a₂}{p₂ : a₂ == a₂}{p₃ : a₁ == a₂}
           → p₂ == =rf → p₁ == p₃ → p₁ • p₂ == p₃
  •idrg-inv {p₁ = p₁} {p₂} {p₃} hrf h = =proof p₁ • p₂     ==[ •extl p₁ hrf ] /
                                               p₁ • =rf   ==[ •idr p₁ • h ]∎
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


  ==-is-nat : {A B : Set}{f g : A → B} → (h : ∀ a → f a == g a)
                 → ∀ {a} {a'} (p : a == a') → =ap f p • h a' == h a • =ap g p
  ==-is-nat h =rf = •idl (h _)

  ==-is-nat-id : {A : Set}{f : A → A} → (h : ∀ a → f a == a)
                 → ∀ {a} {a'} (p : a == a') → =ap f p • h a' == h a • p
  ==-is-nat-id h =rf = •idl (h _)


  →• : {A B : Set}{C : A → Set}{a a' : A}(p : a == a')(f : B → C a)
          → ∀ b → ((λ x → B → C x) ● p) f b == (C ● p) (f b)
  →• {A} {B} {C} p f b = =J (λ x u → ((λ x' → B → C x') ● u) f b == (C ● u) (f b))
                                =rf
                                p

  →•ptw : {A B : Set}{C : A → Set}{a a' : A}(p : a == a')(f : B → C a)
          → ∀ b → ((λ x → B → C x) ● p) f b == (C ● p) (f b)
  →•ptw {A} {B} {C} p f b = =J (λ x u → ((λ x' → B → C x') ● u) f b == (C ● u) (f b))
                                =rf
                                p

  →•ptw₂ : {A B : Set}{C : A → B → Set}{a a' : A}(p : a == a')(f : ∀ y → C a y)
          → ∀ b → ((λ x → ∀ y → C x y) ● p) f b == ((λ x → C x b) ● p) (f b)
  →•ptw₂ {A} {B} {C} p f b = =J (λ x u → ((λ x' → ∀ y → C x' y) ● u) f b == ((λ x → C x b) ● u) (f b))
                                =rf
                                p

  --part of Lemma 2.9.6 in HoTT book
  HoTTLemma2-9-6 : {A : Set}{B C : A → Set}{a a' : A}(p : a == a')
                   {f : B a → C a}{g : B a' → C a'}
                     → ((λ x → B x → C x) ● p) f == g
                       → (y : B a) → (C ● p) (f y) == g ((B ● p) y)
  HoTTLemma2-9-6 {A} {B} {C} {a} {a'} p = =J JEl JElrf p
    where JEl : (x : A) → a == x → Set
          JEl x u = {f : B a → C a}{g : B x → C x} →
                       ((λ x → B x → C x) ● u) f == g → (y : B a) → (C ● u) (f y) == g ((B ● u) y)
          JElrf : JEl a =rf
          JElrf = =ptw

  {-
  -- transport of fibrewise functions is pointwise
  ●ptw : {A : Set}{B C : A → Set}(f : (a : A) → B a → C a)
         {a a' : A}(p : a == a')(b : B a')
            → ((λ x → B x → C x) ● p) (f a) b == (C ● p) (f a ((B ● p ⁻¹) b))
  ●ptw f p b = let ψ : _
                   ψ = {!!}
               in {!!}
  -}

  -- identities of composition

  ∘ass : {A B C D : Set}(f : A → B)(g : B → C)(h : C → D)
            → (h ∘ g) ∘ f == h ∘ g ∘ f
  ∘ass f g h = =rf
  ∘ass⁻¹ : {A B C D : Set}(f : A → B)(g : B → C)(h : C → D)
            → h ∘ g ∘ f == (h ∘ g) ∘ f
  ∘ass⁻¹ f g h = ∘ass f g h ⁻¹


  -- transport and groupoids

  =transp-precmp-rf : {A : Set}{a₁ a₂ : A}(p : a₁ == a₂)
                      → ((_== a₂) ● p ⁻¹) =rf == p
  =transp-precmp-rf = =J (λ x u → ((_== x) ● u ⁻¹) =rf == u) =rf
  =transp-precmp : {A : Set}{a₁ a₂ a₃ : A}(p : a₁ == a₂)(q : a₂ == a₃)
                      → ((_== a₃) ● p ⁻¹) q == p • q
  =transp-precmp {a₃ = a₃} p = =J (λ x u → ((_== x) ● p ⁻¹) u == p • u)
                                  (=transp-precmp-rf p)

  =transp-precmp-inv : {A : Set}{a₁ a₂ a₃ : A}(p : a₂ == a₁)(q : a₂ == a₃)
                      → ((_== a₃) ● p) q == p ⁻¹ • q
  =transp-precmp-inv {a₃ = a₃} p q = =J (λ x u → ((_== a₃) ● u) q == u ⁻¹ • q)
                                        (•idl q ⁻¹)
                                        p

  transp-ext : {A : Set}(B : A → Set){a a' : A}{p p' : a == a'}
                  → p == p' → B ● p == B ● p'
  transp-ext B {p = p} = =J (λ u _ → B ● p == B ● u) =rf

  transp-ext-ptw : {A : Set}(B : A → Set){a a' : A}{p p' : a == a'}
                  → p == p' → ∀ b →  (B ● p) b == (B ● p') b
  transp-ext-ptw B eq = =ptw (transp-ext B eq)

  transp-flip : {A : Set}(B : A → Set){a a' a'' : A}(p : a == a')
                   → ∀ {b b'} → (B ● p) b == b' → b == (B ● p ⁻¹) b'
  transp-flip B = =J (λ _ u → ∀ {b b'} → (B ● u) b == b' → b == (B ● u ⁻¹) b')
                     id

  transp-flip⁻¹ : {A : Set}(B : A → Set){a a' a'' : A}(p : a == a')
                   → ∀ {b b'} → b' == (B ● p) b → (B ● p ⁻¹) b' == b
  transp-flip⁻¹ B = =J (λ _ u → ∀ {b b'} → b' == (B ● u) b → (B ● u ⁻¹) b' == b)
                       id

  transp-flip-inv : {A : Set}(B : A → Set){a a' a'' : A}(p : a == a')
                       → ∀ {b b'} → b == (B ● p ⁻¹) b' → (B ● p) b == b'
  transp-flip-inv B = =J (λ _ u → ∀ {b b'} → b == (B ● u ⁻¹) b' → (B ● u) b == b')
                         id

  transp-flip-inv⁻¹ : {A : Set}(B : A → Set){a a' a'' : A}(p : a == a')
                         → ∀ {b b'} → (B ● p ⁻¹) b' == b → b' == (B ● p) b
  transp-flip-inv⁻¹ B = =J (λ _ u → ∀ {b b'} → (B ● u ⁻¹) b' == b → b' == (B ● u) b)
                           id

  transp-• : {A : Set}(B : A → Set){a a' a'' : A}(p : a == a')(q : a' == a'')
                → (B ● q) ∘ (B ● p) == B ● (p • q)
  transp-• B p = =J (λ _ u → (B ● u) ∘ (B ● p) == B ● (p • u)) =rf

  transp-•-ptw : {A : Set}(B : A → Set){a a' a'' : A}(p : a == a')(q : a' == a'')
               → ∀ b → (B ● q) ((B ● p) b) == (B ● (p • q)) b
  transp-•-ptw B p q = =ptw (transp-• B p q)

  transp-back-forth : {A : Set}(B : A → Set){a a' : A}(p : a == a')
                         → (B ● p) ∘ (B ● p ⁻¹) == id
  transp-back-forth B p = =proof
    B ● p ∘ B ● p ⁻¹  ==[ transp-• B (p ⁻¹) p ] /
    B ● p ⁻¹ • p      ==[ transp-ext B (•invl p) ]∎
    id ∎

  transp-back-forth-ptw : {A : Set}(B : A → Set){a a' : A}(p : a == a')
                         → ∀ b' → (B ● p) ((B ● p ⁻¹) b') == b'
  transp-back-forth-ptw B p = =ptw (transp-back-forth B p)

  transp-forth-back : {A : Set}(B : A → Set){a a' : A}(p : a == a')
                         → (B ● p ⁻¹) ∘ (B ● p) == id
  transp-forth-back B p = =proof
    B ● p ⁻¹ ∘ B ● p  ==[ transp-• B p (p ⁻¹) ] /
    B ● p • p ⁻¹      ==[ transp-ext B (•invr p) ]∎
    id ∎

  transp-forth-back-ptw : {A : Set}(B : A → Set){a a' : A}(p : a == a')
                         → ∀ b' → (B ● p ⁻¹) ((B ● p) b') == b'
  transp-forth-back-ptw B p = =ptw (transp-forth-back B p)

  ---------------------------------
  -- Identities of inductive types
  ---------------------------------

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

  =pj1 : ∀ {A B} {z z' : Σ[ A ] B} → z == z' → pj1 z == pj1 z'
  =pj1 = =ap pj1
  Bpj1● : ∀ {A B} {z z' : Σ[ A ] B} → (u : z == z')
            → ∀ b → (B ● (=pj1 u)) b == ((λ z → B (pj1 z)) ● u) b
  Bpj1● {A} {B} = ●=ap-is-● B pj1

  =pj2 : ∀ {A B} {z z' : Σ[ A ] B} → (u : z == z') → ((λ z → B (pj1 z)) ● u) (pj2 z) == pj2 z'
  =pj2 {A} {B} {z} {z'} u = =apd {A = Σ[ A ] B} {B = λ z → B (pj1 z)} pj2 u
  =pj2' : ∀ {A B} {z z' : Σ[ A ] B} → (u : z == z') → (B ● (=pj1 u)) (pj2 z) == pj2 z'
  =pj2' {A} {B} {z} {z'} u = =proof
    (B ● =pj1 u) (pj2 z)                  ==[ Bpj1● u (pj2 z) ] /
    ((λ z₁ → B (pj1 z₁)) ● u) (pj2 z)    ==[ =pj2 u ]∎
    pj2 z' ∎

  Ση : ∀ {A} {B : A → Set}(z : Σ[ A ] B) → (pj1 z) ,, (pj2 z) == z
  Ση (a ,, b) = =rf
  Ση⁻¹ : ∀ {A} {B : A → Set}(z : Σ[ A ] B) → z == (pj1 z) ,, (pj2 z)
  Ση⁻¹ (a ,, b) = =rf

  =Σover,, :  ∀ {A} {B : A → Set} {a : A}
               → {b b' : B a} → b == b' → _,,_ {A} {B} a b == a ,, b'
  =Σover,, {a = a} {b} = =J (λ w _ → a ,, b == a ,, w) =rf

  =Σover :  ∀ {A} {B : A → Set} {z : Σ[ A ] B}
               → ∀ {b} → b == pj2 z → pj1 z ,, b == z
  =Σover {z = z} eq = =Σover,, {a = pj1 z} eq • Ση z
    -- =J (λ w _ → pj1 z ,, w == z) (Ση z)

  =Σover⁻¹ :  ∀ {A} {B : A → Set} {z : Σ[ A ] B}
               → ∀ {b} → pj2 z == b → z == pj1 z ,, b
  =Σover⁻¹ {z = z} eq = Ση⁻¹ z • =Σover,, {a = pj1 z} eq
    -- =J (λ w _ → z == pj1 z ,, w) (Ση⁻¹ z)

  =Σchar,, : ∀ {A} {B : A → Set} {z : Σ[ A ] B} {a'}
               → (u : pj1 z == a') → ∀ {b'} → (B ● u) (pj2 z) == b'
                 → z == a' ,, b'
  =Σchar,, {A} {B} {z} {a'} =
    =J (λ x y → ∀ {b'} → ((B ● y) (pj2 z)) == b' → z == x ,, b')
       (=Σover⁻¹ {z = z})

  =Σchar : ∀ {A} {B : A → Set}{z z' : Σ[ A ] B}
               → (u : pj1 z == pj1 z') → (B ● u) (pj2 z) == pj2 z'
                 → z == z'
  =Σchar {z = z} {a' ,, b'} u = =Σchar,, {z = z} {a'} u {b'}

  +-EM : {A B : Set} → (v : A + B)
            → Σ[ A ] (λ x → inl x == v) + Σ[ B ] (λ y → inr y == v)
  +-EM {A} {B} = +ind (λ v → Σ[ A ] (λ x → inl x == v) + Σ[ B ] (λ y → inr y == v))
                      (λ a → inl (a ,, =rf))
                      (λ b → inr (b ,, =rf))
  inl-inj : ∀ {A B a a'} → inl {A} {B} a == inl a' → a == a'
  inl-inj =rf = =rf
  inlinj=id : ∀ {A B a a'} → (eq : inl {A} {B} a == inl a') → =ap inl (inl-inj eq) == eq
  inlinj=id =rf = =rf
  injinl=id : ∀ {A B a a'} → (eq : a == a') → inl-inj (=ap (inl {A} {B}) eq) == eq
  injinl=id =rf = =rf
  inr-inj : ∀ {A B b b'} → inr {A} {B} b == inr b' → b == b'
  inr-inj =rf = =rf
  inrinj=id : ∀ {A B a a'} → (eq : inr {A} {B} a == inr a') → =ap inr (inr-inj eq) == eq
  inrinj=id =rf = =rf
  injinr=id : ∀ {A B a a'} → (eq : a == a') → inr-inj (=ap (inr {A} {B}) eq) == eq
  injinr=id =rf = =rf
  inl≠inr : ∀ {A B a b} → ¬ (inl {A} {B} a == inr b)
  inl≠inr ()
  inr≠inl : ∀ {A B a b} → ¬ (inr {A} {B} b == inl a)
  inr≠inl ()

  fnct-to-List : ∀ {A n} → (Fin n → A) → Σ[ List A ] (λ x → n == lenList x)
  fnct-to-List {A} {zero} f = [] ,, =rf
  fnct-to-List {A} {suc n} f = f fz ∣ pj1 ih ,, =ap suc (pj2 ih)
    where ih : Σ[ List A ] (λ x → n == lenList x)
          ih = fnct-to-List {A} {n} (f ∘ fs)

  ¬=sym : {A : Set} {a a' : A} → ¬ (a == a') → ¬ (a' == a)
  ¬=sym = ¬-is-covar =sym

  -- transport and inductive types

  ●pj1 : ∀ {A} {B : A → Set} (C : A → Set){z z' : Σ[ A ] B}(p : z == z')
           → C ● =pj1 p == (C ∘' pj1) ● p
  ●pj1 C = =J (λ _ u → C ● =pj1 u == (C ∘' pj1) ● u) =rf
  ●pj1-ptw : ∀ {A} {B : A → Set} (C : A → Set){z z' : Σ[ A ] B}(p : z == z')
                   → ∀ c → (C ● =pj1 p) c == ((C ∘' pj1) ● p) c
  ●pj1-ptw C p = =ptw (●pj1 C p)

  ●pj1⁻¹ : ∀ {A} {B : A → Set} (C : A → Set){z z' : Σ[ A ] B}(p : z == z')
             → (C ∘' pj1) ● p == C ● =pj1 p
  ●pj1⁻¹ C p = ●pj1 C p ⁻¹
  ●pj1⁻¹-ptw : ∀ {A} {B : A → Set} (C : A → Set){z z' : Σ[ A ] B}(p : z == z')
                 → ∀ c → ((C ∘' pj1) ● p) c == (C ● =pj1 p) c
  ●pj1⁻¹-ptw C p = =ptw (●pj1⁻¹ C p)

  =ap● : ∀ {A B C} {f : A → B} {g : B → C} {a a' : A} (p : a == a')
           → ∀ {b} {q : g (f a) == g b} (z : Σ[ f a == b ] (λ x → =ap g x == q))
               → ((λ x → g (f x) == g b) ● p) q == =ap g (((λ x → f x == b) ● p) (pj1 z))
  =ap● {A} {B} {C} {f} {g} {a} =
    =J (λ _ u → ∀ {b} {q : g (f a) == g b} (z : Σ[ f a == b ] (λ x → =ap g x == q))
              → ((λ x → g (f x) == g b) ● u) q == =ap g (((λ x → f x == b) ● u) (pj1 z)))
       (λ z → pj2 z ⁻¹)
    

  transp-inl : {A : Set}(B C : A → Set){a a' : A}(p : a == a')
                  → ((λ x → B x + C x) ● p) ∘ inl == inl ∘ (B ● p)
  transp-inl B C = =J (λ _ u → ((λ x → B x + C x) ● u) ∘ inl == inl ∘ (B ● u)) =rf

  transp-inl-ptw : {A : Set}(B C : A → Set){a a' : A}(p : a == a')
                  → ∀ b →  ((λ x → B x + C x) ● p) (inl b) == inl ((B ● p) b)
  transp-inl-ptw B C p = =ptw (transp-inl B C p)

  transp-inr : {A : Set}(B C : A → Set){a a' : A}(p : a == a')
                  → ((λ x → B x + C x) ● p) ∘ inr == inr ∘ (C ● p)
  transp-inr B C = =J (λ _ u → ((λ x → B x + C x) ● u) ∘ inr == inr ∘ (C ● u)) =rf

  transp-inr-ptw : {A : Set}(B C : A → Set){a a' : A}(p : a == a')
                  → ∀ c →  ((λ x → B x + C x) ● p) (inr c) == inr ((C ● p) c)
  transp-inr-ptw B C p = =ptw (transp-inr B C p)

  -------------------------
  -- Contractibility & Co.
  -------------------------

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
  ∀-is-prop : ∀ {A} (B : A → Set) → (∀ a → isProp (B a)) → isProp (∀ a → B a)
  ∀-is-prop B BisP-ptw b b' = FunExtd λ a → BisP-ptw a (b a) (b' a)

  isSet : (A : Set) → Set
  isSet A = {a a' : A} → isProp (a == a')

  isProp→=isContr : {A : Set} → isProp A → ∀ a a' → isContr (a == a')
  isProp→=isContr {A} ispr = λ a a' → ispr a a' ,, ispr-uq {a} {a'}
    where ispr-tr : {a a' : A}(u : a == a') → ispr a a • u == ispr a a'
          ispr-tr {a} = =J (λ x u → ispr a a • u == ispr a x) =rf
          ispr-trr : (a : A) → ispr a a • ispr a a == ispr a a
          ispr-trr a = ispr-tr (ispr a a)
          ispr-rf : (a : A) → ispr a a == =rf
          ispr-rf a = =proof
            ispr a a                            ==[ •idrg-inv (•invr (ispr a a)) =rf ⁻¹ ] /
            ispr a a • ispr a a • ispr a a ⁻¹   ==[ •ass (ispr a a) (ispr a a) (ispr a a ⁻¹)
                                                    • (•extr (ispr a a ⁻¹) (ispr-trr a)) ] /
            ispr a a • ispr a a ⁻¹              ==[ •invr (ispr a a) ]∎
            =rf ∎
          ispr-uq : {a a' : A}(u : a == a') → u == ispr a a'
          ispr-uq {a} {a'} u = =proof
            u                ==[ •idlg-inv (ispr-rf a) (=rf {a = u}) ⁻¹ ] /
            ispr a a • u     ==[ ispr-tr u ]∎
            ispr a a' ∎

  isProp→=isProp : {A : Set} → isProp A → {a a' : A} → isProp (a == a')
  isProp→=isProp {A} isprA {a} {a'} =
    λ p q → contr= (isProp→=isContr isprA a a') p • contr= (isProp→=isContr isprA a a') q ⁻¹

  isContr→=isContr : {A : Set} → isContr A → {a a' : A} → isContr (a == a')
  isContr→=isContr cnt {a} {a'} =
    contr= cnt a • contr= cnt a' ⁻¹
    ,, =J (λ x u → u == contr= cnt a • contr= cnt x ⁻¹) (•invr (contr= cnt _) ⁻¹)

  isContr→isProp : {A : Set} → isContr A → isProp A
  isContr→isProp cnt = λ a a' → contr= cnt a • contr= cnt a' ⁻¹

  true-prop-is-contr : ∀ {A} → isProp A → A → isContr A
  true-prop-is-contr prpA a = a ,, λ x → prpA x a
  
  -- I am using ∀-is-prop here
  isContr-is-prop : (A : Set) → isProp (isContr A)
  isContr-is-prop A z z' = =Σchar (u₁ a₀) (→=isprop _ _)
    where a₀ a₁ : A
          a₀ = pj1 z
          a₁ = pj1 z'
          u₀ : ∀ a → a == a₀
          u₀ = pj2 z
          u₁ : ∀ a → a == a₁
          u₁ = pj2 z'
          =iscntr : ∀ a → isContr (a == a₁)
          =iscntr a = isContr→=isContr z {a} {a₁}
          →=isprop : isProp (∀ a → a == a₁)
          →=isprop = ∀-is-prop (λ a → a == a₁) (λ a → isContr→isProp (=iscntr a))
          
  ●irrel :  {A  : Set} {B : A → Set} → isSet A
                 → ∀ {a a'} (p q : a == a') → (B ● p) == (B ● q)
  ●irrel {A} {B} issetA p q = =ap (B ●_) (issetA p q)
  ●irrelₚₜ :  {A  : Set} {B : A → Set} → isSet A
                 → ∀ {a a'} (p q : a == a') → ∀ b → (B ● p) b == (B ● q) b
  ●irrelₚₜ issetA p q = =ptw (●irrel issetA p q)
  ●loop=id : {A  : Set} {B : A → Set} → isSet A
                 → ∀ {a} (p : a == a) → (B ● p) == id
  ●loop=id {A} {B} issetA p = ●irrel issetA p =rf
  ●loop=idₚₜ : {A  : Set} {B : A → Set} → isSet A
                 → ∀ {a} (p : a == a) → ∀ b → (B ● p) b == b
  ●loop=idₚₜ issetA p = =ptw (●loop=id issetA p)
  

  N₀-is-prop : isProp N₀
  N₀-is-prop = λ _ → N₀ind
  →-is-prop : (A {B} : Set) → isProp B → isProp (A → B)
  →-is-prop A {B} isprB = ∀-is-prop {A} (λ _ → B) (λ _ → isprB)
  ¬-is-prop : (A : Set) → isProp (¬ A)
  ¬-is-prop A = →-is-prop A N₀-is-prop

  =η : {A : Set} (a : A) → isContr (Σ[ A ] (a ==_))
  =η {A} a = (a ,, =rf) ,, λ z → =Σchar,, (pj2 z ⁻¹) (•invr (pj2 z))
  =η⁻¹ : {A : Set} (a : A) → isContr (Σ[ A ] (_== a))
  =η⁻¹ {A} a = (a ,, =rf) ,, λ z → =Σchar,, (pj2 z) (=proof
    ((_== a) ● pj2 z) (pj2 z)     ==[ =transp-precmp-inv (pj2 z) (pj2 z) ] /
    pj2 z ⁻¹ • pj2 z              ==[ •invl (pj2 z) ]∎
    =rf ∎)

  -- the fibre of a function
  fib : ∀ {A B} → (f : A → B) → B → Set
  fib {A} f b = Σ[ A ] (λ x → f x == b)  

  =transp-fib : ∀ {A B} {f : A → B} → ∀ {b} → (z : fib f b) → ∀ {a} → (p : a == pj1 z)
                  → =transp (λ x → f x == b) (p ⁻¹) (pj2 z) == =ap f p • pj2 z
  =transp-fib {f = f} {b} z p =
    =J (λ x u → (y : f x == b) → =transp (λ x → f x == b) (u ⁻¹) y == =ap f u • y)
       (λ y → •idl y ⁻¹)
       p
       (pj2 z)

  =transp-fib-inv : ∀ {A B} {f : A → B} → ∀ {b} → (z : fib f b) → ∀ {a} → (p : pj1 z == a)
                  → =transp (λ x → f x == b) p (pj2 z) == =ap f (p ⁻¹) • pj2 z
  =transp-fib-inv {f = f} {b} z p =
    =J (λ x u → =transp (λ xx → f xx == b) u (pj2 z) == =ap f (u ⁻¹) • pj2 z)
       (•idl (pj2 z) ⁻¹)
       p

  -------------
  -- UIP stuff
  -------------

  UIP UIPrf  : (A : Set) → Set
  UIP = isSet --{a a' : A} → is-subsing (a == a')-- (u u' : a == a') → u == u'
  UIPrf A = {a : A} (u : a == a) → u == =rf

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

  ¬¬=elim→uip : {A : Set} → ({a a' : A} → ¬ (¬ (a == a')) → a == a') → UIP A
  ¬¬=elim→uip {A} ¬¬=e = HoTT-Thm7-2-2 (λ x → ¬¬η (=rf {a = x}) )
                                       (λ x x' → ¬-is-prop (¬ (x == x')))
                                       (λ x x' → ¬¬=e {x} {x'})

  HedbergThm : {A : Set} → ((a a' : A) → (a == a') + (a == a' → N₀)) → UIP A
  HedbergThm {A} dec = ¬¬=elim→uip (λ {a} {a'} → dec→¬¬e (dec a a'))


  ----------------
  -- equivalences
  ----------------

  is-equiv : ∀ {A B} → (f : A → B) → Set
  is-equiv f = ∀ b → isContr (fib f b)

  id-is-eqv : ∀ {A} → is-equiv (id {A})
  id-is-eqv {A} a =
    (a ,, =rf)
    ,, λ z → =Σchar,, (pj2 z) (=transp-precmp-inv (pj2 z) (pj2 z) • •invl (pj2 z))

  cntr-N₁-fnc-is-eqv : {A : Set} → isContr A → (f : N₁ → A) → is-equiv f
  cntr-N₁-fnc-is-eqv {A} cntr f = λ a → (0₁ ,, isprp (f 0₁) a)
                                         ,, λ z → =Σchar,, N₁cntr (=isprp _ _)
    where isprp : isProp A
          isprp = isContr→isProp cntr
          N₁cntr : ∀ {x} → x == 0₁
          N₁cntr {x} = pj2 N₁-isContr x
          =isprp : {a a' : A} → isProp (a == a')
          =isprp = isProp→=isProp isprp

  infix 5 _≃_
  _≃_ : (A B : Set) → Set
  A ≃ B = Σ[ (A → B) ] is-equiv

  N₁≃cntr : {A : Set} → isContr A → N₁ ≃ A
  N₁≃cntr {A} cntrA = (λ _ → pj1 cntrA) ,, cntr-N₁-fnc-is-eqv cntrA _

  N₀+eqv : {A B O : Set} {f : A → B} (k : O → N₀)
              → is-equiv f → is-equiv {O + A} [ N₀ind ∘ k ∣ f ]
  N₀+eqv {A} {B} {O} {f} k eqvf b =
    (inr (g b) ,, fg=idB b) ,, eq
    where g : B → A
          g b = pj1 (pj1 (eqvf b))
          fg=idB : ∀ b → f (g b) == b
          fg=idB b = pj2 (pj1 (eqvf b))
          eq : (z : fib [ N₀ind ∘ k ∣ f ] b) → z == inr (g b) ,, fg=idB b
          eq z =
            Ση⁻¹ z
            • +ind (λ v → (u : [ N₀ind ∘ k ∣ f ] v == b)
                                         → v ,, u == inr (g b) ,, fg=idB b)
                   (λ o p → N₀ind {λ _ → _,,_ {_} {λ x → [ N₀ind ∘ k ∣ f ] x == b}
                                                (inl o) p == _}
                                   (k o))
                   (λ a p → =Σchar,, (=ap inr (=pj1 (pj2 (eqvf b) (a ,, p))))
                                      (=proof
             ((λ v → [ N₀ind ∘ k ∣ f ] v == b) ● =ap inr (=pj1 (pj2 (eqvf b) (a ,, p)))) p
                                     ==[ ●=ap-is-● (λ v → [ N₀ind ∘ k ∣ f ] v == b) inr
                                                      (=pj1 (pj2 (eqvf b) (a ,, p))) p ] /
             ((λ v → f v == b) ● =pj1 (pj2 (eqvf b) (a ,, p))) p
                              ==[ ●pj1-ptw (λ v → f v == b) (pj2 (eqvf b) (a ,, p)) p ] /
             ((λ z → f (pj1 z) == b) ● pj2 (eqvf b) (a ,, p)) p
                                                       ==[ =pj2 (pj2 (eqvf b) (a ,, p)) ]∎
             pj2 (pj1 (eqvf b)) ∎))
                   (pj1 z)
                   (pj2 z)

  +N₀eqvr : {A B O : Set} {f : A → B} (k : O → N₀)
              → is-equiv f → is-equiv {A} {O + B} (inr ∘ f)
  +N₀eqvr {A} {B} {O} {f} k eqvf (inl o) =
    N₀ind (k o)
  +N₀eqvr {A} {B} {O} {f} k eqvf (inr b) =
    (g b ,, =ap inr (fg=idB b)) ,, eq
    where g : B → A
          g b = pj1 (pj1 (eqvf b))
          fg=idB : ∀ b → f (g b) == b
          fg=idB b = pj2 (pj1 (eqvf b))
          aux : fib (inr {O} ∘ f) (inr b) → fib f b
          aux z = pj1 z ,, inr-inj (pj2 z)
          eq : (z : fib (inr {O} ∘ f) (inr b)) → z == g b ,, =ap inr (fg=idB b)
          eq z = =Σchar,, (=pj1 (pj2 (eqvf b) (aux z)))
                          (=proof
             ((λ x → inr (f x) == inr b) ● =pj1 (pj2 (eqvf b) (aux z))) (pj2 z)
                                                ==[ ●pj1-ptw (λ x → inr (f x) == inr b)
                                                             (pj2 (eqvf b) (aux z))
                                                             (pj2 z)                    ] /
             ((λ w → inr (f (pj1 w)) == inr b) ● pj2 (eqvf b) (aux z)) (pj2 z)
             ==[ =ap● {f = f ∘ pj1} {inr}
                      (pj2 (eqvf b) (aux z))
                      (pj2 (aux z) ,, inrinj=id (pj2 z)) ] /
             =ap inr (((λ w → f (pj1 w) == b) ● pj2 (eqvf b) (aux z)) (inr-inj (pj2 z)))
                                         ==[ =ap (=ap inr) (=pj2 (pj2 (eqvf b) (aux z))) ]∎
             =ap inr (fg=idB b) ∎)

  eqv-cntr-is-cntr : {A B : Set} → isContr A → {f : A → B} → is-equiv f → isContr B
  eqv-cntr-is-cntr {A} {B} cntrA {f} eqvf =
    bsB ,, cnB
    where g : B → A
          g b = pj1 (pj1 (eqvf b))
          fg=idB : ∀ b → f (g b) == b
          fg=idB b = pj2 (pj1 (eqvf b))
          bsA : A
          bsA = pj1 cntrA
          cnA : ∀ a → a == bsA
          cnA = pj2 cntrA
          bsB : B
          bsB = f bsA
          cnB : ∀ b → b == bsB
          cnB b = =proof
            b           ==[ fg=idB b ⁻¹ ] /
            f (g b)     ==[ =ap f (cnA (g b)) ]∎
            bsB ∎

  -- using ∀-is-prop
  is-equiv-is-Prop : ∀ {A B f} → isProp (is-equiv {A} {B} f)
  is-equiv-is-Prop {A} {B} {f} = ∀-is-prop (λ b → isContr (fib f b))
                                           (λ b → isContr-is-prop (fib f b))

  is-iso-pair : ∀ {A B} → (f : A → B) → (g : B → A) → Set
  is-iso-pair f g = (∀ a → g (f a) == a) × (∀ b → f (g b) == b)
  is-adj-iso-pair : ∀ {A B} → (f : A → B) → (g : B → A) → Set
  is-adj-iso-pair f g = Σ[ (∀ a → g (f a) == a) × (∀ b → f (g b) == b) ]
                           (λ ii → (∀ a → =ap f (prj1 ii a) == prj2 ii (f a))
                                    × (∀ b → =ap g (prj2 ii b) == prj1 ii (g b)) )
  is-invrt : ∀ {A B} → (f : A → B) → Set
  is-invrt {A} {B} f = Σ[ (B → A) ] (is-iso-pair f)
  is-adj-invrt : ∀ {A B} → (f : A → B) → Set
  is-adj-invrt {A} {B} f = Σ[ (B → A) ] (is-adj-iso-pair f)
  is-idfull : ∀ {A B} (f : A → B) → Set
  is-idfull f = ∀ {a a'} (p : f a == f a') → Σ[ a == a' ] (λ x → =ap f x == p)

  idfull-fib-is-prop : ∀ {A B} {f : A → B} → is-idfull f
                         → ∀ b → isProp (fib f b)
  idfull-fib-is-prop {A} {B} {f} fullf b z z' =
    =Σchar z₁=z'₁ z₂=z'₂
      where z₁=z'₁ : pj1 z == pj1 z'
            z₁=z'₁ = pj1 (fullf (pj2 z • pj2 z' ⁻¹))
            z₂=z'₂ : ((λ x → f x == b) ● z₁=z'₁) (pj2 z) == pj2 z'
            z₂=z'₂ = =proof
              ((λ x → f x == b) ● z₁=z'₁) (pj2 z)
                                               ==[ ●=ap-is-●⁻¹ (_== b) f z₁=z'₁ (pj2 z) ] /
              ((_== b) ● =ap f z₁=z'₁) (pj2 z)
                                          ==[ =transp-precmp-inv (=ap f z₁=z'₁) (pj2 z) ] /
              (=ap f z₁=z'₁) ⁻¹ • pj2 z
                ==[ •extr (pj2 z) ( •⁻¹g {p₂ = pj2 z' ⁻¹} (pj2 (fullf (pj2 z • pj2 z' ⁻¹))) )
                                                          • •ass⁻¹ _ (pj2 z ⁻¹) (pj2 z) ] /
              (pj2 z' ⁻¹) ⁻¹ • pj2 z ⁻¹ • pj2 z
                                        ==[ •idrg-inv (•invl (pj2 z)) (⁻¹⁻¹=id (pj2 z')) ]∎
              pj2 z' ∎

  =transp-is-invrt : {A : Set}(B : A → Set){a a' : A} (p : a == a')
                        → is-invrt (B ● p)
  =transp-is-invrt {A} B p =
    B ● (p ⁻¹) ,, (transp-forth-back-ptw B p , transp-back-forth-ptw B p)

  ∘is-invrt : ∀ {A B C} {f : A → B}{g : B → C}
                 → is-invrt f → is-invrt g → is-invrt (g ∘ f)
  ∘is-invrt {A} {B} {C} {f} {g} invf invg =
    (fi ∘ gi)
    ,, ((λ a → =proof
       fi (gi (g (f a)))    ==[ =ap fi (prj1 (pj2 invg) (f a)) ] /
       fi (f a)             ==[ prj1 (pj2 invf) a ]∎
       a ∎)
     , (λ c → =proof
       g (f (fi (gi c)))    ==[ =ap g (prj2 (pj2 invf) (gi c)) ] /
       g (gi c)             ==[ prj2 (pj2 invg) c ]∎
       c ∎))
    where fi : B → A
          fi = pj1 invf
          gi : C → B
          gi = pj1 invg

  inv-trn-pre : ∀ {A B C} {f : A → B} {g : B → C} {h : A → C}
              → (∀ a → g (f a) == h a) → is-invrt f → is-invrt h → is-invrt g
  inv-trn-pre {A} {B} {C} {f} {g} {h} eq invf invh =
    (f ∘ h') ,, (iddom , idcod)
    where f' : B → A
          f' = pj1 invf
          ff'=idB : ∀ b → f (f' b) == b
          ff'=idB = prj2 (pj2 invf)
          h' : C → A
          h' = pj1 invh
          h'h=idA : ∀ a → h' (h a) == a
          h'h=idA = prj1 (pj2 invh)
          hh'=idC : ∀ c → h (h' c) == c
          hh'=idC = prj2 (pj2 invh)
          iddom : ∀ b → (f ∘ h') (g b) == b
          iddom b = =proof
            (f ∘ h') (g b)            ==[ =ap (f ∘ h' ∘ g) (ff'=idB b ⁻¹) ] /
            (f ∘ h') (g (f (f' b)))   ==[ =ap (f ∘ h') (eq (f' b)) ] /
            (f ∘ h' ∘ h) (f' b)       ==[ =ap f (h'h=idA (f' b)) ] /
            f (f' b)                 ==[ ff'=idB b ]∎
            b ∎
          idcod : ∀ c → g (f (h' c)) == c
          idcod c = =proof
            g (f (h' c))            ==[ eq (h' c) ] /
            h (h' c)                ==[ hh'=idC c ]∎
            c ∎

  inv-trn-post : ∀ {A B C} {f : A → B} {g : B → C} {h : A → C}
              → (∀ a → g (f a) == h a) → is-invrt g → is-invrt h → is-invrt f
  inv-trn-post {A} {B} {C} {f} {g} {h} eq invg invh =
    (h' ∘ g) ,, (iddom , idcod)
    where g' : C → B
          g' = pj1 invg
          g'g=idB : ∀ b → g' (g b) == b
          g'g=idB = prj1 (pj2 invg)
          gg'=idC : ∀ c → g (g' c) == c
          gg'=idC = prj2 (pj2 invg)
          h' : C → A
          h' = pj1 invh
          h'h=idA : ∀ a → h' (h a) == a
          h'h=idA = prj1 (pj2 invh)
          hh'=idC : ∀ c → h (h' c) == c
          hh'=idC = prj2 (pj2 invh)
          iddom : ∀ a → (h' ∘ g) (f a) == a
          iddom a = =proof
            (h' ∘ g) (f a)         ==[ =ap h' (eq a) ] /
            h' (h a)               ==[ h'h=idA a ]∎
            a ∎
          idcod : ∀ b → f (h' (g b)) == b
          idcod b = =proof
            f (h' (g b))               ==[ g'g=idB (f (h' (g b))) ⁻¹ ] /
            (g' ∘ g) (f (h' (g b)))    ==[ =ap g' (eq (h' (g b))) ] /
            (g' ∘ h) (h' (g b))        ==[ =ap g' (hh'=idC (g b)) ] /
            g' (g b)                  ==[ g'g=idB b ]∎
            b ∎



  eqv-is-invrt : ∀ {A B} {f : A → B} → is-equiv f → is-invrt f
  eqv-is-invrt {A} {B} {f} eqvf = g ,, (gf=idA , fg=idB)
    where g : B → A
          g b = pj1 (pj1 (eqvf b))
          gf=idA : ∀ a → g (f a) == a
          gf=idA a = =pj1 ((pj2 (eqvf (f a))) (a ,, =rf)) ⁻¹
          fg=idB : ∀ b → f (g b) == b
          fg=idB b = pj2 (pj1 (eqvf b))

  +N₀invrtr : {A B O : Set} {f : A → B} (k : O → N₀)
              → is-invrt f → is-invrt {A} {O + B} (inr ∘ f)
  +N₀invrtr {A} {B} {O} {f} k invf =
    [ N₀ind ∘ k ∣ g ]
    ,, (gf=idA
    , +ind (λ v → (inr ∘ f) ([ N₀ind ∘ k ∣ pj1 invf ] v) == v)
           (λ o → N₀ind {λ _ →  inr (f (N₀ind (k o))) == inl o} (k o))
           λ b → =ap inr (fg=idB b))
    where g : B → A
          g = pj1 invf
          gf=idA : ∀ a → g (f a) == a
          gf=idA = prj1 (pj2 invf)
          fg=idB : ∀ b → f (g b) == b
          fg=idB = prj2 (pj2 invf)
          

  -- every invertible function is adjoint-invertible
  iso-pair-is-adj : ∀ {A B} {f : A → B}{g : B → A}
                         → is-iso-pair f g → is-adj-iso-pair f g
  iso-pair-is-adj {A} {B} {f} {g} isiso = ((gf=idA , fg=idB-adj) ,, (eq1 , eq2))
    where
      gf=idA : ∀ a → g (f a) == a
      gf=idA = prj1 isiso
      fg=idB : ∀ b → f (g b) == b
      fg=idB = prj2 isiso
      fg=idB-adj : ∀ b → f (g b) == b
      fg=idB-adj b = =proof -- fg=idB (f (g b)) ⁻¹ • =ap f (gf=idA (g b)) • fg=idB b
        f (g b)            ==[ fg=idB (f (g b)) ⁻¹ ] /
        f (g (f (g b)))    ==[ =ap f (gf=idA (g b)) ] /
        f (g b)            ==[ fg=idB b ]∎
        b ∎
      gf-aux₁ : ∀ a → =ap (g ∘ f) (gf=idA a) • gf=idA a == gf=idA (g (f a)) • gf=idA a
      gf-aux₁ a = ==-is-nat-id gf=idA (gf=idA a)
      fg-aux₁ : ∀ b → =ap (f ∘ g) (fg=idB b) • fg=idB b == fg=idB (f (g b)) • fg=idB b
      fg-aux₁ b = ==-is-nat-id fg=idB (fg=idB b)
      gf-aux₂ : ∀ a → =ap (g ∘ f) (gf=idA a) == gf=idA (g (f a))
      gf-aux₂ a = =proof
        =ap (g ∘ f) (gf=idA a)                             ==[ •idrg-inv (•invr (gf=idA a)) =rf ⁻¹ ] /
        =ap (g ∘ f) (gf=idA a) • gf=idA a • gf=idA a ⁻¹    ==[ •ass _ (gf=idA a) (gf=idA a ⁻¹)
                                                            • •extr (gf=idA a ⁻¹) (gf-aux₁ a)
                                                            • •ass⁻¹ _ (gf=idA a) (gf=idA a ⁻¹) ] /
        gf=idA (g (f a)) • gf=idA a • gf=idA a ⁻¹          ==[ •idrg-inv (•invr (gf=idA a)) =rf ]∎
        gf=idA (g (f a)) ∎
      fg-aux₂ : ∀ b → =ap (f ∘ g) (fg=idB b) == fg=idB (f (g b))
      fg-aux₂ b = =proof
        =ap (f ∘ g) (fg=idB b)                             ==[ •idrg-inv (•invr (fg=idB b)) =rf ⁻¹ ] /
        =ap (f ∘ g) (fg=idB b) • fg=idB b • fg=idB b ⁻¹    ==[ •ass _ (fg=idB b) (fg=idB b ⁻¹)
                                                            • •extr (fg=idB b ⁻¹) (fg-aux₁ b)
                                                            • •ass⁻¹ _ (fg=idB b) (fg=idB b ⁻¹) ] /
        fg=idB (f (g b)) • fg=idB b • fg=idB b ⁻¹          ==[ •idrg-inv (•invr (fg=idB b)) =rf ]∎
        fg=idB (f (g b)) ∎

      eq1-aux1 : ∀ a → fg=idB (f (g (f a))) • =ap f (gf=idA a) == =ap f (gf=idA (g (f a))) • fg=idB (f a)
      eq1-aux1 a = =proof
        fg=idB (f (g (f a))) • =ap f (gf=idA a)      ==[ ==-is-nat-id fg=idB (=ap f (gf=idA a)) ⁻¹  ] /
        =ap (f ∘ g) (=ap f (gf=idA a)) • fg=idB (f a)   ==[ •extr (fg=idB (f a))
                                                                  (=ap∘ f (f ∘ g) (gf=idA a)
                                                                    • =ap∘⁻¹ (g ∘ f) f (gf=idA a)) ] /
        =ap f (=ap (g ∘ f) (gf=idA a)) • fg=idB (f a)   ==[ •extr (fg=idB (f a))
                                                                  (=ap (=ap f) (gf-aux₂ a)) ]∎
        =ap f (gf=idA (g (f a))) • fg=idB (f a) ∎
      eq1 : (a : A) → =ap f (gf=idA a) == fg=idB-adj (f a)
      eq1 a = =proof
        =ap f (gf=idA a) ==[ •idlg-inv (•invl (fg=idB (f (g (f a))))) =rf ⁻¹
                           • •ass⁻¹ (fg=idB (f (g (f a))) ⁻¹)
                                    (fg=idB (f (g (f a)))) (=ap f (gf=idA a)) ] /
        fg=idB (f (g (f a))) ⁻¹ • fg=idB (f (g (f a))) • =ap f (gf=idA a)
                         ==[ •extl (fg=idB (f (g (f a))) ⁻¹) (eq1-aux1 a)  ]∎
        fg=idB-adj (f a) ∎

      eq2-aux₁ : ∀ a →  =ap g (=ap f (gf=idA a)) == gf=idA (g (f a))
      eq2-aux₁ a = =proof
        =ap g (=ap f (gf=idA a))    ==[ =ap∘ f g (gf=idA a) ] /
        =ap (g ∘ f) (gf=idA a)      ==[ gf-aux₂ a ]∎
        gf=idA (g (f a)) ∎
      eq2-aux₂ : ∀ b → =ap (g ∘ f) (=ap g (fg=idB b)) == =ap g (fg=idB (f (g b)))
      eq2-aux₂ b = =proof
        =ap (g ∘ f) (=ap g (fg=idB b))      ==[ =ap∘ g (g ∘ f) (fg=idB b)
                                            • =ap∘⁻¹ (f ∘ g) g (fg=idB b) ] /
        =ap g (=ap (f ∘ g) (fg=idB b))      ==[ =ap (=ap g) (fg-aux₂ b) ]∎
        =ap g (fg=idB (f (g b))) ∎
      eq2-aux₃ : ∀ b → =ap g (=ap f (gf=idA (g b)) • fg=idB b) == =ap g (fg=idB (f (g b))) • gf=idA (g b)
      eq2-aux₃ b = =proof
        =ap g (=ap f (gf=idA (g b)) • fg=idB b)         ==[ =ap• g (=ap f (gf=idA (g b)))
                                                                 (fg=idB b) ] /
        =ap g (=ap f (gf=idA (g b))) • =ap g (fg=idB b) ==[ •extr (=ap g (fg=idB b))
                                                                  (eq2-aux₁ (g b)) ] /
        gf=idA (g (f (g b))) • =ap g (fg=idB b)         ==[ ==-is-nat-id gf=idA
                                                                      (=ap g (fg=idB b)) ⁻¹ ] /
        =ap (g ∘ f) (=ap g (fg=idB b)) • gf=idA (g b)   ==[ •extr (gf=idA (g b)) (eq2-aux₂ b) ]∎
        =ap g (fg=idB (f (g b))) • gf=idA (g b) ∎
      eq2 : (b : B) → =ap g (fg=idB-adj b) == gf=idA (g b)
      eq2 b = =proof
        =ap g (fg=idB-adj b)
              ==[ =ap• g (fg=idB (f (g b)) ⁻¹) (=ap f (gf=idA (g b)) • fg=idB b)
                • •extr (=ap g (=ap f (gf=idA (g b)) • fg=idB b)) (=ap-sym g (fg=idB (f (g b)))) ] /
        =ap g (fg=idB (f (g b))) ⁻¹ • =ap g (=ap f (gf=idA (g b)) • fg=idB b)
              ==[ •extl (=ap g (fg=idB (f (g b))) ⁻¹) (eq2-aux₃ b) ] /
        =ap g (fg=idB (f (g b))) ⁻¹ • =ap g (fg=idB (f (g b))) • gf=idA (g b)
              ==[ •ass (=ap g (fg=idB (f (g b))) ⁻¹) (=ap g (fg=idB (f (g b)))) (gf=idA (g b))
                • •idlg-inv (•invl (=ap g (fg=idB (f (g b))))) =rf ]∎
        gf=idA (g b) ∎

  invrt-is-adj : ∀ {A B} {f : A → B} → is-invrt f → is-adj-invrt f
  invrt-is-adj inv = pj1 inv ,, iso-pair-is-adj (pj2 inv)


  -- every adjoint-invertible map is full on identities
  adj-invrt-is-full : ∀ {A B} {f : A → B} → is-adj-invrt f → is-idfull f
  adj-invrt-is-full {A} {B} {f} adjinv {a} {a'} p =
    eqA ,, (=proof
    =ap f eqA            ==[ =ap• f (gf=idA a ⁻¹) (=ap g p • gf=idA a')  ] /
    =ap f (gf=idA a ⁻¹) • =ap f (=ap g p • gf=idA a') ==[ •extlr (=ap-sym f (gf=idA a))
                                                                 (=ap• f (=ap g p) (gf=idA a'))  ] /
    =ap f (gf=idA a) ⁻¹ • =ap f (=ap g p) • =ap f (gf=idA a') ==[ •extl (=ap f (gf=idA a) ⁻¹) eqp ] /
    =ap f (gf=idA a) ⁻¹ • =ap f (gf=idA a) • p ==[  •ass _ (=ap f (gf=idA a)) p
                                                 • •idlg-inv (•invl (=ap f (gf=idA a))) =rf ]∎
    p ∎)
    where
      g : B → A
      g = pj1 adjinv
      gf=idA : ∀ a → g (f a) == a
      gf=idA = prj1 (pj1 (pj2 adjinv))
      fg=idB : ∀ b → f (g b) == b
      fg=idB = prj2 (pj1 (pj2 adjinv))
      tr1 : ∀ x → =ap f (gf=idA x) == fg=idB (f x)
      tr1 = prj1 (pj2 (pj2 adjinv))
      tr2 : ∀ b → =ap g (fg=idB b) == gf=idA (g b)
      tr2 = prj2 (pj2 (pj2 adjinv))
      eqA : a == a'
      eqA = =proof
        a               ==[ gf=idA a ⁻¹ ] /
        g (f a)         ==[ =ap g p ] /
        g (f a')        ==[ gf=idA a' ]∎
        a' ∎
      eqp : =ap f (=ap g p) • =ap f (gf=idA a') == =ap f (gf=idA a) • p
      eqp = =proof
        =ap f (=ap g p) • =ap f (gf=idA a')    ==[ •extlr (=ap∘ g f p) (tr1 a') ] /
        =ap (f ∘ g) p • fg=idB (f a')          ==[ ==-is-nat-id fg=idB p ] /
        fg=idB (f a) • p                      ==[ •extr p (tr1 a ⁻¹) ]∎
        =ap f (gf=idA a) • p ∎

  -- it follows that every invertible map is full on identities too
  invrt-is-full : ∀ {A B} {f : A → B} → is-invrt f → is-idfull f
  invrt-is-full {A} {B} {f} inv = adj-invrt-is-full (invrt-is-adj inv)

  -- and that every adjoint-invertible map is an equivalence
  adj-invrt-is-eqv : ∀ {A B} {f : A → B} → is-adj-invrt f → is-equiv f
  adj-invrt-is-eqv {A} {B} {f} adjinv b =
    (g b ,, fg=idB b)
    ,, snd
    where g : B → A
          g = pj1 adjinv
          gf=idA : ∀ x → g (f x) == x
          gf=idA = prj1 (pj1 (pj2 adjinv))
          fg=idB : ∀ y → f (g y) == y
          fg=idB = prj2 (pj1 (pj2 adjinv))
          tr1 : ∀ x → =ap f (gf=idA x) == fg=idB (f x)
          tr1 = prj1 (pj2 (pj2 adjinv))
          tr2 : ∀ y → =ap g (fg=idB y) == gf=idA (g y)
          tr2 = prj2 (pj2 (pj2 adjinv))
          fbase : (z : fib f b) → f (pj1 z) == f (g b)
          fbase z = =proof
            f (pj1 z)      ==[ pj2 z ] /
            b              ==[ fg=idB b ⁻¹ ]∎
            f (g b) ∎
          base : (z : fib f b) → pj1 z == g b
          base z = pj1 (adj-invrt-is-full adjinv (fbase z))
          fbase-eq : (z : fib f b) → =ap f (base z) == fbase z
          fbase-eq z = pj2 (adj-invrt-is-full adjinv (fbase z))
          aux : (z : fib f b) → =ap f (base z ⁻¹) == (fg=idB b ⁻¹) ⁻¹ • pj2 z ⁻¹
          aux z = =proof
            =ap f (base z ⁻¹)                ==[ ⁻¹=ap f (base z) ] /
            =ap f (base z) ⁻¹                ==[ =ap _⁻¹ (fbase-eq z) ] /
            (pj2 z • fg=idB b ⁻¹) ⁻¹         ==[ •⁻¹ (pj2 z) (fg=idB b ⁻¹) ]∎
            (fg=idB b ⁻¹) ⁻¹ • pj2 z ⁻¹ ∎
          snd : (z : fib f b) → z == g b ,, fg=idB b
          snd z = =Σchar,, (base z) (=proof
            ((λ x → f x == b) ● base z) (pj2 z)    ==[ =transp-fib-inv z (base z) ] /
            =ap f (base z ⁻¹) • pj2 z               ==[ •extr (pj2 z) (aux z)
                                                      • •ass⁻¹ _ (pj2 z ⁻¹) (pj2 z) ] /
            (fg=idB b ⁻¹) ⁻¹ • pj2 z ⁻¹ • pj2 z      ==[ •idrg-inv (•invl (pj2 z))
                                                                  (⁻¹⁻¹=id (fg=idB b)) ]∎
            fg=idB b ∎)

  invrt-is-eqv : ∀ {A B} {f : A → B} → is-invrt f → is-equiv f
  invrt-is-eqv {A} {B} {f} inv = adj-invrt-is-eqv (invrt-is-adj inv)

  ∘eqv : {A B C : Set}{f : A → B}{g : B → C}
             → is-equiv f → is-equiv g → is-equiv (g ∘ f)
  ∘eqv {A} {B} {C} {f} {g} eqvf eqvg = invrt-is-eqv (∘is-invrt invf invg)
    where invf : is-invrt f
          invf = eqv-is-invrt eqvf
          invg : is-invrt g
          invg = eqv-is-invrt eqvg

  prop-eqv : ∀ {A B} (f : A → B) → isProp A → isProp B → (B → A)
               → is-equiv f
  prop-eqv {A} {B} f prpA prpB g = invrt-is-eqv (g ,, ((λ a → prpA _ _) , (λ b → prpB _ _)))

  ≃trns : ∀ {A B C} → A ≃ B → B ≃ C → A ≃ C
  ≃trns {A} {B} {C} eqv1 eqv2 = (pj1 eqv2 ∘ pj1 eqv1) ,, ∘eqv (pj2 eqv1) (pj2 eqv2)  
  ≃sym : ∀ {A B} → A ≃ B → B ≃ A
  ≃sym {A} {B} eqv = g ,, invrt-is-eqv (f ,, ((fg=idB , gf=idA)))
    where f : A → B
          f = pj1 eqv
          inv : is-invrt f
          inv = eqv-is-invrt (pj2 eqv)
          g : B → A
          g = pj1 inv
          gf=idA : ∀ a → g (f a) == a
          gf=idA = prj1 (pj2 inv)
          fg=idB : ∀ b → f (g b) == b
          fg=idB = prj2 (pj2 inv)

  =ptw→fib-eqv : ∀ {A B} {f g : A → B} → (∀ a → f a == g a)
                → ∀ b → fib f b ≃ fib g b
  =ptw→fib-eqv {A} {B} {f} {g} eq b = ·eq ,, invrt-is-eqv (eq· ,, (iddom , idcod))
    where ·eq : fib f b → fib g b
          ·eq z = (pj1 z) ,, eq (pj1 z) ⁻¹ • pj2 z
          eq· : fib g b → fib f b
          eq· z = (pj1 z) ,, eq (pj1 z) • pj2 z
          iddom : ∀ z → eq· (·eq z) == z
          iddom z = =Σover (•ass (eq (pj1 z)) _ (pj2 z)
                            • •idlg-inv (•invr (eq (pj1 z))) =rf)
          idcod : ∀ z → ·eq (eq· z) == z
          idcod z = =Σover (•ass _ (eq (pj1 z)) (pj2 z)
                            • •idlg-inv (•invl (eq (pj1 z))) =rf)

  =ptw-eqv-is-eqv : ∀ {A B f g} → is-equiv {A} {B} f → (∀ x → f x == g x) → is-equiv g
  =ptw-eqv-is-eqv {A} {B} {f} {g} eqvf eq b =
    eqv-cntr-is-cntr {fib f b} (eqvf b) (pj2 (=ptw→fib-eqv eq b))

  -- sums of equivalences are equivalences
  
  +fib-inl : {A₁ A₂ B₁ B₂ : Set} (f₁ : A₁ → B₁) (f₂ : A₂ → B₂)
                 → ∀ b₁ → fib [ inl ∘ f₁ ∣ inr ∘ f₂ ] (inl b₁) ≃ fib f₁ b₁
  +fib-inl {A₁} {A₂} {B₁} {B₂} f₁ f₂ b₁ = f ,, invrt-is-eqv (g ,, (gf=id , fg=id))
    where g : fib f₁ b₁ → fib [ inl ∘ f₁ ∣ inr ∘ f₂ ] (inl b₁)
          g = ⟨ inl ∘ pj1 ∣∣ (λ z → =ap inl (pj2 z)) ⟩
          f : fib [ inl ∘ f₁ ∣ inr ∘ f₂ ] (inl b₁) → fib f₁ b₁
          f z = +ind (λ v → [ inl ∘ f₁ ∣ inr ∘ f₂ ] v == inl b₁ → fib f₁ b₁)
                     (λ a eq → a ,, inl-inj eq)
                     (λ _ eq → N₀ind (inr≠inl eq))
                     (pj1 z)
                     (pj2 z)
          gf=id : ∀ z → g (f z) == z
          gf=id z = +ind (λ v → (eq : [ inl ∘ f₁ ∣ inr ∘ f₂ ] v == inl b₁) → g (f (v ,, eq)) == (v ,, eq))
                         (λ _ eq → =Σover (inlinj=id eq))
                         (λ b eq → N₀ind {λ _ → g (f (inr b ,, eq)) == _} (inr≠inl eq))
                         (pj1 z)
                         (pj2 z)
                    • Ση z
          fg=id : ∀ z → f (g z) == z
          fg=id z = =Σover (injinl=id (pj2 z))

  +fib-inr : {A₁ A₂ B₁ B₂ : Set} (f₁ : A₁ → B₁) (f₂ : A₂ → B₂)
                 → ∀ b₂ → fib [ inl ∘ f₁ ∣ inr ∘ f₂ ] (inr b₂) ≃ fib f₂ b₂
  +fib-inr {A₁} {A₂} {B₁} {B₂} f₁ f₂ b₂ = f ,, invrt-is-eqv (g ,, (gf=id , fg=id))
    where f : fib [ inl ∘ f₁ ∣ inr ∘ f₂ ] (inr b₂) → fib f₂ b₂
          f z = +ind (λ v → [ inl ∘ f₁ ∣ inr ∘ f₂ ] v == inr b₂ → fib f₂ b₂)
                     (λ _ eq → N₀ind (inl≠inr eq))
                     (λ b eq → b ,, inr-inj eq)
                     (pj1 z)
                     (pj2 z)
          g : fib f₂ b₂ → fib [ inl ∘ f₁ ∣ inr ∘ f₂ ] (inr b₂)
          g = ⟨ inr ∘ pj1 ∣∣ (λ z → =ap inr (pj2 z)) ⟩
          gf=id : ∀ z → g (f z) == z
          gf=id z = +ind (λ v → (eq : [ inl ∘ f₁ ∣ inr ∘ f₂ ] v == inr b₂) → g (f (v ,, eq)) == (v ,, eq))
                         (λ b eq → N₀ind {λ _ → g (f (inl b ,, eq)) == _} (inl≠inr eq))
                         (λ _ eq → =Σover (inrinj=id eq))
                         (pj1 z)
                         (pj2 z)
                    • Ση z
          fg=id : ∀ z → f (g z) == z
          fg=id z = =Σover (injinr=id (pj2 z))

  +eqv : {A₁ A₂ B₁ B₂ : Set} {f₁ : A₁ → B₁} {f₂ : A₂ → B₂}
              → is-equiv f₁ → is-equiv f₂ → is-equiv [ inl ∘ f₁ ∣ inr ∘ f₂ ]
  +eqv {A₁} {A₂} {B₁} {B₂} {f₁} {f₂} eqv₁ eqv₂ =
    +ind (λ v → isContr (fib [ inl ∘ f₁ ∣ inr ∘ f₂ ] v))
         (λ b₁ → eqv-cntr-is-cntr (eqv₁ b₁) (pj2 (≃sym (+fib-inl f₁ f₂ b₁))))
         (λ b₂ → eqv-cntr-is-cntr (eqv₂ b₂) (pj2 (≃sym (+fib-inr f₁ f₂ b₂))))


  +fib3-inl : {A₁ A₂ A₃ B₁ B₂ B₃ : Set} (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) (f₃ : A₃ → B₃)
                   →  ∀ b₁ → fib [ inl ∘ f₁ ∥ inrl ∘ f₂ ∥ inrr ∘ f₃ ] (inl b₁) ≃ fib f₁ b₁
  +fib3-inl {A₁} {A₂} {A₃} {B₁} {B₂} {B₃} f₁ f₂ f₃ b₁ =
    ≃trns (=ptw→fib-eqv (+rec3-dist f₁ f₂ f₃) (inl b₁))
          (+fib-inl f₁ [ inl ∘ f₂ ∣ inr ∘ f₃ ] b₁)

  +fib3-inrl : {A₁ A₂ A₃ B₁ B₂ B₃ : Set} (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) (f₃ : A₃ → B₃)
                   →  ∀ b₂ → fib [ inl ∘ f₁ ∥ inrl ∘ f₂ ∥ inrr ∘ f₃ ] (inrl b₂) ≃ fib f₂ b₂
  +fib3-inrl {A₁} {A₂} {A₃} {B₁} {B₂} {B₃} f₁ f₂ f₃ b₂ =
    (pj1 eqv2 ∘ pj1 eqv1) ,, ∘eqv (pj2 eqv1) (pj2 eqv2)
    where eqv1 : fib [ inl ∘ f₁ ∥ inrl ∘ f₂ ∥ inrr ∘ f₃ ] (inrl b₂)
                    ≃ fib [ inl ∘ f₂ ∣ inr ∘ f₃ ] (inl b₂)
          eqv1 = ≃trns (=ptw→fib-eqv (+rec3-dist f₁ f₂ f₃) (inr (inl b₂)))
                       (+fib-inr f₁ [ inl ∘ f₂ ∣ inr ∘ f₃ ] (inl b₂))
          eqv2 : fib [ inl ∘ f₂ ∣ inr ∘ f₃ ] (inl b₂) ≃ fib f₂ b₂
          eqv2 = +fib-inl f₂ f₃ b₂

  +fib3-inrr : {A₁ A₂ A₃ B₁ B₂ B₃ : Set} (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) (f₃ : A₃ → B₃)
                   →  ∀ b₃ → fib [ inl ∘ f₁ ∥ inrl ∘ f₂ ∥ inrr ∘ f₃ ] (inrr b₃) ≃ fib f₃ b₃
  +fib3-inrr {A₁} {A₂} {A₃} {B₁} {B₂} {B₃} f₁ f₂ f₃ b₃ =
    (pj1 eqv2 ∘ pj1 eqv1) ,, ∘eqv (pj2 eqv1) (pj2 eqv2)
    where eqv1 : fib [ inl ∘ f₁ ∥ inrl ∘ f₂ ∥ inrr ∘ f₃ ] (inrr b₃)
                    ≃ fib [ inl ∘ f₂ ∣ inr ∘ f₃ ] (inr b₃)
          eqv1 = ≃trns (=ptw→fib-eqv (+rec3-dist f₁ f₂ f₃) (inr (inr b₃)))
                       (+fib-inr f₁ [ inl ∘ f₂ ∣ inr ∘ f₃ ] (inr b₃))
          eqv2 : fib [ inl ∘ f₂ ∣ inr ∘ f₃ ] (inr b₃) ≃ fib f₃ b₃
          eqv2 = +fib-inr f₂ f₃ b₃

  +eqv3 : {A₁ A₂ A₃ B₁ B₂ B₃ : Set} {f₁ : A₁ → B₁} {f₂ : A₂ → B₂} {f₃ : A₃ → B₃}
              → is-equiv f₁ → is-equiv f₂ → is-equiv f₃
                → is-equiv [ inl ∘ f₁ ∥ inrl ∘ f₂ ∥ inrr ∘ f₃ ]
  +eqv3 {A₁} {A₂} {A₃} {B₁} {B₂} {B₃} {f₁} {f₂} {f₃} eqv₁ eqv₂ eqv₃ =
    +ind3 (λ v → isContr (fib [ inl ∘ f₁ ∥ inrl ∘ f₂ ∥ inrr ∘ f₃ ] v))
          (λ b₁ → eqv-cntr-is-cntr (eqv₁ b₁) (pj2 (≃sym (+fib3-inl f₁ f₂ f₃ b₁))))
          (λ b₂ → eqv-cntr-is-cntr (eqv₂ b₂) (pj2 (≃sym (+fib3-inrl f₁ f₂ f₃ b₂))))
          (λ b₃ → eqv-cntr-is-cntr (eqv₃ b₃) (pj2 (≃sym (+fib3-inrr f₁ f₂ f₃ b₃))))

-- end of file
