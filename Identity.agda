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
  =ap-id : {A : Set} {a a' : A} (p : a == a') → =ap id p == p
  =ap-id = =J (λ _ u → =ap id u == u) =rf
  =ap-cnst : {A B : Set}(b : B) {a a' : A} (p : a == a') → =ap (λ _ → b) p == =rf
  =ap-cnst b = =J (λ _ u → =ap (λ _ → b) u == =rf) =rf

  =transp : {A : Set}(B : A → Set){a a' : A} → a == a' → B a → B a'
  =transp B {a} = =J (λ x _ → B a → B x) id
  =transp₂ : {A B : Set}(C : A → B → Set){a a' : A}{b b' : B}
                → a == a' → b == b' → C a b → C a' b'
  =transp₂ C {a} {a'} {b} {b'} p q = =transp (C a') q ∘ =transp (λ x → C x b) p
  infix 40 _●_
  _●_ : {A : Set}(B : A → Set) {a a' : A} → a == a' → B a → B a'
  B ● p = =transp B p

  =ap₂ : {A₁ A₂ B : Set}(f : A₁ → A₂ → B){a₁ a₁' : A₁}{a₂ a₂' : A₂}
             → a₁ == a₁' → a₂ == a₂' → f a₁ a₂ == f a₁' a₂'
  =ap₂ f {a₁} {a₁'} {a₂} {a₂'} p₁ =
    =transp (λ x → a₂ == a₂' → f a₁ a₂ == f x a₂') p₁ (=ap (f a₁))

  =ap₂∘₁ : ∀ {A B₁ B₂ C} (f₁ : A → B₁) (f₂ : A → B₂) (g : B₁ → B₂ → C)
           {a₁ a₂} (p : a₁ == a₂)
             → =ap₂ g (=ap f₁ p) (=ap f₂ p) == =ap (λ x → g (f₁ x) (f₂ x)) p
  =ap₂∘₁ f₁ f₂ g =
    =J (λ _ u → =ap₂ g (=ap f₁ u) (=ap f₂ u) == =ap (λ x → g (f₁ x) (f₂ x)) u)
       =rf

  =ap₂∘ : ∀ {A₁ A₂ B₁ B₂ C} (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) (g : B₁ → B₂ → C)
           {a₁ a₁'} {a₂ a₂'} (p₁ : a₁ == a₁') (p₂ : a₂ == a₂')
             → =ap₂ g (=ap f₁ p₁) (=ap f₂ p₂) == =ap₂ (λ x₁ x₂ → g (f₁ x₁) (f₂ x₂)) p₁ p₂
  =ap₂∘ f₁ f₂ g {a₁} {a₁'} {a₂} {a₂'} =
    =J ( λ x u → (p₂ : a₂ == a₂')
          → =ap₂ g (=ap f₁ u) (=ap f₂ p₂) == =ap₂ (λ x₁ x₂ → g (f₁ x₁) (f₂ x₂)) u p₂ )
       (=ap∘ f₂ (g _))

  =ap∘=ap₂ : ∀ {A₁ A₂ B C} (f : A₁ → A₂ → B) (g : B → C)
             {a₁ a₁'} {a₂ a₂'} (p₁ : a₁ == a₁') (p₂ : a₂ == a₂')
             → =ap g (=ap₂ f p₁ p₂) == =ap₂ (λ x₁ x₂ → g (f x₁ x₂)) p₁ p₂
  =ap∘=ap₂ f g {a₁} {a₁'} {a₂} {a₂'} =
    =J (λ _ u → (p₂ : a₂ == a₂')
                    → =ap g (=ap₂ f u p₂) == =ap₂ (λ x₁ x₂ → g (f x₁ x₂)) u p₂)
       (=ap∘ (f _) g)

  =ap₂-prj1 : ∀ {A₁ A₂} {a₁ a₁' : A₁} {a₂ a₂' : A₂} (p₁ : a₁ == a₁') (p₂ : a₂ == a₂')
                  → =ap₂ (λ x _ → x) p₁ p₂ == p₁
  =ap₂-prj1 {a₁ = a₁} {a₁'} {a₂} {a₂'} =
    =J (λ _ u → (p₂ : a₂ == a₂') → =ap₂ (λ x _ → x) u p₂ == u)
       (=ap-cnst a₁)

  =ap₂-prj2 : ∀ {A₁ A₂} {a₁ a₁' : A₁} {a₂ a₂' : A₂} (p₁ : a₁ == a₁') (p₂ : a₂ == a₂')
                  → =ap₂ (λ _ x → x) p₁ p₂ == p₂
  =ap₂-prj2 {a₁ = a₁} {a₁'} {a₂} {a₂'} =
    =J (λ _ u → (p₂ : a₂ == a₂') → =ap₂ (λ _ x → x) u p₂ == p₂)
       =ap-id


  infix 3 IdOver
  IdOver : ∀ {A} (B : A → Set) {a a'} (p : a == a')
             → B a → B a' → Set
  IdOver B p b b' = (B ● p) b == b'
  syntax IdOver B p b b' = b ==/ b' [ B / p ]
  =/ext : {A : Set} {B : A → Set} {a₁ a₂ : A} {p p' : a₁ == a₂}
             → p == p' → ∀ {b₁ b₂} → b₁ ==/ b₂ [ B / p ] → b₁ ==/ b₂ [ B / p' ]
  =/ext {A} {B} eq {b₁} {b₂} = (λ u → b₁ ==/ b₂ [ B / u ]) ● eq

  =transp₂v : {A : Set} {B : A → Set} (C : ∀ x → B x → Set) → ∀ {a a'} (p : a == a')
                → ∀ b → C a b → C a' ((B ● p) b)
  =transp₂v {A} {B} C {a} = =J (λ x u → ∀ y → C a y → C x ((B ● u) y)) (λ _ → id)

  =transp₂d : {A : Set} {B : A → Set} (C : ∀ x → B x → Set) → ∀ {a a'} (p : a == a')
                → ∀ {b b'} → b ==/ b' [ B / p ] → C a b → C a' b'
  =transp₂d {A} {B} C {a} {a'} p {b} pp = =transp (C a') pp ∘ =transp₂v C p b

  =apd : {A : Set}{B : A → Set}(f : (a : A) → B a){a a' : A}(p : a == a')
            → f a ==/ f a' [ B / p ]
  =apd f p = =J (λ x p → (_ ● p) (f _) == f x) =rf p

  =sym : {A : Set}{a a' : A} → a == a' → a' == a
  =sym p = ((λ x → x == _) ● p) =rf
  =tra : {A : Set}{a₁ a₂ a₃ : A} → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
  =tra p q = ((λ x → _ == x) ● q) p
  infix 60 _⁻¹
  _⁻¹ : {A : Set}{a a' : A} → a == a' → a' == a
  p ⁻¹ = =sym p
  infixr 50 _•_
  _•_ : {A : Set}{a₁ a₂ a₃ : A} → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
  p • q = =tra p q

  =ptw : {A B : Set}{f g : A → B} → f == g → (a : A) → f a == g a
  =ptw p a = =ap (λ x → x a) p
  =ptwg : {A B : Set}{f g : A → B} → f == g → ∀ {a a'} → a == a' → f a == g a'
  =ptwg {g = g} p {a} a=a' = =ptw p a • =ap g a=a'

  =ptwd : {A : Set}{B : A → Set}{f g : (a : A) → B a} → f == g → (a : A) → f a == g a
  =ptwd {f = f} p a = ((λ x → f a == x a) ● p) =rf
  =ptwdg : {A : Set}{B : A → Set}{f g : (a : A) → B a} → f == g
              → ∀ {a a'} → (eq : a == a') → (B ● eq) (f a) == g a'
  =ptwdg {f = f} {g} p eq = =apd f eq • =ptwd p _

  =transpcnst : {A : Set}(B : Set){a a' : A}(p : a == a')(b : B) → ((λ _ → B) ● p) b == b
  =transpcnst B p b = =J (λ x q → ( ((λ _ → B) ● q) b == b )) =rf p

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

  infixr 2 /_==[_]_
  infixr 1 =proof_==[_]_

  =proof_==[_]_ : {A : Set}(a₁ {a₂ a₃} : A) → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
  =proof a ==[ pf ] pf' = =tra pf pf'

  /_==[_]_ : {A : Set}(a₁ {a₂ a₃} : A) → a₁ == a₂ → a₂ == a₃ → a₁ == a₃
  / a₁ ==[ pf ] pf' = =tra pf pf'

  =eqreasend =eqreasend' : {A : Set}(a₁ a₂ : A) → a₁ == a₂ → a₁ == a₂
  =eqreasend _ _ pf = pf
  =eqreasend' _ _ pf = pf

  syntax =eqreasend a b pf = / a ==[ pf ]∎ b ∎
  syntax =eqreasend' a b pf = a ==[ pf ] b

  -- =ap and inverses and concatenations
  
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


  •lc : {A : Set}{a₁ a₂ a₃ : A}{p : a₁ == a₂}{p₁ p₂ : a₂ == a₃}
            → p • p₁ == p • p₂ → p₁ == p₂
  •lc {p = p} {p₁} {p₂} h = =proof p₁               ==[ (•idl p₁ ⁻¹ • •extr p₁ (•invl p ⁻¹)) • •ass⁻¹ _ _ p₁ ] /
                                   p ⁻¹ • p • p₁    ==[ •extl (p ⁻¹) h ] /
                                   p ⁻¹ • p • p₂    ==[ •ass _ _ p₂ • •extr p₂ (•invl p) • •idl p₂ ]∎
                                   p₂ ∎

  •rc : {A : Set}{a₁ a₂ a₃ : A}{p : a₂ == a₃}{p₁ p₂ : a₁ == a₂}
            → p₁ • p == p₂ • p → p₁ == p₂
  •rc {p = p} {p₁} {p₂} h = =proof p₁               ==[ •idr p₁ ⁻¹ • •extl p₁ (•invr p ⁻¹) ] /
                                   p₁ • p • p ⁻¹    ==[ •ass _ _ (p ⁻¹)  • •extr (p ⁻¹) h • •ass⁻¹ _ _ (p ⁻¹)  ] /
                                   p₂ • p • p ⁻¹    ==[ •extl p₂ (•invr p) • •idr p₂ ]∎
                                   p₂ ∎

  =transp-is-nat : {A A' : Set}{B : A → Set}{B' : A' → Set}{f : A → A'}
                   (g : ∀ {x} → B x → B' (f x)) {a a' : A} (p : a == a')
                     → ∀ b → =transp (B' ∘' f) p (g b) == g (=transp B p b)
  =transp-is-nat {A} {A'} {B} {B'} {f} g p =
    =J (λ _ u → ∀ y → =transp (B' ∘' f) u (g y) == g (=transp B u y))
       (λ _ → =rf)
       p
  =transp-is-nat⁻¹ : {A A' : Set}{B : A → Set}{B' : A' → Set}{f : A → A'}
                   (g : ∀ {x} → B x → B' (f x)) {a a' : A} (p : a == a')
                     → ∀ b → g (=transp B p b) == =transp (B' ∘' f) p (g b)
  =transp-is-nat⁻¹ {B' = B'} {f} g p b = =transp-is-nat {B' = B'} {f} g p b ⁻¹

  ==-is-nat : {A B : Set}{f g : A → B} → (h : ∀ a → f a == g a)
                 → ∀ {a} {a'} (p : a == a') → =ap f p • h a' == h a • =ap g p
  ==-is-nat h =rf = •idl (h _)

  ==-is-nat-id : {A : Set}{f : A → A} → (h : ∀ a → f a == a)
                 → ∀ {a} {a'} (p : a == a') → =ap f p • h a' == h a • p
  ==-is-nat-id h =rf = •idl (h _)

  =transp-fun-ptw-cod : {A B : Set}{C : A → Set}{a a' : A}(p : a == a')(f : B → C a)
                           → ∀ b → ((λ x → B → C x) ● p) f b == (C ● p) (f b)
  =transp-fun-ptw-cod {A} {B} {C} p f b =
    =J (λ x u → ((λ x' → B → C x') ● u) f b == (C ● u) (f b))
       =rf
       p

  =transp-fun-ptw₂-cod : {A B : Set}{C : A → B → Set}{a a' : A}
                         (p : a == a')(f : ∀ y → C a y)
                           → ∀ b → ((λ x → ∀ y → C x y) ● p) f b
                                       == ((λ x → C x b) ● p) (f b)
  =transp-fun-ptw₂-cod {A} {B} {C} p f b =
    =J (λ x u → ((λ x' → ∀ y → C x' y) ● u) f b == ((λ x → C x b) ● u) (f b))
       =rf
       p

  =transp-fun-ptw : {A : Set}{B C : A → Set}{a a' : A}(p : a == a')(f : B a → C a)
                       → ∀ b' → ((λ x → B x → C x) ● p) f b'
                                    == (C ● p) (f ((B ● p ⁻¹) b'))
  =transp-fun-ptw {A} {B} {C} p f =
    =J (λ _ u → ∀ y → ((λ x → B x → C x) ● u) f y == (C ● u) (f ((B ● u ⁻¹) y)))
       (λ _ → =rf)
       p

  =transp-famfun : {A A' : Set} (B : A → Set) {f f' : A' → A} (p : f == f')
                          → ∀ a → (λ x → (B ∘' x) a) ● p == B ● =ptw p a
  =transp-famfun B = =J (λ _ u → ∀ a → (λ x → (B ∘' x) a) ● u == B ● =ptw u a)
                        (λ _ → =rf)
  =transp-famfun-ptw : {A A' : Set} (B : A → Set) {f f' : A' → A} (p : f == f')
                          → ∀ a b → ((λ x → B (x a)) ● p) b == (B ● =ptw p a) b
  =transp-famfun-ptw B p a = =ptw (=transp-famfun B p a)


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

  =transp-ext : {A : Set}(B : A → Set){a a' : A}{p p' : a == a'}
                  → p == p' → B ● p == B ● p'
  =transp-ext B {p = p} = =ap (=transp B)

  =transp-ext-ptw : {A : Set}(B : A → Set){a a' : A}{p p' : a == a'}
                  → p == p' → ∀ b →  (B ● p) b == (B ● p') b
  =transp-ext-ptw B eq = =ptw (=transp-ext B eq)

  =transp-flip : {A : Set}(B : A → Set){a a' : A}(p : a == a')
                   → ∀ {b b'} → (B ● p) b == b' → b == (B ● p ⁻¹) b'
  =transp-flip B = =J (λ _ u → ∀ {b b'} → (B ● u) b == b' → b == (B ● u ⁻¹) b')
                     id

  =transp-flip⁻¹ : {A : Set}(B : A → Set){a a' : A}(p : a == a')
                   → ∀ {b b'} → b' == (B ● p) b → (B ● p ⁻¹) b' == b
  =transp-flip⁻¹ B = =J (λ _ u → ∀ {b b'} → b' == (B ● u) b → (B ● u ⁻¹) b' == b)
                       id

  =transp-flip-inv : {A : Set}(B : A → Set){a a' : A}(p : a == a')
                       → ∀ {b b'} → b == (B ● p ⁻¹) b' → (B ● p) b == b'
  =transp-flip-inv B = =J (λ _ u → ∀ {b b'} → b == (B ● u ⁻¹) b' → (B ● u) b == b')
                         id

  =transp-flip-inv⁻¹ : {A : Set}(B : A → Set){a a' : A}(p : a == a')
                         → ∀ {b b'} → (B ● p ⁻¹) b' == b → b' == (B ● p) b
  =transp-flip-inv⁻¹ B = =J (λ _ u → ∀ {b b'} → (B ● u ⁻¹) b' == b → b' == (B ● u) b)
                           id

  =transp-• : {A : Set}(B : A → Set){a a' a'' : A}(p : a == a')(q : a' == a'')
                → (B ● q) ∘ (B ● p) == B ● (p • q)
  =transp-• B p = =J (λ _ u → (B ● u) ∘ (B ● p) == B ● (p • u)) =rf
  =transp-•⁻¹ : {A : Set}(B : A → Set){a a' a'' : A}(p : a == a')(q : a' == a'')
                → B ● (p • q) == (B ● q) ∘ (B ● p)
  =transp-•⁻¹ B p q = =transp-• B p q ⁻¹

  =transp-•-ptw : {A : Set}(B : A → Set){a a' a'' : A}(p : a == a')(q : a' == a'')
               → ∀ b → (B ● q) ((B ● p) b) == (B ● (p • q)) b
  =transp-•-ptw B p q = =ptw (=transp-• B p q)

  =transp-•-ptw⁻¹ : {A : Set}(B : A → Set){a a' a'' : A}(p : a == a')(q : a' == a'')
               → ∀ b → (B ● (p • q)) b == (B ● q) ((B ● p) b)
  =transp-•-ptw⁻¹ B p q b = =transp-•-ptw B p q b ⁻¹

  =transp-•g : {A : Set}(B : A → Set){a a' a'' : A}{p : a == a'}{q : a' == a''}{r : a == a''}
                → p • q == r → (B ● q) ∘ (B ● p) == B ● r
  =transp-•g B {p = p} {q} pq=r = =transp-• B p q • =transp-ext B pq=r

  =transp-•g⁻¹ : {A : Set}(B : A → Set){a a' a'' : A}{p : a == a'}{q : a' == a''}{r : a == a''}
                    → p • q == r → B ● r == (B ● q) ∘ (B ● p)
  =transp-•g⁻¹ B {q = q} pq=r = =transp-•g B {q = q} pq=r ⁻¹

  =transp-•g-ptw : {A : Set}(B : A → Set){a a' a'' : A}{p : a == a'}{q : a' == a''}{r : a == a''}
                      → p • q == r → ∀ b → (B ● q) ((B ● p) b) == (B ● r) b
  =transp-•g-ptw B {q = q} pq=r = =ptw (=transp-•g B {q = q} pq=r)

  =transp-•g-ptw⁻¹ : {A : Set}(B : A → Set){a a' a'' : A}{p : a == a'}{q : a' == a''}{r : a == a''}
                      → p • q == r → ∀ b → (B ● r) b == (B ● q) ((B ● p) b)
  =transp-•g-ptw⁻¹ B {q = q} pq=r b = =transp-•g-ptw B {q = q} pq=r b ⁻¹

  =transp-back-forth : {A : Set}(B : A → Set){a a' : A}(p : a == a')
                         → (B ● p) ∘ (B ● p ⁻¹) == id
  =transp-back-forth B p = =proof
    B ● p ∘ B ● p ⁻¹  ==[ =transp-• B (p ⁻¹) p ] /
    B ● p ⁻¹ • p      ==[ =transp-ext B (•invl p) ]∎
    id ∎

  =transp-back-forth-ptw : {A : Set}(B : A → Set){a a' : A}(p : a == a')
                         → ∀ b' → (B ● p) ((B ● p ⁻¹) b') == b'
  =transp-back-forth-ptw B p = =ptw (=transp-back-forth B p)
  =transp-back-forth-ptw⁻¹ : {A : Set}(B : A → Set){a a' : A}(p : a == a')
                         → ∀ b' → b' == (B ● p) ((B ● p ⁻¹) b')
  =transp-back-forth-ptw⁻¹ B p b' = =transp-back-forth-ptw B p b' ⁻¹

  =transp-forth-back : {A : Set}(B : A → Set){a a' : A}(p : a == a')
                         → (B ● p ⁻¹) ∘ (B ● p) == id
  =transp-forth-back B p = =proof
    B ● p ⁻¹ ∘ B ● p  ==[ =transp-• B p (p ⁻¹) ] /
    B ● p • p ⁻¹      ==[ =transp-ext B (•invr p) ]∎
    id ∎

  =transp-forth-back-ptw : {A : Set}(B : A → Set){a a' : A}(p : a == a')
                         → ∀ b' → (B ● p ⁻¹) ((B ● p) b') == b'
  =transp-forth-back-ptw B p = =ptw (=transp-forth-back B p)
  =transp-forth-back-ptw⁻¹ : {A : Set}(B : A → Set){a a' : A}(p : a == a')
                         → ∀ b' → b' == (B ● p ⁻¹) ((B ● p) b')
  =transp-forth-back-ptw⁻¹ B p b' = =transp-forth-back-ptw B p b' ⁻¹

  -- stuff on identities over identites
  =/cmp : {A : Set} {B : A → Set} {a₁ a₂ a₃ : A} (p : a₁ == a₂) (q : a₂ == a₃)
             → ∀ {b₁ b₂ b₃} (pp : b₁ ==/ b₂ [ B / p ]) (qq : b₂ ==/ b₃ [ B / q ])
               → b₁ ==/ b₃ [ B / p • q ]
  =/cmp {A} {B} {a₁} p q {b₁} {b₂} {b₃} pp qq = =proof
    (B ● p • q) b₁           ==[ =transp-•-ptw⁻¹ B p q b₁ ] /
    (B ● q) ((B ● p) b₁)     ==[ =ap (B ● q) pp ] /
    (B ● q) b₂               ==[ qq ]∎
    b₃ ∎

  =/inv : {A : Set} {B : A → Set} {a₁ a₂ : A} (p : a₁ == a₂)
             → ∀ {b₁ b₂} (pp : b₁ ==/ b₂ [ B / p ])
               → b₂ ==/ b₁ [ B / p ⁻¹ ]
  =/inv {A} {B} p {b₁} {b₂} pp = =transp-flip⁻¹ B p (pp ⁻¹)
  =/cmp-any : {A : Set} {B : A → Set} {a₁ a₂ a₃ : A} {p : a₁ == a₂}
              {q : a₂ == a₃} {r : a₁ == a₃} → p • q == r 
                 → ∀ {b₁ b₂ b₃} (pp : b₁ ==/ b₂ [ B / p ]) (qq : b₂ ==/ b₃ [ B / q ])
                     → b₁ ==/ b₃ [ B / r ]
  =/cmp-any {A} {B} {p = p} {q} {r} tr {b₁} {b₂} {b₃} pp qq = =proof
    (B ● r) b₁               ==[ =transp-•g-ptw⁻¹ B {q = q} tr b₁ ] /
    (B ● q) ((B ● p) b₁)     ==[ =ap (B ● q) pp ] /
    (B ● q) b₂               ==[ qq ]∎
    b₃ ∎

  =/inv-any : {A : Set} {B : A → Set} {a₁ a₂ : A} {p : a₁ == a₂}
                 → ∀ {p'} → p ⁻¹ == p' → ∀ {b₁ b₂} (pp : b₁ ==/ b₂ [ B / p ])
                   → b₂ ==/ b₁ [ B / p' ]
  =/inv-any {p = p} eq pp = =/ext eq (=/inv p pp)

  =/ext-is-ext• : ∀ {A} (B : A → Set) → ∀ {a a'} {p p' : a == a'} (eq : p == p')
                    → ∀ {b b'} (pp : b ==/ b' [ B / p ])
                      → =/ext eq pp == =transp-ext-ptw B eq b ⁻¹ • pp
  =/ext-is-ext• B {p = p} eq {b} {b'} pp = =proof
    ((λ u → b ==/ b' [ B / u ]) ● eq) pp
                                 ==[ ●=ap-is-●⁻¹ (λ x → x b == b') (λ u → B ● u) eq _ ] /
    ((λ x → x b == b') ● =ap (B ●_) eq) pp
                                    ==[ =transp-famfun-ptw (_== b') (=ap (B ●_) eq) _ _ ] /
    ((_== b') ● =ptw (=ap (B ●_) eq) b) pp
                                     ==[ =transp-precmp-inv (=ptw (=ap (B ●_) eq) b) _  ]∎
    =ptw (=ap (B ●_) eq) b ⁻¹ • pp ∎


  ---------------------------------
  -- Identities of inductive types
  ---------------------------------

  ×η : {A B : Set}(z : A × B) → (prj1 z) , (prj2 z) == z
  ×η (a , b) = =rf
  ×η⁻¹ : {A B : Set}(z : A × B) → z == (prj1 z) , (prj2 z)
  ×η⁻¹ z = ×η z ⁻¹

  =prj1 : {A B : Set} {z z' : A × B} → z == z' → prj1 z == prj1 z'
  =prj1 {A} {B} = =ap (prj1 {A} {B})
  =prj2 : {A B : Set} {z z' : A × B} → z == z' → prj2 z == prj2 z'
  =prj2 {A} {B} = =ap (prj2 {A} {B})

  =prj1×η=rf : ∀ {A B} (z : A × B) → =prj1 (×η z) == =rf
  =prj1×η=rf (a , b) = =rf
  =prj2×η=rf : ∀ {A B} (z : A × B) → =prj2 (×η z) == =rf
  =prj2×η=rf (a , b) = =rf
  =prj1×η⁻¹=rf : ∀ {A B} (z : A × B) → =prj1 (×η⁻¹ z) == =rf
  =prj1×η⁻¹=rf (a , b) = =rf
  =prj2×η⁻¹=rf : ∀ {A B} (z : A × B) → =prj2 (×η⁻¹ z) == =rf
  =prj2×η⁻¹=rf (a , b) = =rf

  =×char, : ∀ {A B} {z : A × B} {a b}
               → prj1 z == a → prj2 z == b → z == a , b
  =×char, {A} {B} {z} pf₁ pf₂ = ×η⁻¹ z • =ap₂ (_,_ {A} {B}) pf₁ pf₂  
  =×char : {A B : Set} {z z' : A × B}
               → prj1 z == prj1 z' → prj2 z == prj2 z'
                 → z == z'
  =×char {z' = z'} pf₁ pf₂ = =×char, pf₁ pf₂ • ×η z'

  =pj1 : ∀ {A B} {z z' : Σ[ A ] B} → z == z' → pj1 z == pj1 z'
  =pj1 = =ap pj1
  Bpj1● : ∀ {A B} {z z' : Σ[ A ] B} → (u : z == z')
            → ∀ b → (B ● (=pj1 u)) b == ((λ z → B (pj1 z)) ● u) b
  Bpj1● {A} {B} = ●=ap-is-● B pj1

  =pj2' : ∀ {A B} {z z' : Σ[ A ] B} → (u : z == z') → ((λ z → B (pj1 z)) ● u) (pj2 z) == pj2 z'
  =pj2' {A} {B} {z} {z'} u = =apd {A = Σ[ A ] B} {B = λ z → B (pj1 z)} pj2 u
  =pj2 : ∀ {A B} {z z' : Σ[ A ] B} → (u : z == z') → (B ● (=pj1 u)) (pj2 z) == pj2 z'
  =pj2 {A} {B} {z} {z'} u = =proof
    (B ● =pj1 u) (pj2 z)                  ==[ Bpj1● u (pj2 z) ] /
    ((λ z₁ → B (pj1 z₁)) ● u) (pj2 z)    ==[ =pj2' u ]∎
    pj2 z' ∎

  Ση : ∀ {A} {B : A → Set}(z : Σ[ A ] B) → (pj1 z) ,, (pj2 z) == z
  Ση (a ,, b) = =rf
  Ση⁻¹ : ∀ {A} {B : A → Set}(z : Σ[ A ] B) → z == (pj1 z) ,, (pj2 z)
  Ση⁻¹ (a ,, b) = =rf
  =pj1Ση=rf : ∀ {A} {B : A → Set} z → =pj1 (Ση {A} {B} z) == =rf
  =pj1Ση=rf (a ,, b) = =rf
  =pj1Ση⁻¹=rf : ∀ {A} {B : A → Set} z → =pj1 (Ση⁻¹ {A} {B} z) == =rf
  =pj1Ση⁻¹=rf (a ,, b) = =rf
  =pj2Ση=rf : ∀ {A} {B : A → Set} z
                → =pj2 (Ση {A} {B} z) == =transp-ext-ptw B (=pj1Ση=rf z) (pj2 z)
  =pj2Ση=rf (a ,, b) = =rf
  =pj2Ση⁻¹-is-ext : ∀ {A} {B : A → Set} z
                  → =pj2 (Ση⁻¹ {A} {B} z) == =transp-ext-ptw B (=pj1Ση⁻¹=rf z) (pj2 z)
  =pj2Ση⁻¹-is-ext (a ,, b) = =rf  

  =Σover,, :  ∀ {A} (B : A → Set) {a : A}
               → {b b' : B a} → b == b' → _,,_ {A} {B} a b == a ,, b'
  =Σover,, B {a} {b} = =J (λ w _ → a ,, b == a ,, w) =rf
  =pj1=Σover,,=rf :  ∀ {A} (B : A → Set) {a : A} {b b' : B a} (q : b == b')
                       → =pj1 (=Σover,, B q) == =rf
  =pj1=Σover,,=rf B q = =J (λ _ v → =pj1 (=Σover,, B v) == =rf) =rf q
  =pj2=Σover,,-is-ext :  ∀ {A} (B : A → Set) {a : A} {b b' : B a} (q : b == b')
              → =pj2 (=Σover,, B q) == =transp-ext-ptw B (=pj1=Σover,,=rf B q) b • q
  =pj2=Σover,,-is-ext {A} B =rf = =rf

  =Σover :  ∀ {A} {B : A → Set} {z : Σ[ A ] B}
               → ∀ {b} → b == pj2 z → pj1 z ,, b == z
  =Σover {A} {B} {z} eq = =Σover,, B {pj1 z} eq • Ση z

  =Σover⁻¹ :  ∀ {A} {B : A → Set} {z : Σ[ A ] B}
               → ∀ {b} → pj2 z == b → z == pj1 z ,, b
  =Σover⁻¹ {z = z} eq = Ση⁻¹ z • =Σover,, _ {pj1 z} eq

  =pj1=Σover⁻¹=rf : ∀ {A} {B : A → Set} (z : Σ[ A ] B) → ∀ {b} (q : pj2 z == b)
                          → =pj1 {z = z} (=Σover⁻¹ q) == =rf
  =pj1=Σover⁻¹=rf {A} {B} z =rf = =pj1Ση⁻¹=rf z
{-=proof
            =pj1 (=Σover⁻¹ q)
                               ==[ =ap• (pj1 {A} {B}) _ (=Σover,, _ {pj1 z} q) ] /
            =pj1 (Ση⁻¹ z) • =pj1 {A} {B} (=Σover,, _ {pj1 z} q)
                               ==[ •idlg-inv (=pj1Ση⁻¹=rf  z) (=pj1=Σover,,=rf B q) ]∎
            =rf ∎-}
          
  =pj2=Σover⁻¹-is-ext : ∀ {A} {B : A → Set} (z : Σ[ A ] B) → ∀ {b} (q : pj2 z == b)
      → =pj2 {z = z} (=Σover⁻¹ q) == =transp-ext-ptw B (=pj1=Σover⁻¹=rf z q) (pj2 z)
                                          • q
  =pj2=Σover⁻¹-is-ext z =rf = =pj2Ση⁻¹-is-ext z

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
    

  =transp-inl : {A : Set}(B C : A → Set){a a' : A}(p : a == a')
                  → ((λ x → B x + C x) ● p) ∘ inl == inl ∘ (B ● p)
  =transp-inl B C = =J (λ _ u → ((λ x → B x + C x) ● u) ∘ inl == inl ∘ (B ● u)) =rf

  =transp-inl-ptw : {A : Set}(B C : A → Set){a a' : A}(p : a == a')
                  → ∀ b →  ((λ x → B x + C x) ● p) (inl b) == inl ((B ● p) b)
  =transp-inl-ptw B C p = =ptw (=transp-inl B C p)

  =transp-inr : {A : Set}(B C : A → Set){a a' : A}(p : a == a')
                  → ((λ x → B x + C x) ● p) ∘ inr == inr ∘ (C ● p)
  =transp-inr B C = =J (λ _ u → ((λ x → B x + C x) ● u) ∘ inr == inr ∘ (C ● u)) =rf

  =transp-inr-ptw : {A : Set}(B C : A → Set){a a' : A}(p : a == a')
                  → ∀ c →  ((λ x → B x + C x) ● p) (inr c) == inr ((C ● p) c)
  =transp-inr-ptw B C p = =ptw (=transp-inr B C p)

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

  isProp→isContr : {A : Set} → isProp A → A → isContr A
  isProp→isContr prp a = a ,, λ x → prp x a

  N₁-isProp : isProp N₁
  N₁-isProp = isContr→isProp N₁-isContr

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
  UIP = isSet
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
          q' : (e : R a a) → ((_==_ a) ● p) (R→== a a e) == R→== a a e
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

  infix 2 _≃_
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
                                                       ==[ =pj2' (pj2 (eqvf b) (a ,, p)) ]∎
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
                                         ==[ =ap (=ap inr) (=pj2' (pj2 (eqvf b) (aux z))) ]∎
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

  eqv-prop-is-prop : {A B : Set} → isProp A → {f : A → B} → is-equiv f → isProp B
  eqv-prop-is-prop {A} {B} prpA {f} eqvf  b b' =
    =proof b            ==[ fg=idB b ⁻¹ ] /
           f (g b)      ==[ =ap f (prpA _ _) ] /
           f (g b')     ==[ fg=idB b' ]∎
           b' ∎
    where g : B → A
          g b = pj1 (pj1 (eqvf b))
          fg=idB : ∀ b → f (g b) == b
          fg=idB b = pj2 (pj1 (eqvf b))

  -- using `∀-is-prop` (and `FunExt`)
  is-equiv-is-Prop : ∀ {A B f} → isProp (is-equiv {A} {B} f)
  is-equiv-is-Prop {A} {B} {f} = ∀-is-prop (λ b → isContr (fib f b))
                                           (λ b → isContr-is-prop (fib f b))

  
  -- surjective functions
  is-surjective :  {A B : Set} → (A → B) → Set
  is-surjective f = ∀ b → fib f b

  surjective-cmp : {A B C : Set} {f : A → B} {g : B → C}
                     → is-surjective f → is-surjective g → is-surjective (g ∘ f)
  surjective-cmp {A} {B} {C} {f} {g} fsj gsj c =
    pj1 (fsj b)
    ,, =ap g (pj2 (fsj b)) • pj2 (gsj c)
    where b : B
          b = pj1 (gsj c)
  surjective-tr : {A B C : Set} {f : A → B} {g : B → C} {h : A → C}
                     → (∀ {a} → g (f a) == h a) → is-surjective h
                          → is-surjective g
  surjective-tr {A} {B} {C} {f} {g} {h} tr hsj c =
    f a
    ,, tr • pj2 (hsj c)
    where a : A
          a = pj1 (hsj c)
  
  -- invertible functions
  is-iso-pair : ∀ {A B} → (f : A → B) → (g : B → A) → Set
  is-iso-pair f g = (∀ a → g (f a) == a) × (∀ b → f (g b) == b)
  is-adj-iso-pair : ∀ {A B} → (f : A → B) → (g : B → A) → Set
  is-adj-iso-pair f g = Σ[ (∀ a → g (f a) == a) × (∀ b → f (g b) == b) ]
                           (λ ii → (∀ a → =ap f (prj1 ii a) == prj2 ii (f a))
                                    × (∀ b → =ap g (prj2 ii b) == prj1 ii (g b)) )
  module adjiso {A B} {f : A → B} {g : B → A}(adjiso : is-adj-iso-pair f g) where
    ζ : ∀ a → g (f a) == a
    ζ = prj1 (pj1 adjiso)
    ξ : ∀ b → f (g b) == b
    ξ = prj2 (pj1 adjiso)
    fζ=ξf : ∀ a → =ap f (ζ a) == ξ (f a)
    fζ=ξf = prj1 (pj2 adjiso)
    gξ=ζg : ∀ b → =ap g (ξ b) == ζ (g b)
    gξ=ζg = prj2 (pj2 adjiso)
  adjiso-is-iso : ∀ {A B} {f : A → B} {g : B → A} → is-adj-iso-pair f g → is-iso-pair f g
  adjiso-is-iso = pj1
  is-invrt : ∀ {A B} → (f : A → B) → Set
  is-invrt {A} {B} f = Σ[ (B → A) ] (is-iso-pair f)
  is-adj-invrt : ∀ {A B} → (f : A → B) → Set
  is-adj-invrt {A} {B} f = Σ[ (B → A) ] (is-adj-iso-pair f)
  module adjinv  {A B} {f : A → B} (adjinv : is-adj-invrt f)
                 = adjiso (pj2 adjinv)
  adjinv-is-inv : ∀ {A B} {f : A → B} → is-adj-invrt f → is-invrt f
  adjinv-is-inv = ⟨ pj1 ∣∣ (λ x → adjiso-is-iso (pj2 x)) ⟩

  -- functions full in identities
  is-idfull : ∀ {A B} (f : A → B) → Set
  is-idfull f = ∀ {a a'} → is-surjective (=ap f {a} {a'})

  -- some invertible functions
  inv-is-invrt : ∀ {A B} {f : A → B} (invf : is-invrt f) → is-invrt (pj1 invf)
  inv-is-invrt {f = f} invf = f ,, (prj2 (pj2 invf) , prj1 (pj2 invf))
  id-is-invrt : ∀ {A} → is-invrt (id {A})
  id-is-invrt {A} = id ,, ((λ _ → =rf) , (λ _ → =rf))
  =id-is-invrt : ∀ {A} {f : A → A} → (∀ a → f a == a) → is-invrt f
  =id-is-invrt =id = id ,, (=id , =id)
  =invrt-is-invrt : ∀ {A B} {f g : A → B} → (∀ a → f a == g a) → is-invrt g → is-invrt f
  =invrt-is-invrt {A} {B} {f} {g} pf ginv = pj1 ginv ,, ((λ a → =ap (pj1 ginv) (pf a) • prj1 (pj2 ginv) a)
                                                         , λ b → pf _ • prj2 (pj2 ginv) b)
  =transp-is-invrt : {A : Set}(B : A → Set){a a' : A} (p : a == a')
                        → is-invrt (B ● p)
  =transp-is-invrt {A} B p =
    B ● (p ⁻¹) ,, (=transp-forth-back-ptw B p , =transp-back-forth-ptw B p)
  equiv-is-invrt : ∀ {A B} {f : A → B} → is-equiv f → is-invrt f
  equiv-is-invrt {A} {B} {f} eqvf = g ,, (gf=idA , fg=idB)
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

  -- invertible functions and equivalences are surjective
  invrt-is-surjective : ∀ {A B} {f : A → B} → is-invrt f → is-surjective f
  invrt-is-surjective {A} {B} {f} finv b =
    pj1 finv b
    ,, prj2 (pj2 finv) b
  adj-invrt-is-surjective : ∀ {A B} {f : A → B} → is-adj-invrt f → is-surjective f
  adj-invrt-is-surjective = invrt-is-surjective ∘ adjinv-is-inv
  equiv-is-surjective : ∀ {A B} {f : A → B} → is-equiv f → is-surjective f
  equiv-is-surjective eqv b = pj1 (eqv b)

  -- the main lemma on functions full on identities
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
  -- with its theorem
  surj+idfull-is-equiv : ∀ {A B} {f : A → B} → is-surjective f → is-idfull f → is-equiv f
  surj+idfull-is-equiv {A} {B} {f} fsj fif b =
    isProp→isContr (idfull-fib-is-prop fif b) (fsj b)
  
  -- compositions of invertible functions
  invrt-cmp-rf : ∀ {A B C} {f : A → B}{g : B → C}
                 → is-invrt f → is-invrt g → is-invrt (g ∘ f)
  invrt-cmp-rf {A} {B} {C} {f} {g} invf invg =
    (finv ∘ ginv)
    ,, ((λ a → =proof
       finv (ginv (g (f a)))    ==[ =ap finv (prj1 (pj2 invg) (f a)) ] /
       finv (f a)             ==[ prj1 (pj2 invf) a ]∎
       a ∎)
     , (λ c → =proof
       g (f (finv (ginv c)))    ==[ =ap g (prj2 (pj2 invf) (ginv c)) ] /
       g (ginv c)             ==[ prj2 (pj2 invg) c ]∎
       c ∎))
    where finv : B → A
          finv = pj1 invf
          ginv : C → B
          ginv = pj1 invg

  invrt-cmp : ∀ {A B C} {f : A → B} {g : B → C} {h : A → C}
                 → (∀ x → h x == g (f x)) → is-invrt f → is-invrt g → is-invrt h
  invrt-cmp {A} {B} {C} {f} {g} {h} h=gf invf invg = =invrt-is-invrt h=gf (invrt-cmp-rf invf invg)


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

  -- every adjoint-invertible map is full on identities
  
  adj-invrt-is-idfull : ∀ {A B} {f : A → B} → is-adj-invrt f → is-idfull f
  adj-invrt-is-idfull {A} {B} {f} adjinv {a} {a'} q =
    p ,, fp=q
    where module f = adjinv adjinv
          g : B → A
          g = pj1 adjinv
          p : a == a'
          p = f.ζ a ⁻¹ • =ap g q • f.ζ a'
          fp=q : =ap f p == q
          fp=q = =proof =ap f p
                              ==[ =ap• f _ (=ap g q • f.ζ a') • •extl _ (=ap• f _ (f.ζ a')) ] /
                         =ap f (f.ζ a ⁻¹) • =ap f (=ap g q) • =ap f (f.ζ a')
                              ==[ •extlr (=proof
                         =ap f (f.ζ a ⁻¹)
                              ==[ ⁻¹=ap f (f.ζ a) ] /
                         =ap f (f.ζ a) ⁻¹
                              ==[ =ap _⁻¹ (f.fζ=ξf a) ]∎
                         f.ξ (f a) ⁻¹ ∎)
                                         (=proof
                                         =ap f (=ap g q) • =ap f (f.ζ a')
                                                        ==[ •extlr (=ap∘ g f q) (f.fζ=ξf a') ] /
                                         =ap (f ∘ g) q • f.ξ (f a')
                                                                      ==[ ==-is-nat-id f.ξ q ]∎
                                         f.ξ (f a) • q ∎) ] /
                         f.ξ (f a) ⁻¹ • f.ξ (f a) • q
                              ==[ •ass _ _ q • •idlg-inv (•invl (f.ξ _)) =rf ]∎
                         q ∎

  -- and thus that every adjoint-invertible map is an equivalence
  adj-invrt-is-eqv : ∀ {A B} {f : A → B} → is-adj-invrt f → is-equiv f
  adj-invrt-is-eqv {A} {B} {f} adjinv =
    surj+idfull-is-equiv (adj-invrt-is-surjective adjinv)
                         (adj-invrt-is-idfull adjinv)

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
      fg=idB-adj b = =proof
        f (g b)            ==[ fg=idB (f (g b)) ⁻¹ ] /
        f (g (f (g b)))    ==[ =ap f (gf=idA (g b)) ] /
        f (g b)            ==[ fg=idB b ]∎
        b ∎
      gf-aux₁ : ∀ a → =ap (g ∘ f) (gf=idA a) • gf=idA a == gf=idA (g (f a)) • gf=idA a
      gf-aux₁ a = ==-is-nat-id gf=idA (gf=idA a)
      fg-aux₁ : ∀ b → =ap (f ∘ g) (fg=idB b) • fg=idB b == fg=idB (f (g b)) • fg=idB b
      fg-aux₁ b = ==-is-nat-id fg=idB (fg=idB b)
      gf-aux₂ : ∀ a → =ap (g ∘ f) (gf=idA a) == gf=idA (g (f a))
      gf-aux₂ a = •rc {p = gf=idA a} (gf-aux₁ a)
      fg-aux₂ : ∀ b → =ap (f ∘ g) (fg=idB b) == fg=idB (f (g b))
      fg-aux₂ b = •rc {p = fg=idB b} (fg-aux₁ b)

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

  -- thus invertible maps are idfull and equivalences
  invrt-is-idfull : ∀ {A B} {f : A → B} → is-invrt f → is-idfull f
  invrt-is-idfull {A} {B} {f} inv = adj-invrt-is-idfull (invrt-is-adj inv)

  invrt-is-eqv : ∀ {A B} {f : A → B} → is-invrt f → is-equiv f
  invrt-is-eqv {A} {B} {f} inv = adj-invrt-is-eqv (invrt-is-adj inv)

  -- equivalences are thus closed under composition
  -- (probably not the best proof though)
  ∘eqv : {A B C : Set}{f : A → B}{g : B → C}
             → is-equiv f → is-equiv g → is-equiv (g ∘ f)
  ∘eqv {A} {B} {C} {f} {g} eqvf eqvg = invrt-is-eqv (invrt-cmp-rf invf invg)
    where invf : is-invrt f
          invf = equiv-is-invrt eqvf
          invg : is-invrt g
          invg = equiv-is-invrt eqvg

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
          inv = equiv-is-invrt (pj2 eqv)
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


  -- the identity type of a binary product is equivalent to the binary product of idenity types
  =×isopair : ∀ {A B} (z z' :  A × B)
                → is-iso-pair {z == z'}
                               {(prj1 z == prj1 z') × (prj2 z == prj2 z')}
                               ⟨ =prj1 ∣ =prj2 ⟩
                               λ uu → =×char (prj1 uu) (prj2 uu)
  =×isopair {A} {B} z z' = iddom , λ uu → =×char (idcod1 uu) (idcod2 uu)
    where iddom : (r : z == z') → =×char (=prj1 r) (=prj2 r) == r
          iddom r = =proof
            =×char (=prj1 r) (=prj2 r)
                                   ==[ •ass⁻¹ _ _ (×η z') ] /
            ×η⁻¹ z • =ap₂ (_,_ {A} {B}) (=prj1 r) (=prj2 r) • ×η z'
                                   ==[ •extl (×η⁻¹ z) (=proof
              =ap₂ (_,_ {A} {B}) (=prj1 r) (=prj2 r) • ×η z'
                                           ==[ •extr (×η z') (=ap₂∘₁ prj1 prj2 _,_ r ) ] /
              =ap (λ z → prj1 z , prj2 z) r • ×η z'
                                           ==[ ==-is-nat-id ×η r ]∎
              ×η z • r ∎) ] /
            ×η⁻¹ z • ×η z • r
                                   ==[ •ass _ _ r • •idlg-inv (•invl (×η z)) =rf ]∎
            r ∎
          idcod1 : (uu : (prj1 z == prj1 z') × (prj2 z == prj2 z'))
                       → =prj1 {z = z} {z'} (=×char (prj1 uu) (prj2 uu)) == prj1 uu
          idcod1 uu = =proof
            =prj1 (=×char (prj1 uu) (prj2 uu))
                  ==[ =ap =prj1 (•ass⁻¹ _ _ (×η z')) ] /
            =prj1 (×η⁻¹ z • =ap₂ (_,_ {A} {B}) (prj1 uu) (prj2 uu) • ×η z')
                  ==[ =ap• prj1 (×η⁻¹ z) (=ap₂ _,_ (prj1 uu) (prj2 uu) • ×η z')
                      • •extl (=prj1 (×η⁻¹ z)) (=ap• prj1 _ (×η z')) ] /
            =prj1 (×η⁻¹ z) • =prj1 (=ap₂ (_,_ {A} {B}) (prj1 uu) (prj2 uu)) • =prj1 (×η z')
                  ==[ •idlg-inv (=prj1×η⁻¹=rf z) (•idrg-inv (=prj1×η=rf z') =rf) ] /
            =prj1 (=ap₂ (_,_ {A} {B}) (prj1 uu) (prj2 uu))
                  ==[ =ap∘=ap₂ _,_ prj1 (prj1 uu) (prj2 uu) • =ap₂-prj1 _ _ ]∎
            prj1 uu ∎
          idcod2 : (uu : (prj1 z == prj1 z') × (prj2 z == prj2 z'))
                       → =prj2 {z = z} {z'} (=×char (prj1 uu) (prj2 uu)) == prj2 uu
          idcod2 uu = =proof
            =prj2 (=×char (prj1 uu) (prj2 uu))
                  ==[ =ap =prj2 (•ass⁻¹ _ _ (×η z')) ] /
            =prj2 (×η⁻¹ z • =ap₂ (_,_ {A} {B}) (prj1 uu) (prj2 uu) • ×η z')
                  ==[ =ap• prj2 (×η⁻¹ z) (=ap₂ _,_ (prj1 uu) (prj2 uu) • ×η z')
                      • •extl (=prj2 (×η⁻¹ z)) (=ap• prj2 _ (×η z')) ] /
            =prj2 (×η⁻¹ z) • =prj2 (=ap₂ (_,_ {A} {B}) (prj1 uu) (prj2 uu)) • =prj2 (×η z')
                  ==[ •idlg-inv (=prj2×η⁻¹=rf z) (•idrg-inv (=prj2×η=rf z') =rf) ] /
            =prj2 (=ap₂ (_,_ {A} {B}) (prj1 uu) (prj2 uu))
                  ==[ =ap∘=ap₂ _,_ prj2 (prj1 uu) (prj2 uu) • =ap₂-prj2 (prj1 uu) _ ]∎
            prj2 uu ∎

  =prj12-is-invrt : ∀ {A B} (z z' : A × B)
                     → is-invrt {z == z'}
                                 {(prj1 z == prj1 z') × (prj2 z == prj2 z')}
                                 ⟨ =prj1 ∣ =prj2 ⟩
  =prj12-is-invrt z z' = (λ uu → =×char (prj1 uu) (prj2 uu)) ,, =×isopair z z'

  =×char-is-invrt : ∀ {A B} (z z' : A × B)
                     → is-invrt {(prj1 z == prj1 z') × (prj2 z == prj2 z')}
                                 {z == z'}
                                 (λ uu → =×char (prj1 uu) (prj2 uu))
  =×char-is-invrt z z' = ⟨ =prj1 ∣ =prj2 ⟩ ,, (prj2 (=×isopair z z') , prj1 (=×isopair z z'))

  =×eqv : ∀ {A B} (z z' : A × B)
                → (z == z') ≃ (prj1 z == prj1 z') × (prj2 z == prj2 z')
  =×eqv z z' = ⟨ =prj1 ∣ =prj2 ⟩ ,, invrt-is-eqv (=prj12-is-invrt z z')
    
  =×eqv⁻¹ : ∀ {A B} (z z' : A × B)
                → (prj1 z == prj1 z') × (prj2 z == prj2 z') ≃ (z == z')
  =×eqv⁻¹ {A} {B} z z' =
    (λ uu → =×char (prj1 uu) (prj2 uu)) ,, invrt-is-eqv (=×char-is-invrt z z')



  -- the identity type of a Σ-type is equivalent to the Σ-type of idenity types

  =Σisopair : ∀ {A B} (z z' : Σ[ A ] B)
                → is-iso-pair {z == z'}
                               {Σ[ (pj1 z == pj1 z') ] (λ u → pj2 z ==/ pj2 z' [ B / u ])}
                               ⟨ =pj1 ∣∣ =pj2 ⟩
                               (λ uu → =Σchar (pj1 uu) (pj2 uu))
  =Σisopair {A} {B} z z' =  iddom {z'}
                            , λ uu → =Σchar (idcod1 (pj1 uu) (pj2 uu))
                                             (idcod2 {z'} (pj1 uu) (pj2 uu))
    where iddom : ∀ {w} (r : z == w) → =Σchar (=pj1 r) (=pj2 r) == r
          iddom {a ,, b} =rf = =rf
          idcod1-rf : ∀ {b} q → =pj1 {z = z} {pj1 z ,, b} (=Σchar =rf q) == =rf
          idcod1-rf q = =pj1=Σover⁻¹=rf z q
          idcod1 : {w : Σ[ A ] B} (p : pj1 z == pj1 w)
                     → ∀ q → =pj1 {z = z} {w} (=Σchar p q) == p
          idcod1 {a ,, b} p q =
            =J (λ _ u → ∀ {y} (v : (B ● u) (pj2 z) == y) → =pj1 (=Σchar,, u v) == u)
               idcod1-rf p {b} q
          auxext : ∀ {b} (q : pj2 z == b)
                     → (B ● =pj1 {z = z} (=Σover⁻¹ q)) (pj2 z) == (pj2 z)
          auxext q = =transp-ext-ptw B (idcod1-rf q) (pj2 z)
          idcod2 : {w : Σ[ A ] B} (p : pj1 z == pj1 w) (q : (B ● p) (pj2 z) == pj2 w)
                      → =pj2 {z = z} {w} (=Σchar p q) ==/ q
                              [ (λ u → pj2 z ==/ pj2 w [ B / u ]) / idcod1 {w = w} p q ]
          idcod2 {.(pj1 z) ,, b} =rf q = =proof
            ((λ u → pj2 z ==/ b [ B / u ]) ● idcod1-rf q) (=pj2 {z = z} (=Σover⁻¹ q))
                    ==[ =/ext-is-ext• B (idcod1-rf q) _ ] /
            auxext q ⁻¹ • =pj2 {z = z} (=Σover⁻¹ q)
                                                   ==[ •extl _ (=pj2=Σover⁻¹-is-ext z q) ] /
            auxext q ⁻¹ • auxext q • q
                              ==[ •ass _ (auxext q) q • •idlg-inv (•invl (auxext q)) =rf ]∎
            q ∎

  =pj12-is-invrt : ∀ {A B} (z z' : Σ[ A ] B)
                     → is-invrt {z == z'}
                                 {Σ[ (pj1 z == pj1 z') ] (λ u → pj2 z ==/ pj2 z' [ B / u ])}
                                 ⟨ =pj1 ∣∣ =pj2 ⟩
  =pj12-is-invrt z z' = (λ uu → =Σchar (pj1 uu) (pj2 uu)) ,, =Σisopair z z'

  =Σchar-is-invrt : ∀ {A B} (z z' : Σ[ A ] B)
                     → is-invrt {Σ[ (pj1 z == pj1 z') ] (λ u → pj2 z ==/ pj2 z' [ B / u ])}
                                 {z == z'}
                                 (λ uu → =Σchar (pj1 uu) (pj2 uu))
  =Σchar-is-invrt z z' = ⟨ =pj1 ∣∣ =pj2 ⟩ ,, (prj2 (=Σisopair z z') , prj1 (=Σisopair z z'))

  =Σeqv : ∀ {A B} (z z' : Σ[ A ] B)
                → (z == z') ≃ Σ[ (pj1 z == pj1 z') ] (λ u → pj2 z ==/ pj2 z' [ B / u ])
  =Σeqv z z' = ⟨ =pj1 ∣∣ =pj2 ⟩ ,, invrt-is-eqv (=pj12-is-invrt z z')
    
  =Σeqv⁻¹ : ∀ {A B} (z z' : Σ[ A ] B)
                → Σ[ (pj1 z == pj1 z') ] (λ u → pj2 z ==/ pj2 z' [ B / u ]) ≃ (z == z')
  =Σeqv⁻¹ {A} {B} z z' =
    (λ uu → =Σchar (pj1 uu) (pj2 uu)) ,, invrt-is-eqv (=Σchar-is-invrt z z')

  -- as a consequence, props and sets are closed under Σ-types
  Σpp-is-prop : ∀ {A} {B : A → Set} → isProp A → (∀ a → isProp (B a)) → isProp (Σ[ A ] B)
  Σpp-is-prop {A} {B} prpA prpB z z' = =proof
    z                  ==[ Ση⁻¹ z ] /
    pj1 z ,, pj2 z     ==[ =Σchar,, (prpA _ _) (prpB (pj1 z') _ _) ] /
    pj1 z' ,, pj2 z'   ==[ Ση z' ]∎
    z' ∎
  Σss-is-set : ∀ {A} {B : A → Set} → isSet A → (∀ a → isSet (B a)) → isSet (Σ[ A ] B)
  Σss-is-set {A} {B} Aset Bsets {z} {z'} =
    eqv-prop-is-prop (Σpp-is-prop Aset (λ _ → Bsets _))
                     (pj2 (=Σeqv⁻¹ z z')) 
  Σsp-is-set : ∀ {A} {B : A → Set} → isSet A → (∀ a → isProp (B a)) → isSet (Σ[ A ] B)
  Σsp-is-set {A} {B} Aset Bprps {z} {z'} =
    eqv-prop-is-prop (Σpp-is-prop Aset λ _ → isProp→=isProp (Bprps _))
                     (pj2 (=Σeqv⁻¹ z z')) 

  ×pp-is-prop : ∀ {A B} → isProp A → isProp B → isProp (A × B)
  ×pp-is-prop {A} {B} prpA prpB z z' = =proof
    z                  ==[ ×η⁻¹ z ] /
    prj1 z , prj2 z     ==[ =×char, (prpA _ _) (prpB _ _) ] /
    prj1 z' , prj2 z'   ==[ ×η z' ]∎
    z' ∎
  ×ss-is-set :  ∀ {A B} → isSet A → isSet B → isSet (A × B)
  ×ss-is-set Aset Bset {z} {z'} =
    eqv-prop-is-prop (×pp-is-prop Aset Bset)
                       (pj2 (=×eqv⁻¹ z z'))

  Σcp-is-contr : ∀ {A} {B : A → Set} → (Acntr : isContr A) → (∀ a → isProp (B a))
                   → B (pj1 Acntr) → isContr (Σ[ A ] B)
  Σcp-is-contr Acntr Bprps pf =
    (pj1 Acntr ,, pf)
    ,, λ z → =Σchar,, (pj2 Acntr (pj1 z)) (Bprps _ _ _)

  Σcc-is-contr : ∀ {A} {B : A → Set} → (Acntr : isContr A) → (∀ a → isContr (B a))
                   → isContr (Σ[ A ] B)
  Σcc-is-contr Acntr Bcntrs =
    Σcp-is-contr Acntr (λ a → isContr→isProp (Bcntrs a)) (pj1 (Bcntrs (pj1 Acntr)))

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

  -- mere injectivity (useful just for functions between sets)

  is-injective : {A B : Set} → (A → B) → Set
  is-injective f = ∀ {a a'} → f a == f a' → a == a'

  inj-set-is-idfull : ∀ {A B} {f : A → B} → isSet B → is-injective f → is-idfull f
  inj-set-is-idfull {A} {B} {f} Bset finj fa=fa' = finj fa=fa' ,, Bset (=ap f (finj fa=fa')) fa=fa'

  injective-ext : ∀ {A B} {f g : A → B} → (∀ x → f x == g x)
                     → is-injective f → is-injective g
  injective-ext eq finj {a} {a'} e = finj (eq a • e • eq a' ⁻¹)
  injective-cmp : {A B C : Set} {f : A → B} {g : B → C}
                     → is-injective f → is-injective g → is-injective (g ∘ f)
  injective-cmp finj ginj = finj ∘ ginj
  injective-tr : {A B C : Set} {f : A → B} {g : B → C} {h : A → C}
                     → (∀ {a} → g (f a) == h a) → is-injective h
                          → is-injective f
  injective-tr {f = f} {g} {h} tr hinj {a} {a'} fa=fa' =
    hinj (=proof h a          ==[ tr ⁻¹ ] /
                 g (f a)      ==[ =ap g fa=fa' ] /
                 g (f a')     ==[ tr ]∎
                 h a' ∎)
  invrt-is-injective : ∀ {A B} {f : A → B} → is-invrt f → is-injective f
  invrt-is-injective {A} {B} {f} finv eq = prj1 (pj2 finv) _ ⁻¹ • =ap (pj1 finv) eq • prj1 (pj2 finv) _
  isid-is-injective : ∀ {A} {f : A → A} → (∀ x → f x == x) → is-injective f
  isid-is-injective isid {a} {a'} e = isid a ⁻¹ • e • isid a'

  inj+surj-is-invrt : ∀ {A B} {f : A → B} → is-injective f → is-surjective f → is-invrt f
  inj+surj-is-invrt {f = f} fij fsj =
    (λ b → pj1 (fsj b))
    ,, ((λ a → fij (pj2 (fsj (f a)))) , (λ b → pj2 (fsj b)))

-- end of file
