{-# OPTIONS --without-K #-}

module Basic-Relations where
  open import Basic-Inductives



  -------------------------------------------------------------
  -- The reflexive and transitive closure of a binary relation
  ------------------------------------------------------------

  -- transitive closure
  data trans-closure {A : Set}(R : A → A → Set) : A → A → Set where
    tcl-in : ∀ {M N} → R M N → trans-closure R M N
    tcl-cnc : ∀ {M N L} → R M N → trans-closure R N L → trans-closure R M L

  -- the transitive closure is transitive
  trnclos-trans : {A : Set}(R : A → A → Set){M N L : A}
                    → trans-closure R M N → trans-closure R N L → trans-closure R M L
  trnclos-trans R (tcl-in MN) clNL =           tcl-cnc MN clNL
  trnclos-trans R (tcl-cnc MM' clM'N) clNL =   tcl-cnc MM' (trnclos-trans R clM'N clNL)

  -- and it is the minimal such
  trnclos-min : {A : Set}{R S : A → A → Set}
                  → (∀ {M N L} → S M N → S N L → S M L) → (∀ {M N} → R M N → S M N)
                      → ∀ {M N} → trans-closure R M N → S M N
  trnclos-min trnS RtoS {M} (tcl-in MN) =      RtoS MN
  trnclos-min trnS RtoS (tcl-cnc MM' clM'N) =  trnS (RtoS MM') (trnclos-min trnS RtoS clM'N)

  -- it is also functorial
  trnclos-fun : {A : Set}{R S : A → A → Set}
                  → (∀ {M N} → R M N → S M N)
                    → ∀ {M N} → trans-closure R M N → trans-closure S M N
  trnclos-fun {_} {_} {S} RtoS = trnclos-min (trnclos-trans S) (tcl-in ∘ RtoS)



  -- the reflexive and transitive closure
  data refl-trans-closure {A : Set}(R : A → A → Set) : A → A → Set where
    rtcl-rfl : ∀ M → refl-trans-closure R M M
    rtcl-cnc : ∀ {M N L} → R M N → refl-trans-closure R N L → refl-trans-closure R M L


  -- it contains the orignal relation
  rtcl-in : {A : Set}(R : A → A → Set){M N : A}
                    → R M N → refl-trans-closure R M N
  rtcl-in R {_} {N} MN  = rtcl-cnc MN (rtcl-rfl N)

  -- it composes also to the right
  rtcl-cnc' : {A : Set}(R : A → A → Set){M N L : A}
             → refl-trans-closure R M N → R N L → refl-trans-closure R M L
  rtcl-cnc' R (rtcl-rfl M) RMN = rtcl-in R RMN
  rtcl-cnc' R (rtcl-cnc MM' clRM'N) RNL = rtcl-cnc MM' (rtcl-cnc' R clRM'N RNL)
  
  -- the refl-trans closure is transitive
  rtcl-trans : {A : Set}(R : A → A → Set){M N L : A}
                    → refl-trans-closure R M N → refl-trans-closure R N L → refl-trans-closure R M L
  rtcl-trans R (rtcl-rfl M) clMN = clMN
  rtcl-trans R (rtcl-cnc MM' clM'N) clNL = rtcl-cnc MM' (rtcl-trans R clM'N clNL)

  -- and it is the minimal such
  rtcl-min : {A : Set}{R S : A → A → Set}
                  → (∀ M → S M M) → (∀ {M N L} → S M N → S N L → S M L)
                    → (∀ {M N} → R M N → S M N)
                      → ∀ {M N} → refl-trans-closure R M N → S M N
  rtcl-min rflS trnS inS {M} (rtcl-rfl M) =
    rflS M
  rtcl-min rflS trnS inS (rtcl-cnc r red) =
    trnS (inS r) (rtcl-min rflS trnS inS red)

  -- it is also functorial
  rtclos-fun : {A : Set}{R S : A → A → Set}
                  → (∀ {M N} → R M N → S M N)
                    → ∀ {M N} → refl-trans-closure R M N → refl-trans-closure S M N
  rtclos-fun {_} {_} {S} RtoS = rtcl-min rtcl-rfl (rtcl-trans S) (rtcl-in S ∘ RtoS)


  -- the symmetric closure
  data symm-closure {A : Set}(R : A → A → Set) : A → A → Set where
    scin : ∀ {M N} → R M N → symm-closure R M N
    scinv : ∀ {M N} → R M N → symm-closure R N M

  -- the reflexive, symmetric and transitive closure
  data rst-closure {A : Set}(R : A → A → Set) : A → A → Set where
    rstcl-rfl : ∀ M → rst-closure R M M
    rstcl-cnc : ∀ {M N L} → R M N → rst-closure R N L → rst-closure R M L
    rstcl-sym : ∀ {M N} → rst-closure R M N → rst-closure R N M

  -- it contains the orignal relation
  rstcl-in : {A : Set}(R : A → A → Set){M N : A}
                    → R M N → rst-closure R M N
  rstcl-in R {_} {N} MN = rstcl-cnc MN (rstcl-rfl N)

  -- it is transitive
  rstcl-tran : ∀ {A : Set}(R : A → A → Set){M N L}
                 → rst-closure R M N → rst-closure R N L → rst-closure R M L
  rstcl-tran R clMN (rstcl-rfl _) =
    clMN
  rstcl-tran R (rstcl-rfl _) (rstcl-cnc MM' clM'L) =
    rstcl-cnc MM' clM'L
  rstcl-tran R (rstcl-cnc MM' clM'N) (rstcl-cnc NN' clN'L) =
    rstcl-cnc MM' (rstcl-tran R clM'N (rstcl-cnc NN' clN'L))
  rstcl-tran R (rstcl-sym clNM) (rstcl-cnc NN' clN'L) =
    rstcl-sym (rstcl-tran R (rstcl-sym (rstcl-cnc NN' clN'L)) clNM)
  rstcl-tran R (rstcl-rfl _) (rstcl-sym clLM) =
    rstcl-sym clLM
  rstcl-tran R (rstcl-cnc MM' clM'N) (rstcl-sym clLN) =
    rstcl-cnc MM' (rstcl-tran R clM'N (rstcl-sym clLN))
  rstcl-tran R (rstcl-sym clNM) (rstcl-sym clLN) =
    rstcl-sym (rstcl-tran R clLN clNM)

  -- t composes also to the right
  rstcl-cnc' : ∀ {A : Set}(R : A → A → Set){M N L}
             → rst-closure R M N → R N L → rst-closure R M L
  rstcl-cnc' R clMN NL = rstcl-tran R clMN (rstcl-in R NL)

  -- and it is the minimal such
  rstcl-is-min : {A : Set}{R S : A → A → Set}
                  → (∀ M → S M M)
                  → (∀ {M N} → S M N → S N M)
                  → (∀ {M N L} → S M N → S N L → S M L)
                    → (∀ {M N} → R M N → S M N)
                      → ∀ {M N} → rst-closure R M N → S M N
  rstcl-is-min rflS symS trnS inS (rstcl-rfl _) =
    rflS _
  rstcl-is-min rflS symS trnS inS (rstcl-cnc MM' clM'N) =
    trnS (inS MM') (rstcl-is-min rflS symS trnS inS clM'N)
  rstcl-is-min rflS symS trnS inS (rstcl-sym clNM) =
    symS (rstcl-is-min rflS symS trnS inS clNM)

  -- it is also functorial
  rstcl-is-fun : {A : Set}{R S : A → A → Set}
                  → (∀ {M N} → R M N → S M N)
                    → ∀ {M N} → rst-closure R M N → rst-closure S M N
  rstcl-is-fun {_} {R} {S} RtoS =
    rstcl-is-min rstcl-rfl
                 rstcl-sym
                 (rstcl-tran S)
                 (rstcl-in S ∘ RtoS) 

  -- it contains the reflexive and transitive closure

  rt-to-rst-closure : {A : Set}(R : A → A → Set)
                         → ∀ {M N} → refl-trans-closure R M N → rst-closure R M N
  rt-to-rst-closure R = rtcl-min rstcl-rfl (rstcl-tran R) (rstcl-in R) 


{-
  -- it is the symmetric closure of the reflexive and transititve closure
  srt-closure : {A : Set}(R : A → A → Set) → A → A → Set
  srt-closure R = symm-closure (refl-trans-closure R)

  srtcl-tran : ∀ {A : Set}(R : A → A → Set){M N L}
                 → srt-closure R M N → srt-closure R N L → srt-closure R M L
  srtcl-tran R (scin clMN) (scin clNL) =
    scin (rtclos-trans R clMN clNL)
  srtcl-tran R (scin (tcrfl _)) (scinv clLM) = scinv clLM
  srtcl-tran R (scin (tccnc clMN' N'N)) (scinv clLN) =
    {!!}
    --srtcl-tran R (scin clMN') (srtcl-tran R (scin (rtclos-in R N'N)) (scinv clLN))
  srtcl-tran R (scinv clNM) (scin (tcrfl _)) = {!!}
  srtcl-tran R (scinv clNM) (scin (tccnc clNL' L'L)) =
    srtcl-tran R (srtcl-tran R (scinv clNM) (scin clNL')) (scin (rtclos-in R L'L))
  srtcl-tran R (scinv clNM) (scinv clLN) =
    scinv (rtclos-trans R clLN clNM)
-}


  ----------------------------------------------------------
  -- lists up to the order of their elements (= multi-sets)
  ----------------------------------------------------------

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
  _≡⋆_ = trans-closure _≡_
  ≡⋆rfl : {A : Set} → {α : List A} → α ≡⋆ α
  ≡⋆rfl = tcl-in ≡rfl
  ≡⋆cnc : {A : Set} → {α β γ : List A} → α ≡ β → β ≡⋆ γ → α ≡⋆ γ
  ≡⋆cnc = tcl-cnc
  ≡⋆in : {A : Set} → {α β : List A} → α ≡ β  → α ≡⋆ β
  ≡⋆in = tcl-in
  ≡⋆tr : {A : Set} → {α β γ : List A} → α ≡⋆ β → β ≡⋆ γ → α ≡⋆ γ
  ≡⋆tr = trnclos-trans _≡_

  ≡⋆ext : {A : Set} → {α β : List A} → (a : A) → α ≡⋆ β → a ∣ α ≡⋆ a ∣ β
  ≡⋆ext a (tcl-in eqv) =                   ≡⋆in (≡cnc a eqv)
  ≡⋆ext a (tcl-cnc {α} {α'} eqv cl) =      ≡⋆cnc (≡cnc a eqv) (≡⋆ext a cl)

  ≡swpcnc : {A : Set} → {α α' : List A} → {a b : A} → α ≡ b ∣ α' → a ∣ α ≡⋆ b ∣ a ∣ α'
  ≡swpcnc {a = a} {b} (≡cnc b eqv) =    tcl-in (≡swp a b eqv)
  ≡swpcnc {a = a} {b} (≡swp c b eqv) =  tcl-cnc (≡cnc a (≡swp c b eqv)) (≡swpcnc {a = a} {b} ≡rfl)

  ≡⋆swpcnc : {A : Set} → {α α' : List A} → {a b : A} → α ≡⋆ b ∣ α' → a ∣ α ≡⋆ b ∣ a ∣ α'
  ≡⋆swpcnc {a = a} {b} (tcl-in eqv) =               ≡swpcnc eqv
  ≡⋆swpcnc {a = a} {b} (tcl-cnc {α} {β} eqv cl) =   ≡⋆cnc (≡cnc a eqv) (≡⋆swpcnc {a = a} cl)

  ≡-∋ : {A : Set} → {α α' : List A} → {a : A} → α ≡ α' → α ∋ a → α' ∋ a
  ≡-∋ (≡cnc a eqv) here = here
  ≡-∋ (≡cnc c eqv) (there inp) = there (≡-∋ eqv inp)
  ≡-∋ (≡swp a b eqv) here = there here
  ≡-∋ (≡swp c a eqv) (there here) = here
  ≡-∋ (≡swp c b eqv) (there (there inp)) = there (there (≡-∋ eqv inp))

  ≡⋆-∋ : {A : Set} → {α α' : List A} → {a : A} → α ≡⋆ α' → α ∋ a → α' ∋ a
  ≡⋆-∋ (tcl-in eqv) inp = ≡-∋ eqv inp
  ≡⋆-∋ (tcl-cnc {α} {β} eqv cl) inp = ≡⋆-∋ cl (≡-∋ eqv inp)

-- end of file
