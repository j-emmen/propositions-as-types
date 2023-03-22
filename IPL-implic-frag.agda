import Agda.Builtin.Nat

module IPL-implic-frag (A : Set) where
open Agda.Builtin.Nat renaming (Nat to ℕ) public

data WFF : Set where
  atom : A → WFF
  _⊃_ : WFF → WFF → WFF

infixl 80 _,_
infixl 70 _,,_

data Prem : Set where
  [] : Prem
  _,_ : Prem → WFF → Prem

_,,_ : Prem → Prem → Prem
Δ ,, [] = Δ
Δ ,, Ξ , P = (Δ ,, Ξ) , P

len : Prem → ℕ
len [] = 0
len (Δ , P) = suc (len Δ)

record propJdg : Set where
  field
    prem : Prem
    prop : WFF

infix 30 _⊢_
_⊢_ : Prem → WFF → propJdg
Δ ⊢ P = record
  { prem = Δ
  ; prop = P
  }

data JdgDer : (Δ : Prem)(P : WFF) → Set where
  -- pure calculus when the following line is commented out
  --atm : (Δ : Prem) → (a : A) → JdgDer Δ (atom a)
  Ass : (Δ : Prem) → (P : WFF) → JdgDer (Δ , P) P
  --(Δ Ξ : Prem) → (P : WFF) → JdgDer (Δ , P ,, Ξ) P
  -- have to use weakening (and not the line above),
  -- otherwise Agda does not seem to do induction for me.
  Weak : {Δ : Prem}({P} R : WFF) → JdgDer Δ P → JdgDer (Δ , R) P
  →I : (Δ : Prem) → (P Q : WFF) → JdgDer (Δ , P) Q → JdgDer Δ (P ⊃ Q)
  →E : (Δ : Prem) → (P Q : WFF) → JdgDer Δ (P ⊃ Q) → JdgDer Δ P → JdgDer Δ Q

cur : {Δ : Prem}{P Q : WFF}
           → JdgDer (Δ , P) Q → JdgDer Δ (P ⊃ Q)
cur {Δ} {P} {Q} = →I Δ P Q

uncur : {Δ : Prem}{P Q : WFF}
           → JdgDer Δ (P ⊃ Q) → JdgDer (Δ , P) Q
uncur {Δ} {P} {Q} pf = →E (Δ , P) P Q (Weak P pf) (Ass Δ P)

Wk :  ({Δ} Ξ : Prem){P : WFF}
               → JdgDer Δ P → JdgDer (Δ ,, Ξ) P
Wk {Δ} [] {P} pf = pf
Wk {Δ} (Ξ , U) {P} pf = Weak U (Wk Ξ pf)

Assₚ :  (Δ Ξ : Prem)(P : WFF) → JdgDer (Δ , P ,, Ξ) P
Assₚ Δ Ξ P = Wk Ξ (Ass Δ P)

swap-aux : {Δ Ξ : Prem}{P Q R : WFF}
               → JdgDer (Δ , P , Q ,, Ξ) R → JdgDer (Δ , Q , P ,, Ξ) R
swap-aux {Δ} {[]} {P} {Q} {Q} (Ass (Δ , P) Q) =
  Weak P (Ass Δ Q)
swap-aux {Δ} {[]} {P} {Q} {R} (Weak Q pf) =
  uncur (Weak Q (cur pf))
swap-aux {Δ} {[]} {P} {Q} {(P₁ ⊃ Q₁)} (→I (Δ , P , Q) P₁ Q₁ pf₁) =
  →I (Δ , Q , P) _ _ (swap-aux {Δ} {[] , P₁} {P} {Q}  pf₁)
swap-aux {Δ} {[]} {P} {Q} {R} (→E (Δ , P , Q) P₁ R pf₁ pf₂) =
  →E (Δ , Q , P) P₁ R (swap-aux {Δ} {[]} {P} {Q} pf₁) (swap-aux {Δ} {[]} {P} {Q} pf₂)
swap-aux {Δ} {Ξ , U} {P} {Q} {U} (Ass _ U) =
  Ass (Δ , Q , P ,, Ξ) U
swap-aux {Δ} {Ξ , U} {P} {Q} {R} (Weak U pf) =
  Weak U (swap-aux pf)
swap-aux {Δ} {Ξ , U} {P} {Q} {(P₁ ⊃ Q₁)} (→I (_ , U) P₁ Q₁ pf₁) =
  →I (Δ , Q , P ,, Ξ , U) P₁ Q₁ (swap-aux {Δ} {Ξ , U , P₁} {P} {Q} pf₁)
swap-aux {Δ} {Ξ , U} {P} {Q} {R} (→E (_ , U) P₁ .R pf₁ pf₂) =
  →E (Δ , Q , P ,, Ξ , U) P₁ R (swap-aux {Δ} {Ξ , U} {P} {Q} {P₁ ⊃ R} pf₁)
                                (swap-aux {Δ} {Ξ , U} {P} {Q} {P₁} pf₂)

-- Contraction is admissible:
Cntrₚ : {Δ Ξ : Prem}(P {R} : WFF)
               → JdgDer (Δ , P , P ,, Ξ) R → JdgDer (Δ , P ,, Ξ) R
Cntrₚ {Δ} {[]} P {P} (Ass (Δ , P) P) =
  Ass Δ P
Cntrₚ {Δ} {[]} P {R} (Weak P pf) =
  pf
Cntrₚ {Δ} {[]} P {(P₁ ⊃ Q)} (→I (Δ , P , P) P₁ Q pf) =
  cur (Cntrₚ {Δ} {[] , P₁} P pf)
Cntrₚ {Δ} {[]} P {R} (→E (Δ , P , P) P₁ R pf₁ pf₂) =
  →E (Δ , P) _ _ (Cntrₚ {Δ} {[]} P pf₁) (Cntrₚ {Δ} {[]} P pf₂)
Cntrₚ {Δ} {Ξ , U} P {U} (Ass _ U) =
  Ass (Δ , P ,, Ξ) U
Cntrₚ {Δ} {Ξ , U} P {R} (Weak U pf) =
  Weak U (Cntrₚ P pf)
Cntrₚ {Δ} {Ξ , U} P {(P₁ ⊃ Q)} (→I (_ , U) P₁ Q pf) =
  cur (Cntrₚ {Δ} {Ξ , U , P₁} P pf)
Cntrₚ {Δ} {Ξ , U} P {R} (→E (_ , U) P₁ R pf₁ pf₂) =
  →E ((Δ , P ,, Ξ) , U) _ _ (Cntrₚ {Δ} {Ξ , U} P pf₁) (Cntrₚ {Δ} {Ξ , U} P pf₂)
