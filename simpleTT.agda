
import lambda-calc

module simpleTT (A : Set) where
open lambda-calc public

infixl 100 _⇒_
data Ty : Set where
  atom : A → Ty
  _⇒_ : Ty → Ty → Ty


infixl 80 _,_
infixl 70 _,,_

data Ctx : ℕ → Set where
  [] : Ctx 0
  _,_ : {n : ℕ} → Ctx n → Ty → Ctx (suc n)

_,,_ : {n m : ℕ} → Ctx n → Ctx m → Ctx (n + m)
Γ ,, [] = Γ
Γ ,, Θ , T = (Γ ,, Θ) , T


data JdgDer : {n : ℕ} → Ctx n → ΛTerm → Ty → Set where
  Var : {n : ℕ}(Γ : Ctx n)(T : Ty) → JdgDer (Γ , T) (var (suc n)) T
  --{n m : ℕ}(Γ : Ctx n)(Θ : Ctx m)(T : Ty) → JdgDer (Γ , T ,, Θ) (var (suc n)) T
  Weak : {n : ℕ}{Γ : Ctx n}{M : ΛTerm}(S {T} : Ty) → JdgDer Γ M T → JdgDer (Γ , S) M T
  Abs : {n : ℕ}{Γ : Ctx n}{M : ΛTerm}{S T : Ty}
           → JdgDer (Γ , S) M T → JdgDer Γ (lam (suc n) M) (S ⇒ T)
  App : {n : ℕ}{Γ : Ctx n}{M N : ΛTerm}{S T : Ty}
           → JdgDer Γ M (S ⇒ T) → JdgDer Γ N S → JdgDer Γ (app M N) T

cur : {n : ℕ}{Γ : Ctx n}{S T : Ty}{M : ΛTerm}
           → JdgDer (Γ , S) M T → JdgDer Γ (lam (suc n) M) (S ⇒ T)
cur {n} {Γ} {S} {T} {M} = Abs {n} {Γ} {M} {S} {T}

uncur : {n : ℕ}{Γ : Ctx n}{S T : Ty}{M : ΛTerm}
           → JdgDer Γ M (S ⇒ T) → JdgDer (Γ , S) (app M (var (suc n))) T
uncur {n} {Γ} {S} {T} {M} pf = App {suc n} {Γ , S} {M} {var (suc n)} {S} {T} (Weak S pf) (Var Γ S)

{-
swap-aux : {n : ℕ}{Γ : Ctx n}{R S T : Ty}{M : ΛTerm}
               → JdgDer (Γ , R , S) M T → JdgDer (Γ , S , R) M T
swap-aux pf = {!pf!}

swap : {n m : ℕ}{Γ : Ctx n}{Θ : Ctx m}{S T : Ty}{M : ΛTerm}
          → JdgDer (Γ , S ,, Θ) M T → JdgDer (Γ ,, Θ , S) M T
swap {Γ = Γ} {[]} {S} {T} {M} pf = pf
swap {Γ = Γ} {Θ , R} {S} {T} {M} pf = {!!}
-}
