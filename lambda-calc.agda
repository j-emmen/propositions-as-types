import Agda.Builtin.Nat

module lambda-calc where
open Agda.Builtin.Nat renaming (Nat to ℕ; _+_ to _l+_) public
infixr 6 _+_
_+_ : ℕ → ℕ → ℕ
n + 0 = n
n + suc m = suc (n + m)

data ΛTerm : Set where
  var : ℕ → ΛTerm
  lam : ℕ  → ΛTerm → ΛTerm
  app : ΛTerm → ΛTerm → ΛTerm
