{-# OPTIONS --show-implicit #-}

import IPL-implic-frag
import simpleTT
import lambda-calc

module props-as-types {A : Set} where
  module NJ = IPL-implic-frag A
  module TT = simpleTT A
  open lambda-calc public

  u₂ : TT.Ty → NJ.WFF
  u₂ (TT.atom a) = NJ.atom a
  u₂ (S TT.⇒ T) = (u₂ S) NJ.⊃ (u₂ T)
  u₂' : NJ.WFF → TT.Ty
  u₂' (NJ.atom a) = TT.atom a
  u₂' (P NJ.⊃ Q) = (u₂' P) TT.⇒ (u₂' Q)

  u₁ : {n : ℕ} → TT.Ctx n → NJ.Prem
  u₁ TT.[] = NJ.[]
  u₁ (Γ TT., T) = (u₁ Γ) NJ., (u₂ T)

  u₁' : (Δ : NJ.Prem) → TT.Ctx (NJ.len Δ)
  u₁' NJ.[] = TT.[]
  u₁' (Δ NJ., P) = (u₁' Δ) TT., (u₂' P)

  u : {n : ℕ}{Γ : TT.Ctx n}{M : ΛTerm}{T : TT.Ty} → TT.JdgDer Γ M T → NJ.JdgDer (u₁ Γ) (u₂ T)
  u (TT.Var Γ T) = NJ.Ass (u₁ Γ) (u₂ T)
  u (TT.Weak S pf) = NJ.Weak (u₂ S) (u pf)
  u (TT.Abs pf) = NJ.cur (u pf)
  u (TT.App pf₁ pf₂) = NJ.→E _ _ _ (u pf₁) (u pf₂)

  t : {Δ : NJ.Prem}{P : NJ.WFF} → NJ.JdgDer Δ P → ΛTerm
  t (NJ.Ass Δ P) = var (TT.suc (NJ.len Δ))
  t (NJ.Weak R pf) = t pf
  t (NJ.→I Δ P Q pf) = lam (TT.suc (NJ.len Δ)) (t {Δ NJ., P} {Q} pf)
  t (NJ.→E Δ Q P pf₁ pf₂) = app (t {Δ} {Q NJ.⊃ P} pf₁) (t {Δ} {Q} pf₂)
  -- if implicit arguments in def of t above are explcitly given,
  -- then t does not β-reduce to canonical forms ('lam' and 'app') where it should.
  
  u' : {Δ : NJ.Prem}{P : NJ.WFF} → (pf : NJ.JdgDer Δ P) → TT.JdgDer (u₁' Δ) (t pf) (u₂' P)
  u' (NJ.Ass Δ P) = TT.Var (u₁' Δ) (u₂' P)
  u' (NJ.Weak R pf) = TT.Weak (u₂' R) (u' pf)
  u' (NJ.→I Δ P Q pf) = TT.Abs (u' pf)
  u' (NJ.→E Δ P₁ P pf₁ pf₂) = TT.App (u' pf₁) (u' pf₂)
 
  -- u and u' form equivalence of types? 
