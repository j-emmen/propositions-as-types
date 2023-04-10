
module props-as-types {A : Set} where
  open import Basic-Inductives
  import simpleTT
  import IPL-implic-frag
  module NJ = IPL-implic-frag A
  module TT = simpleTT A
  open TT hiding (atm)
  open NJ hiding (atm)
 

  u₂ : Ty → WFF
  u₂ (TT.atm a) = NJ.atm a
  u₂ (T₁ ⇒ T₂) = (u₂ T₁) ⊃ (u₂ T₂)
  u₂' : WFF → Ty
  u₂' (NJ.atm a) = TT.atm a
  u₂' (P₁ ⊃ P₂) = (u₂' P₁) ⇒ (u₂' P₂)

  u₁ : Ctx → Prem
  u₁ [] = []
  u₁ (T ∣ Γ) = (u₂ T) ∣  (u₁ Γ)
  u₁' : (Δ : Prem) → Ctx
  u₁' [] = []
  u₁' (P ∣ Δ) = (u₂' P) ∣ (u₁' Δ)

  u∋ : {Γ : Ctx}{i : Fin (len Γ)}{T : Ty}
         → Γ ∋ i ∶ T → (u₁ Γ) ∋ (u₂ T)
  u∋ here = here
  u∋ (there inc) = there (u∋ inc)

  pos' : {Δ : Prem}{P : WFF}
            → Δ ∋ P → Fin (len (u₁' Δ))
  pos' here = fz
  pos' (there inp) = fs (pos' inp)

  u'∋ : {Δ : Prem}{P : WFF}
         → (inp : Δ ∋ P) → (u₁' Δ) ∋ (pos' inp) ∶ (u₂' P)
  u'∋ here = here
  u'∋ (there inp) = there (u'∋ inp)

  -- from derivations in TT to derivations in NJ
  u : {Γ : Ctx}{M : Trm (len Γ)}{T : Ty}
         → Γ ⊢ M ∶ T → (u₁ Γ) ⊢ (u₂ T)
  u (⊢-var inc) = Ass (u∋ inc)
  u (⊢-abs derTT) = →I (u derTT)
  u (⊢-app derTT₁ derTT₂) = →E (u derTT₁) (u derTT₂)

  -- from derivations in NJ to derivations in TT
  t : {Δ : Prem}{P : WFF} → Δ ⊢ P → Trm (len (u₁' Δ))
  t (Ass inp) = var (pos' inp)
  t (→I derNJ) = lam (t derNJ)
  t (→E derNJ₁ derNJ₂) = app (t derNJ₁) (t derNJ₂)

  u' : {Δ : Prem}{P : WFF}
          → (derNJ : Δ ⊢ P) → (u₁' Δ) ⊢ (t derNJ) ∶ (u₂' P)
  u' (Ass inp) = ⊢-var (u'∋ inp)
  u' (→I derNJ) = ⊢-abs (u' derNJ)
  u' (→E derNJ₁ derNJ₂) = ⊢-app (u' derNJ₁) (u' derNJ₂)

-- end file
