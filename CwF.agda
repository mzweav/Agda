module CwF where

open import prelude
open import Level
open import Categories.Category
open import Categories.Functor renaming (_≡_ to _==_; _∘_ to comp)
open import Categories.Fam 
open import Categories.Presheaf
open import Categories.Support.PropositionalEquality

import Categories.Object.Terminal as Terminal


record CwF {o ℓ e a b : Level}
       (C : Category o ℓ e)
       (F : Presheaf C (Fam a b))
       : Set (suc (o ⊔ ℓ ⊔ e ⊔ a ⊔ b)) where

  open Category C renaming (_≡_ to _≅_)
  open Terminal C
  open Functor F
  open Fam renaming (_≡_ to _==_; _∘_ to comp)

  module C = Category C
  module F = Functor F


  Ctx = C.Obj


  Subst = C._⇒_


  Id : {Γ : Ctx} → Subst Γ Γ
  Id = C.id


  Ty : Ctx → Set _
  Ty Γ = U (F.F₀ Γ)


  Ter : (Γ : Ctx) → Ty Γ → Set _
  Ter Γ A = (T (F.F₀ Γ)) A


  TApp : {Δ Γ : Ctx}
         (σ   : Subst Δ Γ)
         (A   : Ty Γ)
         → ---------------
         Ty Δ
         
  TApp σ A = (Hom.f (F.F₁ σ)) A


  tApp : {Δ Γ : Ctx}
         (σ   : Subst Δ Γ)
         {A   : Ty Γ}
         (a   : Ter Γ A)
         → ---------------
         Ter Δ (TApp σ A)
         
  tApp σ {A} a = (Hom.φ (F.F₁ σ)) A a


  field -- Equalities that should be derivable
    TIdEq     : {Γ     : Ctx}
                {A     : Ty Γ}
                → -------------------------------------------------
                TApp Id A ≡ A

    TAppEq    : {Δ Γ Θ : Ctx}
                {σ     : Subst Δ Γ}               
                {τ     : Subst Θ Δ}
                {A     : Ty Γ}
                → -------------------------------------------------
                TApp τ (TApp σ A) ≡ TApp (σ ∘ τ) A

    TAppAp    : {Δ Γ   : Ctx}
                {σ     : Subst Δ Γ}               
                {τ     : Subst Δ Γ}
                {A     : Ty Γ}
                (p     : σ ≅ τ)
                → -------------------------------------------------
                TApp σ A ≡ TApp τ A

    tIdEq     : {Γ     : Ctx}
                {A     : Ty Γ}
                {a     : Ter Γ A}
                → -------------------------------------------------
                tApp Id a
                  ≡[ ap (Ter Γ) TIdEq ]≡
                a

    tAppEq    : {Θ Δ Γ : Ctx}
                {σ     : Subst Δ Γ}               
                {τ     : Subst Θ Δ}
                {A     : Ty Γ}
                {a     : Ter Γ A}
                → -------------------------------------------------
                tApp τ (tApp σ a)
                  ≡[ ap (Ter Θ) TAppEq ]≡
                tApp (σ ∘ τ) a

    tAppAp    : {Δ Γ   : Ctx}
                {σ     : Subst Δ Γ}               
                {τ     : Subst Δ Γ}
                {A     : Ty Γ}
                {a     : Ter Γ A}              
                (p     : σ ≅ τ)
                → -------------------------------------------------
                tApp σ a
                  ≡[ ap (Ter Δ) (TAppAp p) ]≡
                tApp τ a

  field 
    []        : Terminal

    ctxExt    : (Γ : Ctx)
                (A : Ty Γ)
                → -------------------------------------------------
                Ctx

    p         : {Γ : Ctx}
                {A : Ty Γ}
                → -------------------------------------------------
                Subst (ctxExt Γ A) Γ

    q         : {Γ : Ctx}
                {A : Ty Γ}
                → -------------------------------------------------
                Ter (ctxExt Γ A) (TApp (p {Γ} {A}) A)

    uSubst    : {Δ Γ : Ctx}
                (σ   : Subst Δ Γ)
                {A   : Ty Γ}
                (a   : Ter Δ (TApp σ A))
                → -------------------------------------------------
                Subst Δ (ctxExt Γ A)

    uEq₁      : {Δ Γ : Ctx}
                (σ   : Subst Δ Γ)
                {A   : Ty Γ}
                (a   : Ter Δ (TApp σ A))
                → -------------------------------------------------
                p ∘ (uSubst σ a) ≅ σ

    uEq₂      : {Γ : Ctx}
                {A : Ty Γ}
                → -------------------------------------------------
                uSubst (p {Γ} {A}) (q {Γ} {A}) ≅ Id

    uEq₃      : {Δ Γ Θ : Ctx}
                (σ     : Subst Δ Γ)
                {A     : Ty Γ}
                (a     : Ter Δ (TApp σ A))
                (τ     : Subst Θ Δ)
                → -------------------------------------------------
                (uSubst σ a) ∘ τ
                  ≅
                uSubst (σ ∘ τ) (coe (ap (Ter Θ) TAppEq) (tApp τ a))

    uEq₄      : {Δ Γ : Ctx}
                (σ   : Subst Δ Γ)
                {A   : Ty Γ}
                (a   : Ter Δ (TApp σ A))
                → -------------------------------------------------
                tApp (uSubst σ a) q
                  ≡[ ap (Ter Δ) (trans TAppEq (TAppAp (uEq₁ σ a))) ]≡
                a
