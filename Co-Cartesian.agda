{-# OPTIONS --cubical --safe #-}

open import Level using (Level) renaming (suc to ℓ-suc)
open import Function using (id; _∘_)
import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_])

open import CubicalIdentity using (_≡_; refl; sym; trans; cong; →-≡)
open CubicalIdentity.≡-Reasoning

open import Category

--*
{-
  This module introduces the notion of co-Cartesian category. 
-
  A co-Cartesian Category enriches the underlying Category by Coproducts 
  (_⊎_, inl, inr) with copairing [_,_] and the corresponding laws. 
-}
--*

module Co-Cartesian where

private
  variable
    ℓ : Level
    Ob : Set (ℓ-suc ℓ)

record Co-Cartesian (C : Category {ℓ} Ob) : Set (ℓ-suc ℓ) where
  open Category.Category C public
  
  infix  2 _⊎_

  field
    -- Coproducts
    _⊎_ : Obj → Obj → Obj
    
    -- Injections
    inl : ∀ {A B : Obj} → (A ➔ A ⊎ B)
    inr : ∀ {A B : Obj} → (B ➔ A ⊎ B)
    
    -- Copairing
    [_,_] : ∀ {A B C : Obj} → (A ➔ C) → (B ➔ C) → (A ⊎ B ➔ C)

    -- Coproduct laws
    []-inl : ∀ {A B C : Obj} {f : A ➔ C} {g : B ➔ C} → [ f , g ] ⊚ inl ≡ f
    []-inr : ∀ {A B C : Obj} {f : A ➔ C} {g : B ➔ C} → [ f , g ] ⊚ inr ≡ g
    [inl,inr] : ∀ {A B : Obj} → [ inl , inr ] ≡ idm {A ⊎ B}
    ⊚-distrib-[] : ∀ {A B C D : Obj} {f : A ➔ C} {g : B ➔ C} {h : C ➔ D}
                   → h ⊚ [ f , g ] ≡ [ h ⊚ f , h ⊚ g ]
  
  _⊕_ : ∀ {A B C D : Obj} → (A ➔ C) → (B ➔ D) → (A ⊎ B ➔ C ⊎ D)
  f ⊕ g = [ inl ⊚ f , inr ⊚ g ]

  ⊕-inl : ∀ {A B C D : Obj} {f : A ➔ C} {g : C ➔ D}
    → (f ⊕ g) ⊚ inl ≡ inl ⊚ f
  ⊕-inl = []-inl

  ⊕-inr : ∀ {A B C D : Obj} {f : A ➔ C} {g : C ➔ D}
    → (f ⊕ g) ⊚ inr ≡ inr ⊚ g
  ⊕-inr = []-inr

  ⊎-destruct : ∀ {A B C} {f g : A ⊎ B ➔ C}
    → f ⊚ inl ≡ g ⊚ inl → f ⊚ inr ≡ g ⊚ inr → f ≡ g
  ⊎-destruct{_}{_}{_}{f}{g} p q =
      begin
        f
      ≡˘⟨ ⊚-unitʳ ⟩
        f ⊚ idm
      ≡˘⟨ cong ( _⊚_ f) [inl,inr] ⟩
        f ⊚ [ inl , inr ]
      ≡⟨ ⊚-distrib-[] ⟩
        [ f ⊚ inl , f ⊚ inr ] 
      ≡⟨ cong ([_, f ⊚ inr ] ) p ⟩
        [ g ⊚ inl , f ⊚ inr ]
      ≡⟨ cong ([ g ⊚ inl ,_] ) q ⟩
        [ g ⊚ inl , g ⊚ inr ]
      ≡˘⟨ ⊚-distrib-[] ⟩
        g ⊚ [ inl , inr ]
      ≡⟨ cong ( _⊚_ g) [inl,inr] ⟩
        g ⊚ idm
      ≡⟨ ⊚-unitʳ ⟩
        g
    ∎

  []-destruct : ∀ {A B C} {f f′ : A ➔ C}{g g′ : B ➔ C}
    → f ≡ f′ → g ≡ g′ → [ f , g ] ≡ [ f′ , g′ ]
  []-destruct{_}{_}{_}{f}{f′}{g}{g′} f≡f′ g≡g′ =
    ⊎-destruct
      (trans []-inl (trans f≡f′ (sym []-inl)))
      (trans []-inr (trans g≡g′ (sym []-inr)))

  []-cong₁ : ∀ {A B C} {f f′ : A ➔ C}{g : B ➔ C}
    → f ≡ f′ → [ f , g ] ≡ [ f′ , g ]
  []-cong₁{_}{_}{_}{f}{f′}{g} f≡f′ = []-destruct f≡f′ refl

  []-cong₂ : ∀ {A B C} {f : A ➔ C}{g g′ : B ➔ C}
    → g ≡ g′ → [ f , g ] ≡ [ f , g′ ]
  []-cong₂{_}{_}{_}{f}{g}{g′} g≡g′ = []-destruct refl g≡g′
  
  []-⊕ : ∀ {A B C A' B' : Obj} {f : A ➔ C}{g : B ➔ C} {f' : A' ➔ A}{g' : B' ➔ B} →
     [ f , g ] ⊚ (f' ⊕ g') ≡ [ f ⊚ f' , g ⊚ g' ]
  []-⊕{f = f}{g = g}{f' = f'}{g' = g'} =
    trans ⊚-distrib-[] ([]-destruct
        (trans ⊚-assoc (cong (_⊚ f') []-inl))
        (trans ⊚-assoc (cong (_⊚ g') []-inr)))

  ⊕-⊕ : ∀ {A B C D E F : Obj} {f : A ➔ B}{g : C ➔ D} {f' : B ➔ E}{g' : D ➔ F} →
     (f' ⊕ g' ) ⊚ (f ⊕ g) ≡ (f' ⊚ f) ⊕ (g' ⊚ g)
  ⊕-⊕ {f}{g}{f′}{g′} = trans []-⊕ ([]-destruct (sym ⊚-assoc) (sym ⊚-assoc)) 

  ⊕-cong : ∀ {A B C D : Obj} {f : A ➔ B} {f′ : A ➔ B} {g : C ➔ D} {g′ : C ➔ D} 
     → f ≡ f′ → g ≡ g′ → f ⊕ g ≡ f′ ⊕ g′
  ⊕-cong{f = f}{f′ = f′}{g = g}{g′ = g′} f≡f′ g≡g′ =
    trans (cong (_⊕ g) f≡f′) (cong (_⊕_ f′) g≡g′)  

  ⊕-cong₁ : ∀ {A B C D : Obj} {f : A ➔ B} {f′ : A ➔ B} {g : C ➔ D}  
     → f ≡ f′ → f ⊕ g ≡ f′ ⊕ g

  ⊕-cong₁ f≡f′ = ⊕-cong f≡f′ refl
  
  ⊕-cong₂ :  ∀ {A B C D : Obj} {f : A ➔ B} {g : C ➔ D} {g′ : C ➔ D} 
     → g ≡ g′ → f ⊕ g ≡ f ⊕ g′

  ⊕-cong₂ g≡g′ = ⊕-cong refl g≡g′


  ⊎-assocˡʳ : ∀ {A B C : Obj} → (A ⊎ B) ⊎ C ➔ A ⊎ (B ⊎ C)
  ⊎-assocˡʳ = [ idm ⊕ inl , inr ⊚ inr ]
  
  ⊎-assocʳˡ : ∀ {A B C : Obj} → A ⊎ (B ⊎ C) ➔ (A ⊎ B) ⊎ C
  ⊎-assocʳˡ = [ inl ⊚ inl , inr ⊕ idm ]

  swap : ∀ {A B : Obj} → A ⊎ B ➔ B ⊎ A
  swap{A}{B} = [ inr{B}{A} , inl{B}{A} ]

  []-swap : ∀ {A B C : Obj}  {f : A ➔ C} {g : B ➔ C}
    → [ f , g ] ⊚ swap ≡ [ g , f ]
  []-swap{f}{g} = trans ⊚-distrib-[] ([]-destruct []-inr []-inl)  

  swap-swap : ∀ {A B : Obj} → swap{A}{B} ⊚ swap ≡ idm
  swap-swap = trans []-swap [inl,inr]

  []-assocʳˡ : ∀ {A B C D : Obj} {f : A ➔ D} {g : B ➔ D} {h : C ➔ D}
    → [ f , [ g , h ] ] ⊚ ⊎-assocˡʳ ≡ [ [ f , g ] , h ]
  []-assocʳˡ {f = f} {g = g} {h = h} =
    trans ⊚-distrib-[] ([]-destruct (trans ⊚-distrib-[] ([]-destruct eq₁ eq₂)) eq₃)
         where
           eq₁ : [ f , [ g , h ] ] ⊚ (inl ⊚ idm) ≡ f
           eq₂ : [ f , [ g , h ] ] ⊚ (inr ⊚ inl) ≡ g
           eq₃ : [ f , [ g , h ] ] ⊚ (inr ⊚ inr) ≡ h

           eq₁ = trans ⊚-assoc (trans (cong (_⊚ idm) []-inl)  ⊚-unitʳ)
           eq₂ = trans ⊚-assoc (trans (cong (_⊚ inl) []-inr) []-inl)
           eq₃ = trans ⊚-assoc (trans (cong (_⊚ inr) []-inr) []-inr)
           
  []-assocˡʳ : ∀ {A B C D : Obj} {f : A ➔ D} {g : B ➔ D} {h : C ➔ D}
    → [ [ f , g ] , h ] ⊚ ⊎-assocʳˡ ≡ [ f , [ g , h ] ]
    
  []-assocˡʳ {f = f} {g = g} {h = h} =
    trans ⊚-distrib-[] ([]-destruct eq₃ (trans ⊚-distrib-[] ([]-destruct eq₂ eq₁))) 
        where
           eq₁ : [ [ f , g ] , h ] ⊚ (inr ⊚ idm) ≡ h
           eq₂ : [ [ f , g ] , h ] ⊚ (inl ⊚ inr) ≡ g
           eq₃ : [ [ f , g ] , h ] ⊚ (inl ⊚ inl) ≡ f

           eq₁ = trans ⊚-assoc (trans ((cong (_⊚ idm) []-inr))  ⊚-unitʳ)
           eq₂ = trans ⊚-assoc (trans (cong (_⊚ inr) []-inl) []-inr)
           eq₃ = trans ⊚-assoc (trans (cong (_⊚ inl) []-inl) []-inl)

  ⊎-assocʳˡʳ : ∀ {A B C : Obj} → ⊎-assocˡʳ {A} {B} {C} ⊚ ⊎-assocʳˡ {A} {B} {C} ≡ idm
  ⊎-assocʳˡʳ = 
             begin
                 [ [ inl ⊚ idm , inr ⊚ inl ] , inr ⊚ inr ] ⊚ ⊎-assocʳˡ
               ≡⟨ []-assocˡʳ ⟩
                 [ inl ⊚ idm , [ inr ⊚ inl , inr ⊚ inr ] ]
               ≡⟨ cong [_, [ inr ⊚ inl , inr ⊚ inr ] ] ⊚-unitʳ ⟩
                 [ inl , [ inr ⊚ inl , inr ⊚ inr ] ]
               ≡⟨ cong [ inl ,_] (sym ⊚-distrib-[]) ⟩
                 [ inl , inr ⊚ [ inl , inr ] ]
               ≡⟨ cong (λ g → [ inl , inr ⊚ g ]) [inl,inr] ⟩
                 [ inl , inr ⊚ idm ]
               ≡⟨ cong [ inl ,_] ⊚-unitʳ ⟩
                 [ inl , inr ]
               ≡⟨ [inl,inr] ⟩
                 idm
               ∎

  ⊎-assocˡʳˡ : ∀ {A B C : Obj} → ⊎-assocʳˡ {A} {B} {C} ⊚ ⊎-assocˡʳ {A} {B} {C} ≡ idm
  ⊎-assocˡʳˡ = begin
                 [ inl ⊚ inl , [ inl ⊚ inr , inr ⊚ idm ] ] ⊚ ⊎-assocˡʳ
               ≡⟨ []-assocʳˡ ⟩
                 [ [ inl ⊚ inl , inl ⊚ inr ] , inr ⊚ idm ]
               ≡⟨ cong [_, inr ⊚ idm ] (sym ⊚-distrib-[]) ⟩
                 [ inl ⊚ [ inl , inr ] , inr ⊚ idm ]
               ≡⟨ cong (λ g → [ inl ⊚ g , inr ⊚ idm ]) [inl,inr] ⟩
                 [ inl ⊚ idm , inr ⊚ idm ]
               ≡⟨ cong [_, inr ⊚ idm ] ⊚-unitʳ ⟩
                 [ inl , inr ⊚ idm ]
               ≡⟨ cong [ inl ,_] ⊚-unitʳ ⟩
                 [ inl , inr ]
               ≡⟨ [inl,inr] ⟩
                 idm
               ∎


SetCoC : Co-Cartesian {ℓ} SetCat
SetCoC = 
  record 
    { _⊎_ = Sum._⊎_
    ; inl = Sum.inj₁
    ; inr = Sum.inj₂
    ; [_,_] = Sum.[_,_]
    ; []-inl = refl
    ; []-inr = refl
    ; [inl,inr]    = →-≡ (λ { (Sum.inj₁ x) → refl ; (Sum.inj₂ y) → refl })
    ; ⊚-distrib-[] = →-≡ (λ { (Sum.inj₁ x) → refl ; (Sum.inj₂ y) → refl })
    }
