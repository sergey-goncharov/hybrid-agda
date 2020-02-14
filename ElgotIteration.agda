{-# OPTIONS --cubical --safe #-}

open import Level using (Level) renaming (suc to ℓ-suc)
open import Function using (id; _∘_; _$_)
open import Data.Product using (_×_; Σ; _,_; ∃-syntax; proj₁; proj₂)

open import CubicalIdentity using (_≡_; sym; trans; refl; cong; cong2; subst; subst-app)
open CubicalIdentity.≡-Reasoning

open import Category
open import Co-Cartesian
open import Functor

--*
{-
  This module introduces the notion of Elgot iteration in a category. 
-}
--*

module ElgotIteration {ℓ : Level} {Ob : Set (ℓ-suc ℓ)} {C : Category Ob} (CoC : Co-Cartesian C) where

open Co-Cartesian.Co-Cartesian CoC renaming (_⊎_ to _+_)

module †-axioms (_† : ∀ {X Y : Obj} → (X ➔ Y + X) → (X ➔ Y))  where

  -- Fixpoint
  Fix : Set (ℓ-suc ℓ)
  Fix = ∀ {X Y : Obj} {f : X ➔ Y + X}
    → [ idm , f † ] ⊚ f ≡ f †

  -- Naturality
  Nat : Set (ℓ-suc ℓ)
  Nat = ∀ {X Y Z : Obj} {f : X ➔ Y + X} {g : Y ➔ Z}
    → ((g ⊕ idm) ⊚ f) † ≡ g ⊚ f †

  -- Dinaturality
  Din : Set (ℓ-suc ℓ)
  Din = ∀ {X Y Z : Obj} {g : X ➔ Y + Z} {h : Z ➔ Y + X}
    → ([ inl , h ] ⊚ g) † ≡ [ idm , ([ inl , g ] ⊚ h) † ] ⊚ g

  -- Codiagonal
  Cod : Set (ℓ-suc ℓ)
  Cod = ∀ {X Y : Obj} {f : X ➔ (Y + X) + X}
    → ([ idm , inr ] ⊚ f) † ≡ f † †

  module _ {D : Category Ob} {CoC-D : Co-Cartesian D}
    {F : Functor D C id} (J : CoC-Functor CoC-D CoC F) where

    open Co-Cartesian.Co-Cartesian CoC-D
      using () renaming (_➔_ to _➔′_; idm to idm′; _⊕_ to _⊕′_)
    open Functor.CoC-Functor J 

    Uni : Set (ℓ-suc ℓ)
    Uni = ∀ {X Y Z : Obj} {f : X ➔ Y + X} {g : Z ➔ Y + Z} {h : Z ➔′ X}
      → f ⊚ (fmap h) ≡ (idm ⊕ fmap h) ⊚ g  → f † ⊚ (fmap h) ≡ g †

open †-axioms

record ElgotIteration : Set (ℓ-suc ℓ) where

  field
    _† : ∀ {X Y : Obj} → (X ➔ Y + X) → (X ➔ Y)
    fix : Fix _†

record TotalConway (It : ElgotIteration) : Set (ℓ-suc ℓ) where
  open ElgotIteration It public

  field
    -- Naturality
    nat : Nat _†
    
    -- Dinaturality
    din : Din _†

    -- Codiagonal
    cod : Cod _†

record TotalUniConway  (It : ElgotIteration) {D : Category Ob} {CoC-D : Co-Cartesian D}
             {F : Functor D C id} (J : CoC-Functor CoC-D CoC F) : Set (ℓ-suc ℓ) where

  -- added uniformity, removed dinaturality;
  -- the latter is derivable, which is shown below
  open ElgotIteration It public

  field
    -- Naturality
    nat : Nat _†

    -- Codiagonal
    cod : Cod _†

    -- Uniformity
    uni : Uni _† J

  open Co-Cartesian.Co-Cartesian CoC-D
    using () renaming (inl to inl′; inr to inr′
      ; _⊚_ to _⊚′_; idm to idm′; _➔_ to _➔′_
      ; _⊎_ to _+′_ ; _⊕_ to _⊕′_; [_,_] to [_,_]′)

  open CoC-Functor J 

  -- some coherence properties of injections,
  -- using the fact that J is identical on objects
  fmap-⊎F-inl : ∀ {X Y : Obj} → fmap (⊎F→ {X} {Y} (X ➔′_) inl′) ≡ inl
  fmap-⊎F-inl{X}{Y} = trans (sym $ subst-app (X ➔′_) {B₂ = X ➔_} (λ _ → fmap) ⊎F) $ sym inlF

  fmap-⊎F-inr : ∀ {X Y : Obj} → fmap (⊎F→ {X} {Y} (Y ➔′_) inr′) ≡ inr
  fmap-⊎F-inr{X}{Y} = trans (sym $ subst-app (Y ➔′_) {B₂ = Y ➔_} (λ _ → fmap) ⊎F) $ sym inrF

  -- an instance of uniformity for inl
  †-inl : ∀ {X Y Z : Obj} {f : (X + Z) ➔ Y + (X + Z)} {g : X ➔ Y + X}
    →  f ⊚ inl ≡ (idm ⊕ inl) ⊚ g → f † ⊚ inl ≡ g †
  †-inl {X} {Y} {Z} {f = f} {g = g} p = 
    begin
      f † ⊚ inl
    ≡˘⟨ cong (_⊚_ (f †)) fmap-⊎F-inl ⟩
      f † ⊚ fmap (⊎F→ (X ➔′_) inl′)
    ≡⟨ uni p′ ⟩
      g †
    ∎
      where
        p′ : f ⊚ fmap (⊎F→ (X ➔′_) inl′) ≡ (idm ⊕ fmap (⊎F→ (X ➔′_) inl′)) ⊚ g
        p′ = trans (cong (_⊚_ f) fmap-⊎F-inl) (trans p (cong (λ w → (idm ⊕ w) ⊚ g) $ sym fmap-⊎F-inl))

  -- an instance of uniformity for inr
  †-inr : ∀ {X Y Z : Obj} {f : (Z + X) ➔ Y + (Z + X)} {g : X ➔ Y + X}
    →  f ⊚ inr ≡ (idm ⊕ inr) ⊚ g → f † ⊚ inr ≡ g †
  †-inr {X} {Y} {Z} {f = f} {g = g} p = 
    begin
      f † ⊚ inr
    ≡˘⟨ cong (_⊚_ (f †)) fmap-⊎F-inr ⟩
      f † ⊚ fmap (⊎F→ (X ➔′_) inr′)
    ≡⟨ uni p′ ⟩
      g †
    ∎
      where
        p′ : f ⊚ fmap (⊎F→ (X ➔′_) inr′) ≡ (idm ⊕ fmap (⊎F→ (X ➔′_) inr′)) ⊚ g
        p′ = trans (cong (_⊚_ f) fmap-⊎F-inr) $ trans p (cong (λ w → (idm ⊕ w) ⊚ g) (sym fmap-⊎F-inr))

  -- an instance of uniformity for swap
  †-swap : ∀ {X Y Z : Obj} {f : (X + Y) ➔ Z + (X + Y)} 
    →  f † ⊚ swap ≡ ((idm ⊕ swap) ⊚ (f ⊚ swap)) †
    
  †-swap {X} {Y} {Z} {f = f} =
    begin
      f † ⊚ swap
    ≡˘⟨ ⊚-cong₂ fmap-swap′ ⟩
      f † ⊚ (fmap swap′)
    ≡⟨
       uni (trans (sym ⊚-unitˡ) $ trans
              (⊚-cong₁ $ trans (trans (sym [inl,inr]) $
                ([]-destruct
                   (trans (sym ⊚-unitʳ) $ ⊚-cong₂ $ sym ⊚-unitˡ)
                   (trans (sym ⊚-unitʳ) $ ⊚-cong₂ $ trans (sym swap-swap) $
                          ⊚-cong (sym fmap-swap′) (sym fmap-swap′))
                 ))
             (sym ⊕-⊕)) $ sym ⊚-assoc)
      ⟩
      ((idm ⊕ fmap swap′) ⊚ (f ⊚ fmap swap′)) †
    ≡⟨ cong2 (λ w w′ → ((idm ⊕ w) ⊚ (f ⊚ w′)) †) fmap-swap′ fmap-swap′ ⟩ 
      ((idm ⊕ swap) ⊚ (f ⊚ swap)) †
    ∎
      where
        swap′ : ∀ {X Y : Obj} → X + Y ➔′ Y + X
        swap′ {X} {Y} = ⊎F→ ((X + Y) ➔′_) (⊎F→ (_➔′ Y +′ X) [ inr′ , inl′ ]′) 

        fmap-swap′ : ∀ {X Y : Obj} → fmap (swap′{X}{Y}) ≡ swap{X}{Y}
        fmap-swap′{X}{Y} =        
           begin
             fmap (swap′{X}{Y})
           ≡˘⟨ subst-app ((X + Y) ➔′_) {B₂ = (X + Y) ➔_} (λ _ → fmap) ⊎F ⟩
             ⊎F→ (X + Y ➔_) (fmap (⊎F→ (_➔′ Y +′ X) [ inr′ , inl′ ]′))
           ≡˘⟨ cong (⊎F→ (X + Y ➔_)) (subst-app (_➔′ Y +′ X) {B₂ = _➔ Y +′ X} (λ _ → fmap) ⊎F) ⟩
             ⊎F→ (X + Y ➔_) (⊎F→ (_➔ Y +′ X) (fmap [ inr′ , inl′ ]′))
           ≡˘⟨ cong (⊎F→ (X + Y ➔_)) []F ⟩
             ⊎F→ (X + Y ➔_) ([ fmap inr′ , fmap inl′ ])
           ≡˘⟨ ⊎-destruct (trans []-inl (⊎F→⊚ h inl)) (trans []-inr (⊎F→⊚ h inr)) ⟩
             [ ⊎F→ (_➔_ X) (h ⊚ inl) , ⊎F→ (_➔_ Y) (h ⊚ inr) ] 
           ≡⟨
              []-destruct
                (trans (cong (⊎F→ (_➔_ X)) []-inl) $ sym inrF)
                (trans (cong (⊎F→ (_➔_ Y)) []-inr) $ sym inlF)
             ⟩
             [ inr , inl ]
           ∎
             where h = [ fmap inr′ , fmap inl′ ]
           
  bekić : ∀ {X Y Z : Obj} {f : X ➔ (Y + X) + Z} {g : Z ➔ (Y + X) + Z}
          → [([ idm , g † ] ⊚ f)† , [ idm , ([ idm , g † ] ⊚ f)† ] ⊚ g † ]
          ≡ ([ idm ⊕ inl , inr ⊚ inr ] ⊚ [ f , g ]) † 

  bekić {f = f} {g = g} =
    begin
    [ ([ idm , g † ] ⊚ f) † , [ idm , ([ idm , g † ] ⊚ f) † ] ⊚ g † ]
       -- using bekić₁ 
       ≡⟨ bekić₁ ⟩
    ([ (idm ⊕ inl) ⊚ ([ idm , g † ] ⊚ f) , (idm ⊕ inl) ⊚ g † ] †)
       ≡⟨ cong _† $ []-cong₁ ⊚-assoc ⟩
    ([ ((idm ⊕ inl) ⊚ [ idm , g † ]) ⊚ f , (idm ⊕ inl) ⊚ g † ] †)
       ≡⟨ cong _† $ []-cong₁ $ trans (⊚-cong₁ ⊚-distrib-[]) $ ⊚-cong₁ $ []-cong₁ ⊚-unitʳ ⟩
    [ [ idm ⊕ inl , (idm ⊕ inl) ⊚ g † ] ⊚ f , (idm ⊕ inl) ⊚ g † ] †      ≡˘⟨ cong _† $ []-cong₁ $ ⊚-cong₁ $ trans []-⊕ ([]-destruct ⊚-unitˡ ⊚-unitʳ) ⟩
    [ ([ idm , (idm ⊕ inl) ⊚ g † ] ⊚ ((idm ⊕ inl) ⊕ idm)) ⊚ f , (idm ⊕ inl) ⊚ g † ] †
      ≡˘⟨ cong _† $ []-cong₁ $ ⊚-assoc ⟩
    [ [ idm , (idm ⊕ inl) ⊚ g † ] ⊚ (((idm ⊕ inl) ⊕ idm) ⊚ f) , (idm ⊕ inl) ⊚ g † ] †
       -- using naturality
       ≡⟨ cong _† $ []-destruct (⊚-cong₁ $ []-cong₂ $ sym nat) (sym nat) ⟩
    [ [ idm , (((idm ⊕ inl) ⊕ idm) ⊚ g) † ] ⊚ (((idm ⊕ inl) ⊕ idm) ⊚ f) , (((idm ⊕ inl) ⊕ idm) ⊚ g) † ] †
       -- using bekić₂
       ≡⟨ cong _† $ trans bekić₂ $ cong _† $ sym ⊚-distrib-[] ⟩
    ((idm ⊕ inr) ⊚ [ ((idm ⊕ inl) ⊕ idm) ⊚ f , ((idm ⊕ inl) ⊕ idm) ⊚ g ]) † †
       ≡⟨ cong (_† ∘ _†) $ ⊚-cong₂ $ sym ⊚-distrib-[] ⟩    
    ((idm ⊕ inr) ⊚ (((idm ⊕ inl) ⊕ idm) ⊚ [ f , g ])) † †
       ≡⟨ cong (_† ∘ _†) $ trans ⊚-assoc $ ⊚-cong₁ $ trans ⊕-⊕ $
               []-destruct (⊚-cong₂ ⊚-unitˡ) (⊚-cong₂ ⊚-unitʳ) ⟩    
    (((idm ⊕ inl) ⊕ inr) ⊚ [ f , g ]) † †
      -- using codiagonal
      ≡˘⟨ cod ⟩
    ([ idm , inr ] ⊚ (((idm ⊕ inl) ⊕ inr) ⊚ [ f , g ])) †
      ≡⟨ cong _† ⊚-assoc ⟩
    (([ idm , inr ] ⊚ ((idm ⊕ inl) ⊕ inr)) ⊚ [ f , g ]) †
      ≡⟨ cong _† $ ⊚-cong₁ $ trans []-⊕ $ []-cong₁ ⊚-unitˡ ⟩
    ([(idm ⊕ inl) , inr ⊚ inr ] ⊚ [ f , g ]) †
    ∎
      
    where

      -- one instance of the Bekić law
      bekić₁ : ∀ {X Y Z : Obj} {f : X ➔ Y + X}{g : Z ➔ Y + X}
        → [ f † , [ idm , f † ] ⊚ g ] ≡ [ (idm ⊕ inl) ⊚ f , (idm ⊕ inl) ⊚ g ] † 
      
      bekić₁ {f = f} {g = g} =
         begin
         [ f † , [ idm , f † ] ⊚ g ]
           ≡˘⟨ []-destruct (†-inl []-inl) $  ⊚-cong₁ $ []-cong₂ $ †-inl []-inl ⟩
         [ h † ⊚ inl , [ idm ,  h † ⊚ inl ] ⊚ g ]
           ≡˘⟨ []-cong₂ $ ⊚-cong₁ $ []-cong₁ $ ⊚-unitʳ  ⟩  
         [ h † ⊚ inl , [ idm ⊚ idm , h † ⊚ inl ] ⊚ g ]
           ≡˘⟨ []-cong₂ $ ⊚-cong₁ $ []-⊕ ⟩
         [ h † ⊚ inl , ([ idm ,  h † ] ⊚ (idm ⊕ inl)) ⊚ g ]
           ≡˘⟨ []-cong₂ $  ⊚-assoc ⟩
         [ h † ⊚ inl , [ idm , h † ] ⊚ ((idm ⊕ inl) ⊚ g) ]
           ≡˘⟨ []-cong₂ $ ⊚-cong₂ $ []-inr ⟩
         [ h † ⊚ inl , [ idm ,  h † ] ⊚ (h ⊚ inr) ]
           ≡⟨ []-cong₂ $ ⊚-assoc ⟩
         [ h † ⊚ inl , ([ idm ,  h † ] ⊚ h) ⊚ inr ]
           ≡⟨ []-cong₂ $ ⊚-cong₁ $ fix ⟩
         [ h † ⊚ inl , h † ⊚ inr ] 
           ≡˘⟨ ⊚-distrib-[] ⟩
         h † ⊚ [ inl , inr ] 
           ≡⟨ ⊚-cong₂ [inl,inr] ⟩
         h † ⊚ idm
           ≡⟨ ⊚-unitʳ ⟩
         h †
         ∎
           where h = [ (idm ⊕ inl) ⊚ f , (idm ⊕ inl) ⊚ g ]

      -- another instance of the Bekić law
      bekić₂ : ∀ {X Y Z : Obj} {f : X ➔ Y + X} {g : Z ➔ Y + X}
        → [ [ idm , f † ] ⊚ g , f † ] ≡ [ (idm ⊕ inr) ⊚ g , (idm ⊕ inr) ⊚ f ] †
      bekić₂ {f = f} {g = g} = 
         begin
         [ [ idm , f † ] ⊚ g , f † ]
           ≡˘⟨ []-destruct (⊚-cong₁ $ []-cong₂ $ †-inr []-inr) (†-inr []-inr) ⟩ 
         [ [ idm , h †  ⊚ inr ] ⊚ g , h † ⊚ inr ] 
           ≡˘⟨ []-cong₁ $  ⊚-cong₁ $  []-cong₁ $ ⊚-unitʳ ⟩ 
         [ [ idm ⊚ idm , h † ⊚ inr ] ⊚ g , h † ⊚ inr ]
           ≡˘⟨ []-cong₁ $ ⊚-cong₁ $ []-⊕ ⟩  
         [ ([ idm , h † ] ⊚ (idm ⊕ inr)) ⊚ g , h † ⊚ inr ]
           ≡˘⟨ []-cong₁ $ ⊚-assoc ⟩ 
         [ [ idm , h † ] ⊚ ((idm ⊕ inr) ⊚ g) , h † ⊚ inr ]
           ≡˘⟨ []-cong₁ $ ⊚-cong₂ $ []-inl ⟩ 
         [ [ idm , h † ] ⊚ (h ⊚ inl) , h † ⊚ inr ]
           ≡⟨ []-cong₁ $ ⊚-assoc  ⟩ 
         [ ([ idm , h † ] ⊚ h) ⊚ inl , h † ⊚ inr ]
           ≡⟨ []-cong₁ $ ⊚-cong₁ $ fix ⟩
         [ h † ⊚ inl ,  h † ⊚ inr ] 
           ≡˘⟨ ⊚-distrib-[] ⟩
         h † ⊚ [ inl , inr ] 
           ≡⟨  ⊚-cong₂ [inl,inr] ⟩
         h † ⊚ idm
           ≡⟨ ⊚-unitʳ ⟩
         h †
         ∎
           where h = [ (idm ⊕ inr) ⊚ g , (idm ⊕ inr) ⊚ f ]

  -- Dinaturality
  din : Din _†
  din {g = g} {h = h} =
     begin
       ([ inl , h ] ⊚ g) †
     ≡˘⟨ []-inl ⟩
        [([ inl , h ] ⊚ g) † , [ idm , ([ inl , h ] ⊚ g) † ] ⊚ h ] ⊚ inl
     ≡˘⟨ ⊚-cong₁ helper₁ ⟩    
       [ (idm ⊕ inr) ⊚ g , (idm ⊕ inl) ⊚ h ] † ⊚ inl
     ≡⟨ trans (⊚-cong₁ (sym helper₂)) (trans (sym ⊚-assoc) (⊚-cong₂ []-inl))  ⟩
       [ (idm ⊕ inr) ⊚ h , (idm ⊕ inl) ⊚ g ] † ⊚ inr
     ≡⟨ trans
           (⊚-cong₁ (sym fix))
           (trans
             (sym ⊚-assoc)
             (trans
               (⊚-cong₂ []-inr)
               (trans
                 ⊚-assoc
                 (⊚-cong₁
                   (trans []-⊕
                     (trans
                       ([]-destruct ⊚-unitˡ refl)
                       refl)))))) ⟩
       [ idm , [ (idm ⊕ inr) ⊚ h , (idm ⊕ inl) ⊚ g ] † ⊚ inl ] ⊚ g
         ≡⟨ trans (cong (λ w → [ idm , w ⊚ inl ] ⊚ g) helper₁) (cong (λ w → [ idm , w ] ⊚ g) []-inl) ⟩
       [ idm , ([ inl , g ] ⊚ h) † ] ⊚ g
     ∎
     where
      helper₁ : ∀ {X Y Z : Obj} {g : X ➔ Y + Z} {h : Z ➔ Y + X} →
        [ (idm ⊕ inr) ⊚ g , (idm ⊕ inl) ⊚ h ] † ≡ [([ inl , h ] ⊚ g) † , [ idm , ([ inl , h ] ⊚ g) † ] ⊚ h ] 
      helper₁{X}{Y}{Z}{g = g}{h = h} =
        begin
          (([ (idm ⊕ inr) ⊚ g , (idm ⊕ inl) ⊚ h ] †))
        ≡⟨ cong _† (trans
                   ([]-destruct
                     (trans
                       (⊚-cong₁
                         (trans
                           ([]-destruct
                             (trans (⊚-unitʳ)
                               (trans (sym ⊚-unitʳ) (sym []-inl)) )
                               (sym ⊚-unitʳ))
                           (sym []-⊕)))
                     (sym ⊚-assoc))
                     (trans (⊚-cong₁ (sym []-inl)) (sym ⊚-assoc))) ( sym ⊚-distrib-[])) ⟩
           (([ idm ⊕ inl , inr ⊚ inr ] ⊚ [ (inl ⊕ idm) ⊚ g , inl ⊚ h ]) †)
        ≡˘⟨ bekić{f = (inl ⊕ idm) ⊚ g}{g = inl ⊚ h} ⟩
           [ ([ idm , (inl ⊚ h) † ] ⊚ ((inl ⊕ idm) ⊚ g))† , [ idm ,
             ([ idm , (inl ⊚ h) † ] ⊚ ((inl ⊕ idm) ⊚ g))† ] ⊚ ((inl ⊚ h) †) ]
        ≡⟨ []-destruct
              (cong _†
                (trans ⊚-assoc (cong (_⊚ g) (trans []-⊕ ([]-destruct ⊚-unitˡ (trans ⊚-unitʳ inl-h†))))))
                (⊚-cong ([]-destruct refl (cong _† (trans ⊚-assoc (⊚-cong₁ (trans []-⊕ ([]-destruct ⊚-unitˡ (trans ⊚-unitʳ inl-h†))))))) inl-h†) ⟩
          [([ inl , h ] ⊚ g) † , [ idm , ([ inl , h ] ⊚ g)† ] ⊚ h ] 
        ∎
          where
            inl-h† : (inl ⊚ h) † ≡ h
            inl-h† = trans (sym fix) (trans ⊚-assoc (trans (⊚-cong₁ []-inl) ⊚-unitˡ))

      helper₂ : ∀ {X Y Z : Obj} {g : X ➔ Y + Z} {h : Z ➔ Y + X} →
        [ (idm ⊕ inr) ⊚ g , (idm ⊕ inl) ⊚ h ] † ⊚ swap ≡  [ (idm ⊕ inr) ⊚ h , (idm ⊕ inl) ⊚ g ] †
      helper₂ = trans †-swap (
        cong _† (trans (⊚-cong₂ []-swap) (trans ⊚-distrib-[] ([]-destruct
                         (trans ⊚-assoc (⊚-cong₁ (trans ⊕-⊕ ([]-destruct (⊚-cong₂ ⊚-unitˡ) (⊚-cong₂ []-inl)))))
                         (trans ⊚-assoc (⊚-cong₁ (trans ⊕-⊕ ([]-destruct (⊚-cong₂ ⊚-unitˡ) (⊚-cong₂ []-inr)))))))))



