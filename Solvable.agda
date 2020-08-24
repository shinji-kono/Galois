open import Level hiding ( suc ; zero )
open import Algebra
module Solvable {n m : Level} (G : Group n m ) where

open import Data.Unit
open import Function.Inverse as Inverse using (_↔_; Inverse; _InverseOf_)
open import Function
open import Data.Nat hiding (_⊔_) -- using (ℕ; suc; zero)
open import Relation.Nullary
open import Data.Empty
open import Data.Product
open import  Relation.Binary.PropositionalEquality hiding ( [_] ; sym )


open Group G
open import Gutil G

[_,_] :  Carrier   → Carrier   → Carrier  
[ g , h ] = g ⁻¹ ∙ h ⁻¹ ∙ g ∙ h 

data Commutator (P : Carrier → Set (Level.suc n ⊔ m)) : (f : Carrier) → Set (Level.suc n ⊔ m) where
  uni   : Commutator P ε
  comm  : {g h : Carrier} → P g → P h  → Commutator P [ g , h ] 
  gen   : {f g : Carrier} → Commutator P f → Commutator P g → Commutator P ( f ∙  g  )
  ccong : {f g : Carrier} → f ≈ g → Commutator P f → Commutator P g

deriving : ( i : ℕ ) → Carrier → Set (Level.suc n ⊔ m)
deriving 0 x = Lift (Level.suc n ⊔ m) ⊤
deriving (suc i) x = Commutator (deriving i) x 

record solvable : Set (Level.suc n ⊔ m) where
  field 
     dervied-length : ℕ
     end : (x : Carrier ) → deriving dervied-length x →  x ≈ ε  

-- deriving stage is closed on multiplication and inversion

import Relation.Binary.Reasoning.Setoid as EqReasoning

lemma4 : (g h : Carrier ) → [ h , g ] ≈ [ g , h ] ⁻¹
lemma4 g h = begin
       [ h , g ]                               ≈⟨ grefl ⟩
       (h ⁻¹ ∙ g ⁻¹ ∙   h ) ∙ g                ≈⟨ assoc _ _ _ ⟩
       h ⁻¹ ∙ g ⁻¹ ∙  (h ∙ g)                  ≈⟨ ∙-cong grefl (gsym (∙-cong lemma6 lemma6))  ⟩
       h ⁻¹ ∙  g ⁻¹ ∙ ((h ⁻¹) ⁻¹ ∙ (g ⁻¹) ⁻¹)  ≈⟨  ∙-cong grefl (lemma5 _ _ )  ⟩
       h ⁻¹ ∙  g ⁻¹ ∙  (g ⁻¹ ∙ h ⁻¹) ⁻¹        ≈⟨ assoc _ _ _ ⟩
       h ⁻¹ ∙ (g ⁻¹ ∙  (g ⁻¹ ∙ h ⁻¹) ⁻¹)       ≈⟨ ∙-cong grefl (lemma5 (g ⁻¹ ∙ h ⁻¹ ) g ) ⟩
       h ⁻¹ ∙ (g ⁻¹ ∙   h ⁻¹ ∙ g) ⁻¹           ≈⟨ lemma5 (g ⁻¹ ∙ h ⁻¹ ∙ g) h ⟩
       (g ⁻¹ ∙ h ⁻¹ ∙   g ∙ h) ⁻¹              ≈⟨ grefl ⟩
       [ g , h ]  ⁻¹                  
     ∎ where open EqReasoning (Algebra.Group.setoid G)

deriving-mul : { i : ℕ } → { x y : Carrier } → deriving i x → deriving i y  → deriving i ( x ∙ y )
deriving-mul {zero} {x} {y} _ _ = lift tt
deriving-mul {suc i} {x} {y} ix iy = gen ix iy

deriving-inv : { i : ℕ } → { x  : Carrier } → deriving i x → deriving i ( x ⁻¹ )
deriving-inv {zero} {x} (lift tt) = lift tt
deriving-inv {suc i} {ε} uni = ccong lemma3 uni
deriving-inv {suc i} {_} (comm x x₁ )   = ccong (lemma4 _ _) (comm x₁ x) where
deriving-inv {suc i} {_} (gen x x₁ )    = ccong (lemma5 _ _ ) ( gen (deriving-inv x₁) (deriving-inv x)) where
deriving-inv {suc i} {x} (ccong eq ix ) = ccong (⁻¹-cong eq) ( deriving-inv ix )

idcomtr : (g  : Carrier ) → [ g , ε  ] ≈ ε 
idcomtr g  = begin
       (g ⁻¹ ∙ ε  ⁻¹ ∙   g ∙ ε )              ≈⟨ ∙-cong (∙-cong (∙-cong grefl (sym lemma3 )) grefl ) grefl ⟩ 
       (g ⁻¹ ∙ ε   ∙   g ∙ ε )                ≈⟨ ∙-cong (∙-cong (proj₂ identity _) grefl)  grefl ⟩
       (g ⁻¹   ∙   g ∙ ε     )                ≈⟨ ∙-cong (proj₁ inverse _ )   grefl ⟩
       (  ε  ∙ ε     )                        ≈⟨  proj₂ identity _  ⟩
       ε
     ∎ where open EqReasoning (Algebra.Group.setoid G)

idcomtl : (g  : Carrier ) → [ ε ,  g ] ≈ ε 
idcomtl g  = begin
       (ε ⁻¹ ∙ g  ⁻¹ ∙   ε ∙ g )              ≈⟨ ∙-cong (proj₂ identity _) grefl ⟩ 
       (ε ⁻¹ ∙ g  ⁻¹ ∙    g )                ≈⟨ ∙-cong (∙-cong (sym lemma3 ) grefl ) grefl ⟩
       (ε  ∙ g  ⁻¹ ∙    g )                  ≈⟨ ∙-cong (proj₁ identity _) grefl ⟩
       (g ⁻¹   ∙    g     )                ≈⟨  proj₁ inverse _ ⟩
       ε
     ∎ where open EqReasoning (Algebra.Group.setoid G)
