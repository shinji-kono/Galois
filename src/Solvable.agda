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
  comm  : {g h : Carrier} → P g → P h  → Commutator P [ g , h ] 
  ccong : {f g : Carrier} → f ≈ g → Commutator P f → Commutator P g

deriving : ( i : ℕ ) → Carrier → Set (Level.suc n ⊔ m)
deriving 0 x = Lift (Level.suc n ⊔ m) ⊤
deriving (suc i) x = Commutator (deriving i) x 

open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ )

deriving-subst : { i : ℕ } → {x y : Carrier } → x ≈ y → (dx : deriving i x ) → deriving i y 
deriving-subst {zero} {x} {y} x=y dx = lift tt
deriving-subst {suc i} {x} {y} x=y dx = ccong x=y dx

record solvable : Set (Level.suc n ⊔ m) where
  field 
     dervied-length : ℕ
     end : (x : Carrier ) → deriving dervied-length x →  x ≈ ε  

-- deriving stage is closed on multiplication and inversion

import Relation.Binary.Reasoning.Setoid as EqReasoning

open EqReasoning (Algebra.Group.setoid G)

lemma4 : (g h : Carrier ) → [ h , g ] ≈ [ g , h ] ⁻¹
lemma4 g h = begin
       [ h , g ]                               ≈⟨ grefl ⟩
       (h ⁻¹ ∙ g ⁻¹ ∙   h ) ∙ g                ≈⟨ assoc _ _ _ ⟩
       h ⁻¹ ∙ g ⁻¹ ∙  (h ∙ g)                  ≈⟨ ∙-cong grefl (gsym (∙-cong f⁻¹⁻¹≈f f⁻¹⁻¹≈f))  ⟩
       h ⁻¹ ∙  g ⁻¹ ∙ ((h ⁻¹) ⁻¹ ∙ (g ⁻¹) ⁻¹)  ≈⟨  ∙-cong grefl (lemma5 _ _ )  ⟩
       h ⁻¹ ∙  g ⁻¹ ∙  (g ⁻¹ ∙ h ⁻¹) ⁻¹        ≈⟨ assoc _ _ _ ⟩
       h ⁻¹ ∙ (g ⁻¹ ∙  (g ⁻¹ ∙ h ⁻¹) ⁻¹)       ≈⟨ ∙-cong grefl (lemma5 (g ⁻¹ ∙ h ⁻¹ ) g ) ⟩
       h ⁻¹ ∙ (g ⁻¹ ∙   h ⁻¹ ∙ g) ⁻¹           ≈⟨ lemma5 (g ⁻¹ ∙ h ⁻¹ ∙ g) h ⟩
       (g ⁻¹ ∙ h ⁻¹ ∙   g ∙ h) ⁻¹              ≈⟨ grefl ⟩
       [ g , h ]  ⁻¹                  
     ∎ 

deriving-inv : { i : ℕ } → { x  : Carrier } → deriving i x → deriving i ( x ⁻¹ )
deriving-inv {zero} {x} (lift tt) = lift tt
deriving-inv {suc i} {_} (comm x x₁ )   = ccong (lemma4 _ _) (comm x₁ x) 
deriving-inv {suc i} {x} (ccong eq ix ) = ccong (⁻¹-cong eq) ( deriving-inv ix )

idcomtr : (g  : Carrier ) → [ g , ε  ] ≈ ε 
idcomtr g  = begin
       (g ⁻¹ ∙ ε  ⁻¹ ∙   g ∙ ε )              ≈⟨ ∙-cong (∙-cong (∙-cong grefl (sym ε≈ε⁻¹  )) grefl ) grefl ⟩ 
       (g ⁻¹ ∙ ε   ∙   g ∙ ε )                ≈⟨ ∙-cong (∙-cong (proj₂ identity _) grefl)  grefl ⟩
       (g ⁻¹   ∙   g ∙ ε     )                ≈⟨ ∙-cong (proj₁ inverse _ )   grefl ⟩
       (  ε  ∙ ε     )                        ≈⟨  proj₂ identity _  ⟩
       ε
     ∎ 

idcomtl : (g  : Carrier ) → [ ε ,  g ] ≈ ε 
idcomtl g  = begin
       (ε ⁻¹ ∙ g  ⁻¹ ∙   ε ∙ g )              ≈⟨ ∙-cong (proj₂ identity _) grefl ⟩ 
       (ε ⁻¹ ∙ g  ⁻¹ ∙    g )                ≈⟨ ∙-cong (∙-cong (sym ε≈ε⁻¹  ) grefl ) grefl ⟩
       (ε  ∙ g  ⁻¹ ∙    g )                  ≈⟨ ∙-cong (proj₁ identity _) grefl ⟩
       (g ⁻¹   ∙    g     )                ≈⟨  proj₁ inverse _ ⟩
       ε
     ∎ 

deriving-ε : { i : ℕ } → deriving i ε
deriving-ε {zero} = lift tt
deriving-ε {suc i} = ccong (idcomtr ε) (comm deriving-ε deriving-ε) 

comm-refl : {f g : Carrier } → f ≈ g  → [ f ,  g ] ≈ ε 
comm-refl {f} {g} f=g = begin
       f ⁻¹ ∙ g ⁻¹ ∙   f ∙ g
     ≈⟨ ∙-cong (∙-cong (∙-cong (⁻¹-cong f=g ) grefl ) f=g ) grefl ⟩
       g ⁻¹ ∙ g ⁻¹ ∙   g ∙ g
     ≈⟨ ∙-cong (assoc _ _ _ ) grefl  ⟩
       g ⁻¹ ∙ (g ⁻¹ ∙   g ) ∙ g
     ≈⟨ ∙-cong (∙-cong grefl (proj₁ inverse _) ) grefl ⟩
       g ⁻¹ ∙ ε  ∙ g 
     ≈⟨ ∙-cong (proj₂ identity _) grefl  ⟩
       g ⁻¹ ∙  g 
     ≈⟨  proj₁ inverse _  ⟩
       ε
     ∎ 

comm-resp : {g h g1 h1  : Carrier } → g ≈ g1  → h ≈ h1 → [ g , h ] ≈ [ g1 , h1 ] 
comm-resp {g} {h} {g1} {h1} g=g1 h=h1 =  ∙-cong (∙-cong (∙-cong (⁻¹-cong g=g1 ) (⁻¹-cong h=h1 )) g=g1 ) h=h1

