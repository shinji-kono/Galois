{-# OPTIONS --allow-unsolved-metas #-}
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
open import Tactic.MonoidSolver using (solve; solve-macro)


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

open import NormalSubgroup
import Algebra.Morphism.Definitions as MorphismDefinitions
open import Algebra.Morphism.Structures

-- Commutator is normal subgroup of G

Pcomm : {a b : Carrier} → (i : ℕ) → deriving i a → deriving i (b ∙ (a ∙ b ⁻¹ ))
Pcomm {a} {b} zero (lift tt) = lift tt
Pcomm {.([ _ , _ ])} {b} (suc i) (comm {g} {h} pg ph ) = ccong cc2 (comm (Pcomm {_} {b} i pg) (Pcomm {_} {b} i ph)) where
   cc2 : [ b ∙ (g ∙ b ⁻¹) , b ∙ (h ∙ b ⁻¹) ] ≈ b ∙ ([ g , h ] ∙ b ⁻¹)
   cc2 = begin
    [ b ∙ (g ∙ b ⁻¹) , b ∙ (h ∙ b ⁻¹) ] ≈⟨ grefl ⟩ 
    (b ∙ (g ∙ b ⁻¹) ) ⁻¹ ∙ ( b ∙ (h ∙ b ⁻¹)) ⁻¹ ∙  (b ∙ (g ∙ b ⁻¹)) ∙ (b ∙ (h ∙ b ⁻¹)) 
        ≈⟨ car (car (∙-cong (sym (lemma5 _ _)) (sym (lemma5 _ _)))) ⟩ 
    ((g ∙ b ⁻¹) ⁻¹ ∙ b ⁻¹  )  ∙ ( (h ∙ b ⁻¹) ⁻¹ ∙ b ⁻¹ ) ∙  (b ∙ (g ∙ b ⁻¹)) ∙ (b ∙ (h ∙ b ⁻¹)) 
        ≈⟨ car (car (∙-cong (car (sym (lemma5 _ _))) (car (sym (lemma5 _ _))))) ⟩ 
    (((b ⁻¹ )⁻¹ ∙ g ⁻¹ )  ∙ b ⁻¹  )  ∙ ( ((b ⁻¹) ⁻¹ ∙ h ⁻¹ ) ∙ b ⁻¹ ) ∙  (b ∙ (g ∙ b ⁻¹)) ∙ (b ∙ (h ∙ b ⁻¹)) 
        ≈⟨ car (car (∙-cong (car (car f⁻¹⁻¹≈f)) (car (car f⁻¹⁻¹≈f))))  ⟩ 
    ((b  ∙ g ⁻¹ )  ∙ b ⁻¹  )  ∙ ( (b  ∙ h ⁻¹ ) ∙ b ⁻¹ ) ∙  (b ∙ (g ∙ b ⁻¹)) ∙ (b ∙ (h ∙ b ⁻¹)) ≈⟨ solve monoid ⟩ 
    (((b  ∙ g ⁻¹ )  ∙ (b ⁻¹    ∙ b ) ∙ h ⁻¹ ) ∙ b ⁻¹ ) ∙  (b ∙ (g ∙ b ⁻¹)) ∙ (b ∙ (h ∙ b ⁻¹)) ≈⟨ car (car (car (car (cdr (proj₁ inverse _))))) ⟩ 
    (((b  ∙ g ⁻¹ )  ∙ ε ∙ h ⁻¹ ) ∙ b ⁻¹ ) ∙  (b ∙ (g ∙ b ⁻¹)) ∙ (b ∙ (h ∙ b ⁻¹)) ≈⟨ solve monoid ⟩ 
    ((b  ∙ (g ⁻¹   ∙ ε) ∙ h ⁻¹ ) ∙ b ⁻¹ ) ∙  (b ∙ (g ∙ (b ⁻¹ ∙ b ) ∙ (h ∙ b ⁻¹))) ≈⟨ cdr (cdr (car (cdr (proj₁ inverse _)))) ⟩
    ((b  ∙ (g ⁻¹   ∙ ε) ∙ h ⁻¹ ) ∙ b ⁻¹ ) ∙  (b ∙ (g ∙ ε ∙ (h ∙ b ⁻¹))) ≈⟨ 
           ∙-cong (car (car (cdr (proj₂ identity _)))) (cdr (car (proj₂ identity _))) ⟩ 
    (((b  ∙ g ⁻¹ )  ∙ h ⁻¹ ) ∙ b ⁻¹ ) ∙  (b ∙ (g ∙ (h ∙ b ⁻¹))) ≈⟨ solve monoid ⟩ 
    ((b  ∙ g ⁻¹ )  ∙ h ⁻¹ ) ∙ (b ⁻¹  ∙  b ) ∙ (g ∙ (h ∙ b ⁻¹)) ≈⟨ ∙-cong (∙-cong grefl (proj₁ inverse _) ) grefl ⟩ 
    ((b  ∙ g ⁻¹ )  ∙ h ⁻¹ ) ∙ ε ∙ (g ∙ (h ∙ b ⁻¹)) ≈⟨ ∙-cong (proj₂ identity _) grefl ⟩ 
    ((b  ∙ g ⁻¹ )  ∙ h ⁻¹ ) ∙ (g ∙ (h ∙ b ⁻¹)) ≈⟨ solve monoid ⟩ 
    b ∙ (( g ⁻¹ ∙ h ⁻¹ ∙ g ∙ h ) ∙ b ⁻¹) ≈⟨ grefl ⟩
    b ∙ ([ g , h ] ∙ b ⁻¹) ∎
Pcomm {a} {b} (suc i) (ccong f=a pa) = ccong (∙-cong grefl (∙-cong f=a grefl)) (Pcomm {_} {b} (suc i) pa)

-- a proudct of commutators may not be a commutator
-- so we have to use finite products of commutators

data iCommutator (i : ℕ) : (j : ℕ) → Carrier → Set (Level.suc n ⊔ m) where
  iunit : {a : Carrier} → deriving i a  →  iCommutator i zero a
  icoml : {j : ℕ} → {a b : Carrier} → deriving i a → iCommutator i j b → iCommutator i (suc j) (a ∙ b)
  icomr : {j : ℕ} → {a b : Carrier} → deriving i a → iCommutator i j b → iCommutator i (suc j) (b ∙ a)
  iccong : {j : ℕ} → {a b : Carrier} → a ≈ b → iCommutator i j b → iCommutator i j a

record IC (i : ℕ ) (ica : Carrier) : Set (Level.suc n ⊔ m) where
  field 
     icn : ℕ
     icc : iCommutator i icn ica

CommGroup : (i : ℕ) → NormalSubGroup G 
CommGroup i = record {
     P = IC i
   ; Pε = record { icn = 0; icc = iunit deriving-ε }
   ; P⁻¹ =  cg00
   ; P≈ = λ b=a ic → record { icn = icn ic ; icc = iccong (sym b=a) (icc ic) }
   ; P∙ = cg01
   ; Pcomm = cg02
 }  where
     open IC
     cg00 :  (a : Carrier) → IC i a → IC i (a ⁻¹)
     cg00 a record { icn = .zero ; icc = iunit  x } = record { icn = 0 ; icc = iunit (deriving-inv x) }
     cg00 .((G Group.∙ _) _) record { icn = suc j ; icc = icoml ia icc₁ } with cg00 _ record { icn = _ ; icc = icc₁ } 
     ... | ib = record { icn = suc (icn ib) ; icc = iccong (sym (lemma5 _ _ )) ( icomr (deriving-inv ia) (icc ib)) }
     cg00 .((G Group.∙ _) _) record { icn = suc j ; icc = icomr ia icc₁ } with cg00 _ record { icn = _ ; icc = icc₁ } 
     ... | ib = record { icn = suc (icn ib) ; icc = iccong (sym (lemma5 _ _ )) ( icoml (deriving-inv ia) (icc ib)) }
     cg00 _ record { icn = j ; icc = iccong eq icc₁ } with cg00 _ record { icn = _ ; icc = icc₁ } 
     ... | ib = record { icn = icn ib ; icc = iccong (⁻¹-cong eq) (icc ib) }
     cg01 : {a b : Carrier} → IC i a → IC i b → IC i (a ∙ b)
     cg01 {a} {b} record { icn = .zero ; icc = (iunit x) } ib = ?
     cg01 {.((G Group.∙ _) _)} {b} record { icn = .(suc _) ; icc = (icoml x icc₁) } ib = ?
     cg01 {.((G Group.∙ _) _)} {b} record { icn = .(suc _) ; icc = (icomr x icc₁) } ib = ?
     cg01 {a} {b} record { icn = icn ; icc = (iccong x icc₁) } ib = ?
     cg02 :  {a b : Carrier} → IC i a → IC i (b ∙ (a ∙ b ⁻¹))
     cg02 = ?


