{-# OPTIONS --cubical-compatible --safe #-} 

open import Level hiding ( suc ; zero )
open import Algebra
module Solvable {n m : Level} (G : Group n m ) where

open import Data.Unit
open import Function.Bundles --  as Inverse using (_↔_; Inverse; _InverseOf_)
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
  comm  : {g h i : Carrier} → P g → P h  → i ≈ [ g , h ] → Commutator P  i

ccong : (P : Carrier → Set (Level.suc n ⊔ m)) {f g : Carrier} → f ≈ g → Commutator P f → Commutator P g
ccong P {f} {g} f=g (comm {g1} {h} {i} pg  ph f=gh ) = comm pg ph (gtrans (gsym f=g) f=gh)

deriving : ( i : ℕ ) → Carrier → Set (Level.suc n ⊔ m)
deriving 0 x = Lift (Level.suc n ⊔ m) ⊤
deriving (suc i) x = Commutator (deriving i) x 

-- open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ )

deriving-subst : { i : ℕ } → {x y : Carrier } → x ≈ y → (dx : deriving i x ) → deriving i y 
deriving-subst {zero} {x} {y} x=y dx = lift tt
deriving-subst {suc i} {x} {y} x=y (comm ig ih x=gh) = comm ig ih (gtrans (gsym x=y) x=gh)

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
deriving-inv {suc i} {x} (comm ig ih x=gh )   = comm ih ig (gtrans (⁻¹-cong x=gh) (gsym (lemma4 _ _)))

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
deriving-ε {suc i} = comm (deriving-ε {i}) (deriving-ε {i}) (gsym (idcomtr ε))

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

Pcomm : {a b : Carrier} → (i : ℕ) → deriving i a → deriving i (b ∙ (a ∙ b ⁻¹ ))
Pcomm {a} {b} zero (lift tt) = lift tt
Pcomm {a} {b} (suc i) (comm {g} {h} pg ph eq ) = comm (Pcomm {_} {b} i pg) (Pcomm {_} {b} i ph) (gtrans cc3 (gsym cc2)) where
   cc3 : b ∙ (a ∙ b ⁻¹) ≈ b ∙ ([ g , h ] ∙ b ⁻¹)
   cc3 = cdr (car eq ) 
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

-- Finitely Generated Commutator is normal subgroup of G

-- a proudct of commutators may not be a commutator
-- so we have to use finite products of commutators

data iCommutator (i : ℕ) : Carrier → Set (Level.suc n ⊔ m) where
  iunit : {a : Carrier} → deriving i a  →  iCommutator i a
  i∙ : {a b : Carrier} → iCommutator i a → iCommutator i  b → iCommutator i  (a ∙ b)
  iccong : {a b : Carrier} → a ≈ b → iCommutator i  b → iCommutator i  a

CommNormal : (i : ℕ) → NormalSubGroup G 
CommNormal i = record {
   Psub = record {
     P = iCommutator i
   ; Pε = iunit deriving-ε 
   ; P⁻¹ =  cg00
   ; P≈ = λ b=a ic → iccong (sym b=a) ic
   ; P∙ = cg01 
   }
   ; Pcomm = cg02 
 }  where
     cg00 :  (a : Carrier) → iCommutator i a → iCommutator i (a ⁻¹)
     cg00 a (iunit x) = iunit (deriving-inv x)
     cg00 .((G Group.∙ _) _) (i∙ ic ic₁) = iccong (gsym (lemma5 _ _)) ( i∙ (cg00 _ ic₁) (cg00 _ ic) )
     cg00 a (iccong eq ic) = iccong (⁻¹-cong eq) (cg00 _ ic)
     cg01 : {a b : Carrier} → iCommutator i a → iCommutator i b → iCommutator i (a ∙ b)
     cg01 {a} {b} ia ib = i∙  ia ib
     cg02 : {a b : Carrier} → iCommutator i a → iCommutator i (b ∙ (a ∙ b ⁻¹))
     cg02 {a} {b} (iunit da) = iunit ( Pcomm i da )
     cg02 {a} {b} (i∙ {a₁} {b₁} ia ib)  = iccong cg03 (i∙ (cg02 {a₁} {b} ia) (cg02 {b₁} {b} ib)) where
        cg03 : b ∙ (a₁ ∙ b₁ ∙ b ⁻¹) ≈  b ∙ (a₁ ∙ b ⁻¹) ∙ (b ∙ (b₁ ∙ b ⁻¹))
        cg03 = begin
           b ∙ (a₁ ∙ b₁ ∙ b ⁻¹) ≈⟨ solve monoid ⟩
           b ∙ (a₁ ∙ ε ∙ b₁ ∙ b ⁻¹) ≈⟨ cdr (car (car (cdr (gsym (proj₁ inverse _))))) ⟩
           b ∙ (a₁ ∙ (b ⁻¹ ∙ b ) ∙ b₁ ∙ b ⁻¹) ≈⟨ solve monoid ⟩
            b ∙ (a₁ ∙ b ⁻¹) ∙ (b ∙ (b₁ ∙ b ⁻¹)) ∎ 
     cg02 {a} {b} (iccong eq ia) = iccong (cdr (car eq)) ( cg02 {_} {b} ia )


