{-# OPTIONS --cubical-compatible --safe #-}

open import Level hiding ( suc ; zero )
module NormalSubgroup  where

open import Algebra
open import Algebra.Structures
open import Algebra.Definitions
open import Data.Product
open import Relation.Binary.PropositionalEquality 
open import Algebra.Morphism.Structures
open import Data.Empty
open import Relation.Nullary

open GroupMorphisms

GR : {c l : Level } → Group c l → RawGroup c l
GR G = record {
     Carrier        = Carrier G
     ; _≈_          = _≈_ G
     ; _∙_          = _∙_ G
     ; ε            = ε G
     ; _⁻¹          = _⁻¹ G
  } where open Group

record GAxiom {c l : Level } (G : Group c l)  : Set ( c  Level.⊔  l ) where
  open Group G
  field
     ∙-cong :  {x y u v : Carrier } → x ≈ y → u ≈ v →  x ∙ u ≈  y ∙ v 
     assoc : (x y z : Carrier ) → x ∙ y ∙ z ≈  x ∙ ( y ∙ z )
     identity : ((y : Carrier) → ε ∙ y ≈ y ) ×  ((y : Carrier) → y ∙ ε ≈ y )
     inverse   : ((y : Carrier) → y ⁻¹ ∙ y  ≈ ε ) ×  ((y : Carrier) → y ∙ y ⁻¹  ≈ ε )
     ⁻¹-cong   : {x y : Carrier } → x ≈ y → x ⁻¹ ≈ y ⁻¹

GA : {c l : Level } → (G : Group c l) → GAxiom G
GA G = record {
        ∙-cong = IsMagma.∙-cong ( IsSemigroup.isMagma ( IsMonoid.isSemigroup ( IsGroup.isMonoid isGroup)))
     ;  assoc = IsSemigroup.assoc ( IsMonoid.isSemigroup ( IsGroup.isMonoid isGroup))
     ;  identity = IsMonoid.identity ( IsGroup.isMonoid isGroup)
     ;  inverse   = IsGroup.inverse isGroup
     ;  ⁻¹-cong   = IsGroup.⁻¹-cong isGroup
   } where open Group G

open import Relation.Binary.Structures

Eq : {c l : Level } → (G : Group c l) → IsEquivalence _
Eq G =  IsMagma.isEquivalence (IsSemigroup.isMagma (IsMonoid.isSemigroup
             (IsGroup.isMonoid (Group.isGroup G ))) )

_<_∙_> : {c d : Level} (m : Group c d )  →    Group.Carrier m →  Group.Carrier m →  Group.Carrier m
m < x ∙ y > =  Group._∙_ m x y

_<_≈_> : {c d : Level} (m : Group c d )  →    (f  g : Group.Carrier m ) → Set d
m < x ≈ y > =  Group._≈_ m x y

infixr 9 _<_∙_>

record SubGroup {l c d : Level} (A : Group c d )  : Set (Level.suc (l Level.⊔ (c Level.⊔ d))) where
   open Group A
   field                           
       P : Carrier  → Set l
       Pε : P ε
       P⁻¹ : (a : Carrier  ) → P a → P (a ⁻¹)
       P≈ :  {a b : Carrier  } → a ≈ b → P a → P b
       P∙ :  {a b : Carrier  } → P a → P b → P (  a ∙ b  )

-- assuming Homomorphism is too strong
--
record NormalSubGroup {l c d : Level} (A : Group c d )  : Set (Level.suc (l Level.⊔ (c Level.⊔ d))) where
   open Group A
   field                           
       Psub : SubGroup {l} A
       -- gN ≈ Ng
       Pcomm : {a b : Carrier  }  → SubGroup.P Psub a  →  SubGroup.P Psub ( b ∙  ( a  ∙ b ⁻¹ ) )
   P : Carrier  → Set l
   P = SubGroup.P Psub
   Pε : P ε
   Pε = SubGroup.Pε Psub
   P⁻¹ : (a : Carrier  ) → P a → P (a ⁻¹)
   P⁻¹ = SubGroup.P⁻¹ Psub
   P≈ :  {a b : Carrier  } → a ≈ b → P a → P b
   P≈ = SubGroup.P≈ Psub
   P∙ :  {a b : Carrier  } → P a → P b → P (  a ∙ b  )
   P∙ = SubGroup.P∙ Psub

import Relation.Binary.Reasoning.Setoid as EqReasoning

record Nelm {c d e : Level} (A : Group c d ) (n : SubGroup {e} A) : Set  (Level.suc e ⊔ (Level.suc c ⊔ d))  where
   open Group A
   open SubGroup n 
   field                           
       elm : Carrier
       Pelm : P elm

SGroup : {c d e : Level} (A : Group c d ) (n : SubGroup {e} A) → Group  (Level.suc e ⊔ (Level.suc c ⊔ d))  d
SGroup {_} {_} {_} A n = record {
      Carrier        = Nelm A n
    ; _≈_            = λ x y → elm x ≈ elm y
    ; _∙_            = λ x y → record { elm = elm x ∙ elm y ; Pelm = P∙ (Pelm x) (Pelm y) }
    ; ε              = record { elm = ε ; Pelm = Pε }
    ; _⁻¹            = λ x → record { elm = (elm x) ⁻¹  ; Pelm = P⁻¹ (elm x) (Pelm x) }
    ; isGroup = record { isMonoid  = record { isSemigroup = record { isMagma = record {
       isEquivalence = record { refl = IsEquivalence.refl (IsGroup.isEquivalence ga) 
          ; sym =  IsEquivalence.sym (IsGroup.isEquivalence ga) 
          ; trans = IsEquivalence.trans (IsGroup.isEquivalence ga)  }
       ; ∙-cong = IsGroup.∙-cong ga }
       ; assoc = λ a b c → IsGroup.assoc ga (elm a) (elm b) (elm c) }
       ; identity = ( (λ q → proj₁ (IsGroup.identity ga) (elm q)) , (λ q → proj₂ (IsGroup.identity ga) (elm q)) ) }
       ; inverse = ( (λ q → proj₁ (IsGroup.inverse ga) (elm q)) , (λ q → proj₂ (IsGroup.inverse ga) (elm q)) ) 
       ; ⁻¹-cong   = IsGroup.⁻¹-cong ga }
   }  where
       open Group A
       open SubGroup n 
       open Nelm 
       ga = Group.isGroup A


