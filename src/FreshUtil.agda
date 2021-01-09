{-# OPTIONS --without-K --safe #-}
module FreshUtil where

open import Level using (Level; _⊔_; Lift)
open import Data.Empty
open import Data.Product using (∃; _,_; -,_)
open import Data.Sum.Base using (_⊎_; [_,_]′; inj₁; inj₂)
open import Function.Equivalence using (_⇔_; equivalence)
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Nullary.Sum using (_⊎-dec_)
open import Relation.Unary  as U
open import Relation.Binary as B using (Rel)

open import Data.List.Fresh.Relation.Unary.Any 
open import Data.List.Fresh using (List#; []; cons; _∷#_; _#_)
open import Relation.Binary.PropositionalEquality hiding ( [_] ) 

private
  variable
    ax px rx ay py ry az pz rz : Level
    AX : Set ax
    AY : Set ay
    AZ : Set az

module _ {AX : Set ax} {RX : Rel AX rx} (PX : Pred AX px) {AY : Set ay} {RY : Rel AY ry} (PY : Pred AY py) {AZ : Set az} {RZ : Rel AZ rz} (PZ : Pred AZ pz) where

        -------------
        FLinsert : AZ → List# AZ RZ  → List# AZ RZ
        FLfresh :  (a x : AZ ) → (y :  List# AZ RZ ) → RZ a x
             -- → # AZ ? a y → fresh AZ ? a (FLinsert x y)
        FLinsert = {!!}
        FLfresh = {!!}

        x∈FLins : (x : AZ)    → (xs : List# AZ RZ)  → Any (x ≡_) (FLinsert x xs)
        x∈FLins = {!!}
        insAny :  {x h : AZ } → (xs : List# AZ RZ)  → Any (x ≡_) xs → Any (x ≡_) (FLinsert h xs)
        insAny = {!!}

--        FLinsert {zero} f0 y = f0 ∷# []
--        FLinsert {suc n} x [] = x ∷# []
--        FLinsert {suc n} x (cons a y x₁) with FLcmp x a
--        ... | tri≈ ¬a b ¬c  = cons a y x₁
--        ... | tri< lt ¬b ¬c  = cons x ( cons a y x₁) ( Level.lift (fromWitness lt ) , ttf lt y  x₁) 
--        FLinsert {suc n} x (cons a [] x₁) | tri> ¬a ¬b lt  = cons a ( x  ∷# []  ) ( Level.lift (fromWitness lt) , Level.lift tt )
--        FLinsert {suc n} x (cons a y yr)  | tri> ¬a ¬b a<x = cons a (FLinsert x y) (FLfresh a x y a<x yr )
--
--        FLfresh a x [] a<x (Level.lift tt) = Level.lift (fromWitness a<x) , Level.lift tt
--        FLfresh a x (cons b [] (Level.lift tt)) a<x (Level.lift a<b , a<y) with FLcmp x b
--        ... | tri< x<b ¬b ¬c  = Level.lift (fromWitness a<x) , Level.lift a<b , Level.lift tt
--        ... | tri≈ ¬a refl ¬c = Level.lift (fromWitness a<x) , Level.lift tt
--        ... | tri> ¬a ¬b b<x =  Level.lift a<b  ,  Level.lift (fromWitness  (f<-trans (toWitness a<b) b<x))  , Level.lift tt
--        FLfresh a x (cons b y br) a<x (Level.lift a<b , a<y) with FLcmp x b
--        ... | tri< x<b ¬b ¬c =  Level.lift (fromWitness a<x) , Level.lift a<b , ttf (toWitness a<b) y br
--        ... | tri≈ ¬a refl ¬c = Level.lift (fromWitness a<x) , ttf a<x y br
--        FLfresh a x (cons b [] br) a<x (Level.lift a<b , a<y) | tri> ¬a ¬b b<x =
--            Level.lift a<b , Level.lift (fromWitness (f<-trans (toWitness a<b) b<x)) , Level.lift tt
--        FLfresh a x (cons b (cons a₁ y x₁) br) a<x (Level.lift a<b , a<y) | tri> ¬a ¬b b<x =
--            Level.lift a<b , FLfresh a x (cons a₁ y x₁) a<x a<y


        -- all cobmbination in P and Q (could be more general)
        record AnyPair (X :  List# AX RX ) (Y :  List# AY RY ) (fpq : (p : AX) (q : AY) → AZ) : Set 
                         (ax  ⊔ px  ⊔ rx  ⊔ ay  ⊔ py  ⊔ ry  ⊔ az  ⊔ pz  ⊔ rz ) where
           field
             pairList :   List# AZ RZ 
             pairAny : (p : AX) (q : AY)
                 → Any ( p ≡_ ) X →  Any ( q ≡_ ) Y
                 → Any (fpq p q ≡_) pairList

        -------------
        --    (p,q)   (p,qn) ....           (p,q0)
        --    pn,q       
        --     :        AnyPair FL0 FL0 P  Q
        --    p0,q       

        open AnyPair 
        anyPair : (P : List# AX RX) (Q : List# AY RY) → (fpq : (p : AX) (q : AY) → AZ)  → AnyPair P Q fpq
        anyPair [] [] _ = record { pairList = [] ; pairAny = λ _ _ () }
        anyPair [] (cons q Q qr) _ = record { pairList = [] ; pairAny = λ _ _ () }
        anyPair (cons p P pr) [] _ = record { pairList = [] ; pairAny = λ _ _ _ () }
        anyPair (cons p P pr) (cons q Q qr) fpq = record { pairList = FLinsert (fpq p q) (pairListQ Q)  ; pairAny = anyc0n } where 
          pairListP : (P1 : List# AX RX) → List# AZ RZ
          pairListP [] = pairList (anyPair P Q fpq)
          pairListP (cons p₁ P1 x) =  FLinsert (fpq p₁ q) (pairListP P1)
          pairListQ : (Q1 : List# AY RY) → List# AZ RZ
          pairListQ [] = pairListP P
          pairListQ (cons q₁ Q1 qr₁) = FLinsert (fpq p q₁) (pairListQ Q1)
          anyc0n : (p₁ : AX) (q₁ : AY) → Any (_≡_ p₁) (cons p P pr) → Any (_≡_ q₁) (cons q Q qr)
            → Any (_≡_ (fpq p₁ q₁)) (FLinsert (fpq p q) (pairListQ Q))
          anyc0n p₁ q₁ (here refl) (here refl) = x∈FLins _ (pairListQ Q )
          anyc0n p₁ q₁ (here refl) (there anyq) = insAny (pairListQ Q) (anyc01 Q anyq) where 
             anyc01 : (Q1 : List# AY RY) → Any (_≡_ q₁) Q1 → Any (_≡_ (fpq p₁ q₁)) (pairListQ Q1)
             anyc01 (cons q Q1 qr₂) (here refl) = x∈FLins _ _
             anyc01 (cons q₂ Q1 qr₂) (there any) = insAny _ (anyc01 Q1 any)
          anyc0n p₁ q₁ (there anyp) (here refl) = insAny _ (anyc02 Q) where
             anyc03 : (P1 : List# AX RX) → Any (_≡_ p₁) P1  → Any (_≡_ (fpq p₁ q₁)) (pairListP P1)
             anyc03 (cons a P1 x) (here refl) = x∈FLins _ _ 
             anyc03 (cons a P1 x) (there any) = insAny _ ( anyc03 P1 any) 
             anyc02 : (Q1 : List# AY RY) → Any (_≡_ (fpq p₁ q₁)) (pairListQ Q1)
             anyc02 [] = anyc03 P anyp
             anyc02 (cons a Q1 x) = insAny _ (anyc02 Q1)
          anyc0n p₁ q₁ (there anyp) (there anyq) = insAny (pairListQ Q) (anyc04 Q) where
             anyc05 : (P1 : List# AX RX) → Any (_≡_ (fpq p₁ q₁)) (pairListP P1)
             anyc05 [] = pairAny (anyPair P Q fpq) p₁ q₁ anyp anyq
             anyc05 (cons a P1 x) = insAny _ (anyc05 P1)
             anyc04 : (Q1 : List# AY RY) → Any (_≡_ (fpq p₁ q₁)) (pairListQ Q1)
             anyc04 [] = anyc05 P 
             anyc04 (cons a Q1 x) = insAny _ (anyc04 Q1)

