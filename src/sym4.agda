{-# OPTIONS  --safe #-}

open import Level hiding ( suc ; zero )
open import Algebra
module sym4 where

open import Symmetric 
open import Data.Unit
open import Function.Inverse as Inverse using (_↔_; Inverse; _InverseOf_)
open import Function
open import Data.Nat hiding (_⊔_) -- using (ℕ; suc; zero)
open import Relation.Nullary
open import Data.Empty
open import Data.Product

open import Gutil 
open import Putil 
open import Solvable using (solvable)
open import  Relation.Binary.PropositionalEquality hiding ( [_] )

open import Data.Fin
open import Data.Fin.Permutation hiding (_∘ₚ_)

infixr  200 _∘ₚ_
_∘ₚ_ = Data.Fin.Permutation._∘ₚ_

sym4solvable : solvable (Symmetric 4)
solvable.dervied-length sym4solvable = 3
solvable.end sym4solvable x d = solved1 x d where

   open import Data.List using ( List ; [] ; _∷_ )
   open Solvable (Symmetric 4)

   -- Klien
   --
   --  1                     (1,2),(3,4)           (1,3),(2,4)           (1,4),(2,3)
   --  0 ∷ 1 ∷ 2 ∷ 3 ∷ [] ,  1 ∷ 0 ∷ 3 ∷ 2 ∷ [] ,  2 ∷ 3 ∷ 0 ∷ 1 ∷ [] ,  3 ∷ 2 ∷ 1 ∷ 0 ∷ [] ,  

   a0 =  pid {4}
   a1 =  pswap (pswap (pid {0}))
   a2 =  pid {4} ∘ₚ pins (n≤ 3) ∘ₚ pins (n≤ 3 ) 
   a3 =  pins (n≤ 3)  ∘ₚ  pins (n≤ 2) ∘ₚ pswap (pid {2})

   k3 = plist  (a1  ∘ₚ a2 ) ∷ plist (a1 ∘ₚ a3)  ∷ plist (a2 ∘ₚ a1 ) ∷  []

   open import FLutil
   open import Data.List.Fresh hiding ([_])
   open import Relation.Nary using (⌊_⌋)

   p0id :  FL→perm ((# 0) :: (# 0) :: ((# 0) :: ((# 0 ) :: f0))) =p= pid
   p0id = pleq _ _ refl


   open import Data.List.Fresh.Relation.Unary.Any
   open import FLComm

   stage3FList : CommFListN 4 3 ≡ cons (zero :: zero :: zero :: zero :: f0) [] (Level.lift tt)
   stage3FList = refl

   st3 = proj₁ (toList ( CommFListN 4 2 ))
 
   solved1 :  (x : Permutation 4 4) → deriving 3 x → x =p= pid 
   solved1 x dr = CommSolved 4 x ( CommFListN 4 3 ) stage3FList p0id solved2 where
      solved2 : Any (perm→FL x ≡_) ( CommFListN 4 3 )
      solved2 = CommStage→ 4 3 x dr 
