{-# OPTIONS --cubical-compatible  --safe #-}
open import Level hiding ( suc ; zero )
module sym2n where

open import Symmetric 
open import Data.Unit
open import Data.Nat hiding (_⊔_) -- using (ℕ; suc; zero)

open import Gutil 
open import Putil 
open import Solvable using (solvable)
open import  Relation.Binary.PropositionalEquality hiding ( [_] )

open import Data.Fin
open import Data.Fin.Permutation 

open import FLutil
open import Data.List.Fresh 
open import Data.List.Fresh.Relation.Unary.Any
open import FLComm
open import Data.List 

sym2solvable : solvable (Symmetric 2)
solvable.dervied-length sym2solvable = 1
solvable.end sym2solvable x d = solved1 x d where

   open Solvable (Symmetric 2)

   p0id :  FL→perm ((# 0) :: ((# 0) :: f0)) =p= pid
   p0id = pleq _ _ refl

   stage2FList : CommFListN 2 1 ≡ cons (zero :: zero :: f0) [] (Level.lift tt)
   stage2FList = refl

   solved1 :  (x : Permutation 2 2) → deriving 1 x → x =p= pid
   solved1 x dr = CommSolved 2 x ( CommFListN 2 1 ) stage2FList p0id solved0 where
      solved0 : Any (perm→FL x ≡_) ( CommFListN 2 1 )
      solved0 = CommStage→ 2 1 x dr


