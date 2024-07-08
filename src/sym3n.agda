{-# OPTIONS --cubical-compatible --safe #-}

open import Level hiding ( suc ; zero )
open import Algebra
module sym3n where

open import Symmetric 
open import Data.Unit
open import Function
open import Data.Nat hiding (_⊔_) -- using (ℕ; suc; zero)

open import Gutil 
open import Putil 
open import Solvable using (solvable)
open import  Relation.Binary.PropositionalEquality hiding ( [_] )

open import Data.Fin
open import Data.Fin.Permutation 
open import Data.List 
open import FLutil
open import Data.List.Fresh 
open import Relation.Nary 
open import Data.List.Fresh.Relation.Unary.Any
open import FLComm

sym3solvable : solvable (Symmetric 3)
solvable.dervied-length sym3solvable = 2
solvable.end sym3solvable x d = solved1 x d where


   open Solvable (Symmetric 3)

   p0id :  FL→perm ((# 0) :: ((# 0) :: ((# 0 ) :: f0))) =p= pid
   p0id = pleq _ _ refl

   stage3FList : CommFListN 3 2 ≡ cons (zero :: zero :: zero :: f0) [] (Level.lift tt)
   stage3FList = refl

   solved1 :  (x : Permutation 3 3) → deriving 2 x → x =p= pid
   solved1 x dr = CommSolved 3 x ( CommFListN 3 2 ) stage3FList p0id solved2 where
      solved2 : Any (perm→FL x ≡_) ( CommFListN 3 2 )
      solved2 = CommStage→ 3 2 x dr


