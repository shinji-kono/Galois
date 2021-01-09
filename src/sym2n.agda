open import Level hiding ( suc ; zero )
open import Algebra
module sym2n where

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


sym2solvable : solvable (Symmetric 2)
solvable.dervied-length sym2solvable = 1
solvable.end sym2solvable x d = solved1 x d where

   open import Data.List using ( List ; [] ; _∷_ )

   open Solvable (Symmetric 2)
   open import FLutil
   open import Data.List.Fresh hiding ([_])
   open import Relation.Nary using (⌊_⌋)

   p0id :  FL→perm ((# 0) :: ((# 0) :: f0)) =p= pid
   p0id = pleq _ _ refl

   open import Data.List.Fresh.Relation.Unary.Any
   open import FLComm

   stage2FList : CommFListN 2 1 ≡ cons (zero :: zero :: f0) [] (Level.lift tt)
   stage2FList = refl

   solved1 :  (x : Permutation 2 2) → deriving 1 x → x =p= pid
   solved1 x dr = CommSolved 2 x ( CommFListN 2 1 ) stage2FList p0id solved0 where
      solved0 : Any (perm→FL x ≡_) ( CommFListN 2 1 )
      solved0 = CommStage→ 2 1 x dr


