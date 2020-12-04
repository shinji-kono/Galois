open import Level hiding ( suc ; zero )
open import Algebra
module sym5n where

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

sym5solvable : ¬ solvable (Symmetric 5)
sym5solvable = {!!} where

   open import Data.List using ( List ; [] ; _∷_ )
   open Solvable (Symmetric 5)

   open import FLutil
   open import Data.List.Fresh hiding ([_])
   open import Relation.Nary using (⌊_⌋)

   p0id :  FL→perm (zero :: zero :: zero :: (zero :: (zero :: f0))) =p= pid
   p0id = pleq _ _ refl

   open import Data.List.Fresh.Relation.Unary.Any
   open import FLComm

   stage4FList = CommFListN 5 2 
 
