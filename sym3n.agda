open import Level hiding ( suc ; zero )
open import Algebra
module sym3n where

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


sym3solvable : solvable (Symmetric 3)
solvable.dervied-length sym3solvable = 2
solvable.end sym3solvable x d = solved1 x d where

   open import Data.List using ( List ; [] ; _∷_ )

   open Solvable (Symmetric 3)
   open import FLutil
   open import Data.List.Fresh hiding ([_])
   open import Relation.Nary using (⌊_⌋)

   p0id :  FL→perm ((# 0) :: ((# 0) :: ((# 0 ) :: f0))) =p= pid
   p0id = pleq _ _ refl

   open import Data.List.Fresh.Relation.Unary.Any
   open import FLComm

   stage3FList : CommFListN 3 2 ≡ cons (zero :: zero :: zero :: f0) [] (Level.lift tt)
   stage3FList = refl

   solved1 :  (x : Permutation 3 3) → deriving 2 x → x =p= pid
   solved1 x dr = CommSolved 3 x ( CommFListN 3 2 ) stage3FList pf solved2 where
      --    p0id :  FL→perm ((# 0) :: ((# 0) :: ((# 0 ) :: f0))) =p= pid
      pf : perm→FL x ≡ FL0 → x =p= pid
      pf eq = ptrans pf2 (ptrans pf0 p0id ) where
         pf2 : x =p= FL→perm (perm→FL x)
         pf2 = psym (FL←iso x)
         pf0 : FL→perm (perm→FL x) =p= FL→perm FL0
         pf0 = pcong-Fp eq
      solved2 : Any (perm→FL x ≡_) ( CommFListN 3 2 )
      solved2 = CommStage→ 3 2 x dr


