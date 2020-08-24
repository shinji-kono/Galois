open import Level hiding ( suc ; zero )
open import Algebra
module sym3 where

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
open import Data.Fin.Permutation

sym3solvable : solvable (Symmetric 3)
solvable.dervied-length sym3solvable = 2
solvable.end sym3solvable x d = solved1 x d where

   open import Data.List using ( List ; [] ; _∷_ )

   open Solvable (Symmetric 3)
   -- open Group (Symmetric 2) using (_⁻¹)

   p0 :  FL→perm ((# 0) :: ((# 0) :: ((# 0 ) :: f0))) =p= pid
   p0 = record { peq = p00 } where
      p00 : (q : Fin 3) → (FL→perm ((# 0) :: ((# 0) :: ((# 0) :: f0))) ⟨$⟩ʳ q) ≡ (pid ⟨$⟩ʳ q)
      p00 zero = refl
      p00 (suc zero) = refl
      p00 (suc (suc zero)) = refl

   open _=p=_
   
   solved1 :  (x : Permutation 3 3) →  Commutator (λ x₁ → Commutator (λ x₂ → Lift (Level.suc Level.zero) ⊤) x₁) x → x =p= pid
   solved1 = {!!}
