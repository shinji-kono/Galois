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

   p0id :  FL→perm ((# 0) :: ((# 0) :: ((# 0 ) :: f0))) =p= pid
   p0id = pleq _ _ refl 

   p0 =  FL→perm ((# 0) :: ((# 0) :: ((# 0 ) :: f0))) 
   p1 =  FL→perm ((# 0) :: ((# 1) :: ((# 0 ) :: f0))) 
   p2 =  FL→perm ((# 1) :: ((# 0) :: ((# 0 ) :: f0))) 
   p3 =  FL→perm ((# 1) :: ((# 1) :: ((# 0 ) :: f0))) 
   p4 =  FL→perm ((# 2) :: ((# 0) :: ((# 0 ) :: f0))) 
   p5 =  FL→perm ((# 2) :: ((# 1) :: ((# 0 ) :: f0))) 
   t0  =  plist p0 ∷ plist p1 ∷  plist p2 ∷ plist p3 ∷ plist p4 ∷  plist p5 ∷ [] 

   t1  =  plist [ p0 , p0 ] ∷ plist [ p1 , p0 ] ∷  plist [ p2 , p0 ] ∷ plist [ p3 , p0 ] ∷ plist [ p4 , p0 ] ∷  plist [ p5 , p1 ] ∷ 
          plist [ p0 , p1 ] ∷ plist [ p1 , p1 ] ∷  plist [ p2 , p1 ] ∷ plist [ p3 , p1 ] ∷ plist [ p4 , p1 ] ∷  plist [ p5 , p1 ] ∷ 
          plist [ p0 , p2 ] ∷ plist [ p1 , p2 ] ∷  plist [ p2 , p2 ] ∷ plist [ p3 , p2 ] ∷ plist [ p4 , p2 ] ∷  plist [ p5 , p2 ] ∷ 
          plist [ p0 , p3 ] ∷ plist [ p1 , p3 ] ∷  plist [ p3 , p3 ] ∷ plist [ p3 , p3 ] ∷ plist [ p4 , p3 ] ∷  plist [ p5 , p3 ] ∷ 
          plist [ p0 , p4 ] ∷ plist [ p1 , p4 ] ∷  plist [ p3 , p4 ] ∷ plist [ p3 , p4 ] ∷ plist [ p4 , p4 ] ∷  plist [ p5 , p4 ] ∷ 
          plist [ p0 , p5 ] ∷ plist [ p1 , p5 ] ∷  plist [ p3 , p5 ] ∷ plist [ p3 , p5 ] ∷ plist [ p4 , p4 ] ∷  plist [ p5 , p5 ] ∷ 
          []

   open _=p=_
   
   stage1 :  (x : Permutation 3 3) →  Set (Level.suc Level.zero)
   stage1 x = Commutator (λ x₂ → Lift (Level.suc Level.zero) ⊤)  x 

   open import logic
   
   stage12  :  (x : Permutation 3 3) → stage1 x →  ( x =p= pid ) ∨ ( x =p= p3 ) ∨ ( x =p= p4 )
   stage12 x uni = case1 prefl
   stage12 x (comm x1 y1 ) = {!!}
   stage12 _ (gen {x} {y} sx sy) with stage12 x sx | stage12 y sy --  x =p= pid : t , y =p= pid : s
   ... | case1 t | case1 s = case1 ( {!!} )
   ... | case1 t | case2 (case1 x₁) = {!!}
   ... | case1 t | case2 (case2 x₁) = {!!}
   ... | case2 t | case1 s = {!!}
   ... | case2 (case1 s) | case2 (case1 t) = case2 (case2 (pleq _ _ {!!} ))
   ... | case2 (case1 s) | case2 (case2 t) = {!!}
   ... | case2 (case2 s) | case2 (case1 t) = {!!}
   ... | case2 (case2 s) | case2 (case2 t) = {!!}
   stage12 _ (ccong {y} x=y sx) with stage12 y sx
   ... | case1 id = case1 ( ptrans (psym x=y ) id )
   ... | case2 (case1 x₁) = case2 (case1 ( ptrans (psym x=y ) x₁ ))
   ... | case2 (case2 x₁) = case2 (case2 ( ptrans (psym x=y ) x₁ ))

   solved1 :  (x : Permutation 3 3) →  Commutator (λ x₁ → Commutator (λ x₂ → Lift (Level.suc Level.zero) ⊤) x₁) x → x =p= pid
   solved1 = {!!}
