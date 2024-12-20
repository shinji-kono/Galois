{-# OPTIONS --cubical-compatible #-}
-- {-# OPTIONS --cubical-compatible --safe #-}

open import Level hiding ( suc ; zero )
open import Algebra
module sym3 where

open import Symmetric 
open import Data.Unit
open import Function.Bundles --  as Inverse using (_↔_; Inverse; _InverseOf_)
open import Function
open import Data.Nat hiding (_⊔_) -- using (ℕ; suc; zero)
open import Relation.Nullary
open import Data.Empty
open import Data.Product

open import Gutil 
open import Putil 
open import FLutil 
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

   p33=4 : ( p3  ∘ₚ p3 ) =p= p4
   p33=4 = pleq _ _ refl

   p44=3 : ( p4  ∘ₚ p4 ) =p= p3
   p44=3 = pleq _ _ refl

   p34=0 : ( p3  ∘ₚ p4 ) =p= pid
   p34=0 = pleq _ _ refl

   p43=0 : ( p4  ∘ₚ p3 ) =p= pid
   p43=0 = pleq _ _ refl

   com33 : [ p3 , p3 ] =p= pid
   com33 = pleq _ _ refl

   com44 : [ p4 , p4 ] =p= pid
   com44 = pleq _ _ refl

   com34 : [ p3 , p4 ] =p= pid
   com34 = pleq _ _ refl

   com43 : [ p4 , p3 ] =p= pid
   com43 = pleq _ _ refl


   pFL : ( g : Permutation 3 3) → { x : FL 3 } →  perm→FL g ≡ x → g =p=  FL→perm x
   pFL g {x} refl = ptrans (psym (FL←iso g)) ( FL-inject refl ) 

   open ≡-Reasoning

--   st00 = perm→FL [ FL→perm ((suc zero) :: (suc zero :: (zero :: f0 ))) , FL→perm  ((suc (suc zero)) :: (suc zero) :: (zero :: f0))  ]

--   st02 :  ( g h : Permutation 3 3) →  ([ g , h ] =p= pid) ∨ ([ g , h ] =p= p3) ∨ ([ g , h ] =p= p4)
--   st02 g h with perm→FL g | perm→FL h  
--   ... | x :: s | t = ?

--  we can do everything in FL 3, but we give it up now
--    sym3n is enough

--   st02 :  ( g h : FL 3) →  ([ FL→perm g , FL→perm h ] =p= pid) ∨ ([ FL→perm g , FL→perm h ] =p= p3) ∨ ([ FL→perm g , FL→perm h ] =p= p4)
--   st02 (zero :: (zero :: (zero :: f0)))  h = 
--      case1 (ptrans (comm-resp {FL→perm (zero :: (zero :: (zero :: f0)))} {FL→perm h} {pid} {_} (pleq _ _ refl) prefl) (idcomtl (FL→perm h) ))
-- st02 (zero :: (suc zero :: (zero :: f0)))  h = ?
-- st02 (suc zero :: (zero :: (zero :: f0)))  h = ?
-- st02 (suc zero :: (suc zero :: (zero :: f0)))  h = ?
-- st02 (suc (suc zero) :: (zero :: (zero :: f0)))  h = ?
-- st02 (suc (suc zero) :: (suc zero :: (zero :: f0)))  h = ?
    

--   stage12  :  (x : Permutation 3 3) → stage1 x →  ( x =p= pid ) ∨ ( x =p= p3 ) ∨ ( x =p= p4 )
--   stage12 x (comm {g} {h} x1 y1 eq ) = ? -- st02 g h

--   solved2 : (x : Permutation 3 3) →  Commutator (λ x₁ → Commutator (λ x₂ → Lift (Level.suc Level.zero) ⊤) x₁) x → x =p= pid
--   solved2 z (comm {g} {h} {z} x y eq) with st02 (perm→FL g) (perm→FL h )
--   ... | t = ?    this will take more than 16GB memory

   solved1 : (x : Permutation 3 3) →  Commutator (λ x₁ → Commutator (λ x₂ → Lift (Level.suc Level.zero) ⊤) x₁) x → x =p= pid
   solved1 z (comm {g} {h} {z} x y eq) with perm→FL g | perm→FL h 
   ... | (zero :: (zero :: (zero :: f0)))  | (zero :: (zero :: (zero :: f0)))  = ?
   ... | (zero :: (zero :: (zero :: f0)))  | (zero :: (suc zero :: (zero :: f0)))  = ?
   ... | (zero :: (zero :: (zero :: f0)))  | (suc zero :: (zero :: (zero :: f0)))  = ?
   ... | (zero :: (zero :: (zero :: f0)))  | (suc zero :: (suc zero :: (zero :: f0)))  = ?
   ... | (zero :: (zero :: (zero :: f0)))  | (suc (suc zero) :: (zero :: (zero :: f0)))  = ?
   ... | (zero :: (zero :: (zero :: f0)))  | (suc (suc zero) :: (suc zero :: (zero :: f0)))  = ?

   ... | (zero :: (suc zero :: (zero :: f0)))  | (zero :: (zero :: (zero :: f0)))  = ?
   ... | (zero :: (suc zero :: (zero :: f0)))  | (zero :: (suc zero :: (zero :: f0)))  = ?
   ... | (zero :: (suc zero :: (zero :: f0)))  | (suc zero :: (zero :: (zero :: f0)))  = ?
   ... | (zero :: (suc zero :: (zero :: f0)))  | (suc zero :: (suc zero :: (zero :: f0)))  = ?
   ... | (zero :: (suc zero :: (zero :: f0)))  | (suc (suc zero) :: (zero :: (zero :: f0)))  = ?
   ... | (zero :: (suc zero :: (zero :: f0)))  | (suc (suc zero) :: (suc zero :: (zero :: f0)))  = ?

   ... | (suc zero :: (zero :: (zero :: f0)))  | s = ?
   ... | (suc zero :: (suc zero :: (zero :: f0)))  | s = ?
   ... | (suc (suc zero) :: (zero :: (zero :: f0)))  | s = ?
   ... | (suc (suc zero) :: (suc zero :: (zero :: f0)))  | s = ?

