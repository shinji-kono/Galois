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
solvable.end sym4solvable x d = solved1 x {!!} where

   open import Data.List using ( List ; [] ; _∷_ )

   open Solvable (Symmetric 4)
   -- open Group (Symmetric 2) using (_⁻¹)

   open _=p=_

   -- Klien
   --
   --  1                     (1,2),(3,4)           (1,3),(2,4)           (1,4),(2,3)
   --  0 ∷ 1 ∷ 2 ∷ 3 ∷ [] ,  1 ∷ 0 ∷ 3 ∷ 2 ∷ [] ,  2 ∷ 3 ∷ 0 ∷ 1 ∷ [] ,  3 ∷ 2 ∷ 1 ∷ 0 ∷ [] ,  


   data Klein : (x : Permutation 4 4 ) → Set where
       kid : Klein pid
       ka  : Klein (pswap (pswap pid))
       kb  : Klein (pid {4} ∘ₚ pins (n≤ 3) ∘ₚ pins (n≤ 3 ) )
       kc  : Klein (pins (n≤ 3)  ∘ₚ  pins (n≤ 2) ∘ₚ pswap (pid {2}))

   a0 =  pid {4}
   a1 =  pswap (pswap (pid {0}))
   a2 =  pid {4} ∘ₚ pins (n≤ 3) ∘ₚ pins (n≤ 3 ) 
   a3 =  pins (n≤ 3)  ∘ₚ  pins (n≤ 2) ∘ₚ pswap (pid {2})

   --   1 0  
   --   2 1 0 
   --   3 2 1 0

   k1 : { x :  Permutation 4 4 } → Klein x → List ℕ
   k1 {x} kid = plist x
   k1 {x} ka = plist x
   k1 {x} kb = plist x
   k1 {x} kc = plist x

   k2 = k1 kid ∷ k1 ka ∷ k1 kb ∷ k1 kc ∷ []
   k3 = plist  (a1  ∘ₚ a2 ) ∷ plist (a1 ∘ₚ a3)  ∷ plist (a2 ∘ₚ a1 ) ∷  []

   p0id :  FL→perm ((# 0) :: ((# 0) :: ((# 0 ) :: f0))) =p= pid
   p0id = pleq _ _ refl

   -- stage 1 (A4)
   p0 =  (zero :: zero :: zero :: zero :: f0 )
   p1 =  (zero :: suc zero :: suc zero :: zero :: f0 )
   p2 =  (zero :: suc (suc zero) :: zero :: zero :: f0 )
   p3 =  (suc zero :: zero :: suc zero :: zero :: f0 )
   p4 =  (suc zero :: suc zero :: zero :: zero :: f0 ) 
   p5 =  (suc zero :: suc (suc zero) :: suc zero :: zero :: f0 )
   p6 =  (suc (suc zero) :: zero :: zero :: zero :: f0 )
   p7 =  (suc (suc zero) :: suc zero :: suc zero :: zero :: f0 )
   p8 =  (suc (suc zero) :: suc (suc zero) :: zero :: zero :: f0 )
   p9 =  (suc (suc (suc zero)) :: zero :: suc zero :: zero :: f0 )
   pa =  (suc (suc (suc zero)) :: suc zero :: zero :: zero :: f0 )
   pb =  (suc (suc (suc zero)) :: suc (suc zero) :: suc zero :: zero :: f0 )

   t0  =  plist (FL→perm p0 ) ∷ plist (FL→perm p1 ) ∷  plist (FL→perm p2 ) ∷ plist (FL→perm p3 ) ∷ plist (FL→perm p4 ) ∷  plist (FL→perm p5 ) ∷ 
          plist (FL→perm p6 ) ∷ plist (FL→perm p7 ) ∷  plist (FL→perm p8 ) ∷ plist (FL→perm p9 ) ∷ plist (FL→perm pa ) ∷  plist (FL→perm pb ) ∷ []

   t1  : List (FL 4) →  List (FL 4) 
   t1  x =  tl2 x x [] where
       tl3 : (FL 4) → ( z : List (FL 4)) → List (FL 4) → List (FL 4)
       tl3 h [] w = w
       tl3 h (x ∷ z) w = tl3 h z (( perm→FL [ FL→perm h , FL→perm x ] ) ∷ w )
       tl2 : ( x z : List (FL 4)) → List (FL 4) →  List (FL 4)
       tl2 [] _ x = x
       tl2 (h ∷ x) z w = tl2 x z (tl3 h z w)

   stage1  :  List (FL 4)
   stage1  =  t1 ( ∀-FL 3 ) 

   -- stage2 ( Kline )
   --  k0  p0  zero :: zero :: zero :: zero :: f0 ∷                                   (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ∷
   --  k1  p3  suc zero :: zero :: suc zero :: zero :: f0 ∷                           (1 ∷ 0 ∷ 3 ∷ 2 ∷ []) ∷
   --  k2  p8  suc (suc zero) :: suc (suc zero) :: zero :: zero :: f0 ∷               (2 ∷ 3 ∷ 0 ∷ 1 ∷ []) 
   --  k3  pb  suc (suc (suc zero)) :: suc (suc zero) :: suc zero :: zero :: f0 ∷     (3 ∷ 2 ∷ 1 ∷ 0 ∷ [])

   tb = plist ( FL→perm p0) ∷ plist ( FL→perm p3) ∷ plist ( FL→perm p8) ∷ plist ( FL→perm pb) ∷ []

   stage2  :   List (FL 4)
   stage2   =  t1 ( p0 ∷ p1 ∷ p2 ∷ p3 ∷ p4 ∷ p5 ∷ p6 ∷ p7 ∷ p8 ∷ p9 ∷ pa ∷ pb ∷ [] ) 
   
   solved1 :  (x : Permutation 4 4) →  Commutator (λ x₁ → Commutator (λ x₂ → Lift (Level.suc Level.zero) ⊤) x₁) x → x =p= pid
   solved1 = {!!}
