{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Nat -- using (ℕ; suc; zero; s≤s ; z≤n )
module FLComm (n : ℕ) where

open import Level renaming ( suc to Suc ; zero to Zero ) hiding (lift)
open import Data.Fin hiding ( _<_  ; _≤_ ; _-_ ; _+_ ; _≟_)
open import Data.Fin.Properties hiding ( <-trans ; ≤-refl ; ≤-trans ; ≤-irrelevant ; _≟_ ) renaming ( <-cmp to <-fcmp )
open import Data.Fin.Permutation  
open import Data.Nat.Properties 
open import Relation.Binary.PropositionalEquality hiding ( [_] ) renaming ( sym to ≡-sym )
open import Data.List using (List; []; _∷_ ; length ; _++_ ; tail ) renaming (reverse to rev )
open import Data.Product hiding (_,_ )
open import Relation.Nullary 
open import Data.Unit
open import Data.Empty
open import  Relation.Binary.Core 
open import  Relation.Binary.Definitions hiding (Symmetric )
open import logic
open import nat

open import FLutil
open import Putil
import Solvable 
open import Symmetric

-- infixr  100 _::_

open import Relation.Nary using (⌊_⌋)
open import Data.List.Fresh hiding ([_])
open import Data.List.Fresh.Relation.Unary.Any

open Solvable (Symmetric n) 

tl3 : (FL n) → ( z : FList n) → FList n → FList n
tl3 h [] w = w
tl3 h (x ∷# z) w = tl3 h z (FLinsert ( perm→FL [ FL→perm h , FL→perm x ] ) w )
tl2 : ( x z : FList n) → FList n →  FList n
tl2 [] _ x = x
tl2 (h ∷# x) z w = tl2 x z (tl3 h z w)

CommFList  :  FList n →  FList n
CommFList x =  tl2 x x [] 

CommFListN  : ℕ  →  FList n
CommFListN  0 = ∀Flist fmax
CommFListN  (suc i) = CommFList (CommFListN i)

open import Algebra 
open Group (Symmetric n) hiding (refl)

open _∧_

-- {-# TERMINATING #-}
CommStage→ : (i : ℕ) → (x : Permutation n n ) → deriving i x → Any (perm→FL x ≡_) ( CommFListN i )
CommStage→ zero x (Level.lift tt) = AnyFList (perm→FL x)
CommStage→ (suc i) .( [ g , h ] ) (comm {g} {h} p q) = comm2 (CommFListN i) (CommFListN i) (CommStage→ i g p) (CommStage→ i h q) [] where
   G = perm→FL g
   H = perm→FL h

   -- tl3 case
   commc :  (L3 L1 : FList n) →  Any (_≡_ (perm→FL [  FL→perm G , FL→perm H ])) L3 
           →  Any (_≡_ (perm→FL [ FL→perm G , FL→perm H ])) (tl3 G L1 L3)
   commc L3 [] any = any
   commc L3 (cons a L1 _) any = commc (FLinsert (perm→FL [ FL→perm G , FL→perm a ]) L3) L1 (insAny _ any)
   comm6 : perm→FL [ FL→perm G , FL→perm H ] ≡ perm→FL [ g , h ]
   comm6 = pcong-pF (comm-resp (FL←iso _) (FL←iso _))  
   comm3 : (L1 : FList n) → Any (H ≡_) L1 → (L3 : FList n) → Any (_≡_ (perm→FL [ g , h ])) (tl3 G L1 L3)
   comm3 (H ∷# []) (here refl) L3 = subst (λ k → Any (_≡_  k) (FLinsert (perm→FL [ FL→perm G , FL→perm H ]) L3 ) )
       comm6 (x∈FLins ( perm→FL [ FL→perm G , FL→perm H ] ) L3 )
   comm3 (cons H L1 x₁) (here refl) L3 = subst (λ k → Any (_≡_ k) (tl3 G L1 (FLinsert (perm→FL [ FL→perm G , FL→perm H ]) L3))) comm6
       (commc (FLinsert (perm→FL [ FL→perm G , FL→perm H ]) L3 ) L1 (x∈FLins ( perm→FL [ FL→perm G , FL→perm H ] ) L3))
   comm3 (cons a L  _) (there b) L3 = comm3 L b (FLinsert (perm→FL [ FL→perm G , FL→perm a ]) L3)

   -- tl2 case
   comm2 : (L L1 : FList n) → Any (G ≡_) L → Any (H ≡_) L1 → (L3 : FList n) → Any (perm→FL [ g , h ]  ≡_) (tl2 L L1 L3)
   comm2 (cons G L xr) L1 (here refl) b L3 = comm7 L L3 where
       comm8 : (L L4 L2 : FList n) → (a : FL n) 
            → Any (_≡_ (perm→FL [ g , h ])) (tl2 L4 L1 L2)
            → Any (_≡_ (perm→FL [ g , h ])) (tl2 L4 L1 (tl3 a L L2))
       comm8← : (L L4 L2 : FList n) → (a : FL n)  → ¬ ( a ≡ perm→FL g )
           →  Any (_≡_ (perm→FL [ g , h ])) (tl2 L4 L1 (tl3 a L L2))
           →  Any (_≡_ (perm→FL [ g , h ])) (tl2 L4 L1 L2)
       comm9← : (L4 L2 : FList n) → (a a₁ : FL n) → ¬ ( a ≡ perm→FL g )
           → Any (_≡_ (perm→FL [ g , h ])) (tl2 L4 L1 (FLinsert (perm→FL [ FL→perm a , FL→perm a₁ ]) L2))
           → Any (_≡_ (perm→FL [ g , h ])) (tl2 L4 L1 L2) 
       --  Any (_≡_ (perm→FL [ g , h ])) (FLinsert (perm→FL [ FL→perm a , FL→perm a₁ ]) L2) → Any (_≡_ (perm→FL [ g , h ])) L2
       comm9← [] L2 a a₁ not any = {!!}
       comm9← (cons a₂ L4 x) L2 a a₁ not any = comm8 L1 L4 L2 a₂
           (comm9← L4 L2 a a₁ not
           (comm8← L1 L4 (FLinsert (perm→FL [ FL→perm a , FL→perm a₁ ]) L2 ) a₂ {!!} any)) 
       -- Any (_≡_ (perm→FL [ g , h ])) (tl2 L4 L1 (tl3 a₂ L1 (FLinsert (perm→FL [ FL→perm a , FL→perm a₁ ]) L2))) →
       -- Any (_≡_ (perm→FL [ g , h ])) (tl2 L4 L1 (FLinsert (perm→FL [ FL→perm a , FL→perm a₁ ]) L2))
       -- Any (_≡_ (perm→FL [ g , h ])) (tl2 L4 L1 L2)
       -- Any (_≡_ (perm→FL [ g , h ])) (tl2 L4 L1 (tl3 a₂ L1 L2))
       comm8← [] L4 L2 a _ any = any 
       comm8← (cons a₁ L x) L4 L2 a not any  = comm8← L  L4 L2 a not
            (comm9← L4 (tl3 a L L2 ) a a₁ not (subst (λ k →  Any (_≡_ (perm→FL [ g , h ])) (tl2 L4 L1  k )) {!!} any ))
       -- Any (_≡_ (perm→FL [ g , h ])) (tl2 L4 L1 (tl3 a L (FLinsert (perm→FL [ FL→perm a , FL→perm a₁ ]) L2))) →
       -- Any (_≡_ (perm→FL [ g , h ])) (tl2 L4 L1 (FLinsert (perm→FL [ FL→perm a , FL→perm a₁ ]) (tl3 a L L2)))
       comm9 : (L4 L2 : FList n) → (a a₁ : FL n) → Any (_≡_ (perm→FL [ g , h ])) (tl2 L4 L1 L2) →
                                                   Any (_≡_ (perm→FL [ g , h ])) (tl2 L4 L1 (FLinsert (perm→FL [ FL→perm a , FL→perm a₁ ]) L2))
       comm8 [] L4 L2 a any = any
       comm8 (cons a₁ L x) L4 L2 a any =  comm8 L  L4 (FLinsert (perm→FL [ FL→perm a , FL→perm a₁ ]) L2) a  (comm9 L4 L2 a a₁ any)
       comm9 [] L2 a a₁ any = insAny _ any
       comm9 (cons a₂ L4 x) L2 a a₁ any = comm8 L1 L4 (FLinsert (perm→FL [ FL→perm a , FL→perm a₁ ]) L2) a₂ (comm9 L4 L2 a a₁ (comm8← L1 L4 L2 a₂ {!!} any))
       -- found g, we have to walk thru till the end
       comm7 : (L L3 : FList n) → Any (_≡_ (perm→FL [ g , h ])) (tl2 L L1 (tl3 G L1 L3))
       -- at the end, find h
       comm7 [] L3 = comm3 L1 b L3  
       -- add n path
       comm7 (cons a L4 xr) L3 = comm8 L1 L4 (tl3 G L1 L3) a (comm7 L4 L3)
   -- accumerate tl3
   comm2 (cons x L xr) L1 (there a) b L3 = comm2 L L1 a b (tl3 x L1 L3)
CommStage→ (suc i) x (ccong {f} {x} eq p) = subst (λ k → Any (k ≡_) (tl2 (CommFListN i) (CommFListN i) [])) (comm4 eq) (CommStage→ (suc i) f p ) where
   comm4 : f =p= x →  perm→FL f ≡ perm→FL x
   comm4 = pcong-pF

CommSolved : (x : Permutation n n) → (y : FList n) → y ≡ FL0 ∷# [] → (FL→perm (FL0 {n}) =p= pid ) → Any (perm→FL x ≡_) y → x =p= pid
CommSolved x .(cons FL0 [] (Level.lift tt)) refl eq0 (here eq) = FLpid _ eq eq0
