{-# OPTIONS --allow-unsolved-metas #-}
open import Data.Nat -- using (ℕ; suc; zero; s≤s ; z≤n )
module FLComm (n : ℕ) where

open import Level renaming ( suc to Suc ; zero to Zero ) hiding (lift)
open import Data.Fin hiding ( _<_  ; _≤_ ; _-_ ; _+_ ; _≟_)
open import Data.Fin.Properties hiding ( <-trans ; ≤-refl ; ≤-trans ; ≤-irrelevant ; _≟_ ) renaming ( <-cmp to <-fcmp )
open import Data.Fin.Permutation  
open import Data.Nat.Properties 
open import Relation.Binary.PropositionalEquality hiding ( [_] )
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

open import Data.List.Fresh hiding ([_])
open import Data.List.Fresh.Relation.Unary.Any

open Solvable (Symmetric n)

CommFList  :  FList n →  FList n
CommFList x =  tl2 x x [] where
   tl3 : (FL n) → ( z : FList n) → FList n → FList n
   tl3 h [] w = w
   tl3 h (x ∷# z) w = tl3 h z (FLinsert ( perm→FL [ FL→perm h , FL→perm x ] ) w )
   tl2 : ( x z : FList n) → FList n →  FList n
   tl2 [] _ x = x
   tl2 (h ∷# x) z w = tl2 x z (tl3 h z w)

CommFListN  : ℕ  →  FList n
CommFListN  0 = ∀Flist fmax
CommFListN  (suc i) = CommFList (CommFListN i)

open import Algebra 
open Group (Symmetric n)

CommStage→ : (i : ℕ) → (x : Permutation n n ) → deriving i x → Any (perm→FL x ≡_) ( CommFListN i )
CommStage→ zero x (Level.lift tt) = AnyFList (perm→FL x)
CommStage→ (suc i) x uni = {!!}
CommStage→ (suc i) x (comm {g} {h} p q) = {!!}
CommStage→ (suc i) x (gen {f} {g} p q) = {!!}
CommStage→ (suc i) x (ccong {f} {g} eq p) = {!!}

CommSolved : (x : Permutation n n) → (y : FList n) → y ≡ FL0 ∷# [] → (perm→FL x ≡ FL0 → x =p= pid ) → Any (perm→FL x ≡_) y → x =p= pid
CommSolved x .(cons FL0 [] (Level.lift tt)) refl fl0→pid (here eq) = fl0→pid eq
