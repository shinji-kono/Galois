{-# OPTIONS --guardedness #-}

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

open import Data.Nat.Base
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_; lines)
open import Data.Unit.Polymorphic as DP hiding (⊤)
open import IO


infixr  200 _∘ₚ_
_∘ₚ_ = Data.Fin.Permutation._∘ₚ_

-- open import IO
open import Data.String hiding (toList)
open import Data.Unit
open import Agda.Builtin.String 

sym5solvable : (n : ℕ) → String -- ¬ solvable (Symmetric 5)
sym5solvable n = FListtoStr (CommFListN 5 n) where

   open import Data.List using ( List ; [] ; _∷_ )
   open Solvable (Symmetric 5)

   open import FLutil
   open import Data.List.Fresh hiding ([_])
   open import Relation.Nary using (⌊_⌋)

   p0id :  FL→perm (zero :: zero :: zero :: (zero :: (zero :: f0))) =p= pid
   p0id = pleq _ _ refl

   open import Data.List.Fresh.Relation.Unary.Any
   open import FLComm


   stage4FList = CommFListN 5 0 
   stage6FList = CommFListN 5 3 

   -- stage5FList = {!!}
   -- s2=s3 :  CommFListN 5 2 ≡ CommFListN 5 3 
   -- s2=s3 = refl

   FLtoStr : {n : ℕ} → (x : FL n) → String
   FLtoStr f0 = "f0"
   FLtoStr (x :: y) = primStringAppend ( primStringAppend (primShowNat (toℕ x)) " :: " ) (FLtoStr y)

   FListtoStr : {n : ℕ} → (x : FList n) → String
   FListtoStr [] = ""
   FListtoStr (cons a x x₁) = primStringAppend (FLtoStr a) (primStringAppend "\n" (FListtoStr x))

-- open import Codata.Musical.Notation
open import Data.Maybe hiding (_>>=_)
open import Data.List  
open import Data.Char  
-- open import IO.Primitive
-- open import Codata.Musical.Costring

postulate
    getArgs : IO (List (List Char))
{-# FOREIGN GHC import qualified System.Environment #-}
{-# COMPILE GHC getArgs = System.Environment.getArgs #-}

charToDigit : Char → Maybe ℕ
charToDigit '0' = just ( 0)
charToDigit '1' = just ( 1)
charToDigit '2' = just ( 2)
charToDigit '3' = just ( 3)
charToDigit '4' = just ( 4)
charToDigit '5' = just ( 5)
charToDigit '6' = just ( 6)
charToDigit '7' = just ( 7)
charToDigit '8' = just ( 8)
charToDigit '9' = just ( 9)
charToDigit _   = nothing

getNumArg1 : (List (List Char)) → ℕ
getNumArg1 [] = 0
getNumArg1 ([] ∷ y) = 0
getNumArg1 ((x ∷ _) ∷ y) with charToDigit x
... | just n = n
... | nothing  = 0


--
-- CommFListN 5 x is too slow use compiler
-- agda --compile sym5n.agda
--

main : IO {0ℓ} DP.⊤
main = getArgs >>= (λ x →  putStrLn $ sym5solvable $ getNumArg1 x ) 


