{-# OPTIONS --cubical-compatible  --safe #-}

open import Level hiding ( suc ; zero )
open import Algebra
module sym5h where

open import Symmetric 
open import Data.Unit using (⊤ ; tt )
open import Function.Bundles --  as Inverse using (_↔_; Inverse; _InverseOf_)
open import Function hiding (flip)
open import Data.Nat hiding (_⊔_) -- using (ℕ; suc; zero)
open import Data.Nat.Properties
open import Relation.Nullary
open import Data.Empty
open import Data.Product

open import Gutil 
open import NormalSubgroup
open import Putil 
open import Solvable (Symmetric 5)
open import  Relation.Binary.PropositionalEquality hiding ( [_] )

import Algebra.Morphism.Definitions as MorphismDefinitions
open import Algebra.Morphism.Structures

open import Tactic.MonoidSolver using (solve; solve-macro)
import Algebra.Morphism.Definitions as MorphismDefinitions
open import Algebra.Morphism.Structures

open import Data.Fin hiding (_<_ ; _≤_  ; lift )
open import Data.Fin.Permutation  hiding (_∘ₚ_)

infixr  200 _∘ₚ_
_∘ₚ_ = Data.Fin.Permutation._∘ₚ_

open import Data.List  hiding ( [_] )
open import nat
open import fin
open import logic
open import FLutil
open import Putil

open _∧_

¬sym5solvable : ¬ ( solvable  )
¬sym5solvable sol = counter-example (end5 _ (s02 (dervied-length sol))) where
--
--    dba       1320      d → b → a → d
--    (dba)⁻¹   3021      a → b → d → a
--    aec       21430
--    (aec)⁻¹   41032
--    [ dba , aec ] = (abd)(cea)(dba)(aec) = abc
--
--    dba = (dc)(cba)(cd) = (dc)(abc)⁻¹(cd)     covariant of (abc)⁻¹
--    aec = (eb)(abc) (be)                      covariant of abc
--
--      so commutator always contains abc
--
--      this is not true on commutator group because it is finite generated and it may not a commutator
--      that is even if a commutator group contains abc,  it may not ba commutaor.
--

     open _=p=_
     open ≡-Reasoning
     open solvable
     open import Data.Fin.Properties

     -- a group contains Symmetric 3 as a normal subgroup

     open _=p=_

     -- d   e   b   c   a
     -- 0 ∷ 1 ∷ 3 ∷ 4 ∷ 2 ∷ []
     abc : FL 5
     abc = (# 0) :: ((# 0) :: ((# 2) :: ((# 0) :: ((# 0 ) :: f0))))
     abc-test : plist (FL→perm abc) ≡ 0 ∷ 1 ∷ 3 ∷ 4 ∷ 2 ∷ []
     abc-test = refl

     dc : FL 5
     dc = (# 4) :: ((# 1) :: ((# 1) :: ((# 1) :: ((# 0 ) :: f0))))
     dc-test : plist (FL→perm dc) ≡ 4 ∷ 1 ∷ 2 ∷ 3 ∷ 0 ∷ []
     dc-test = refl

     be : FL 5
     be = (# 0) :: ((# 2) :: ((# 1) :: ((# 0) :: ((# 0 ) :: f0))))
     be-test : plist (FL→perm be) ≡ 0 ∷ 3 ∷ 2 ∷ 1 ∷ 4 ∷ []
     be-test = refl

     s02 : (i : ℕ ) → deriving  i ( FL→perm abc )
     s02 zero = lift tt
     s02 (suc i) = s17 where
           -- [ dba , aec ] = (abd)(cea)(dba)(aec) = abc
           --    dba = (dc)(cba)(cd) = (dc)(abc)⁻¹(cd) 
           --    aec = (eb)(abc) (be)
           s10 : deriving  i ( FL→perm abc )
           s10 = s02 i
           dba : Permutation 5 5
           dba = FL→perm dc ∘ₚ (pinv (FL→perm  abc) ∘ₚ pinv (FL→perm dc) )
           aec : Permutation 5 5
           aec = FL→perm be ∘ₚ (FL→perm abc ∘ₚ pinv (FL→perm be))
           s12 : abc ≡ perm→FL [ dba , aec ]  
           s12 = refl
           s11 : FL→perm abc =p= [ dba , aec ]  
           s11 = ptrans (pcong-Fp s12 ) (FL←iso _)    -- this takes a long time
           s17 : deriving  (suc i) ( FL→perm abc )
           s17 = ccong _ (psym s11) (comm (Pcomm {_} {FL→perm dc} i (deriving-inv s10)) (Pcomm {_} {FL→perm be} i s10) prefl )


     -- open Solvable ( Symmetric 5) 
     end5 : (x : Permutation 5 5) → deriving  (dervied-length sol) x →  x =p= pid  
     end5 x der = end sol x der

     counter-example : ¬ ( FL→perm abc  =p= pid )
     counter-example eq with ←pleq _ _ eq
     ... | ()

