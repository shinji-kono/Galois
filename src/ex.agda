{-# OPTIONS --cubical-compatible --safe #-}

-- fundamental homomorphism theorem
--

module ex where

open import Level hiding ( suc ; zero )
open import Algebra
open import Algebra.Structures
open import Algebra.Definitions
open import Algebra.Core
open import Algebra.Bundles

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import NormalSubgroup
import Gutil
import Function.Definitions as FunctionDefinitions

import Algebra.Morphism.Definitions as MorphismDefinitions
open import Algebra.Morphism.Structures

open import Tactic.MonoidSolver using (solve; solve-macro)

--
-- Given two groups G and H and a group homomorphism f : G → H,
-- let K be a normal subgroup in G and φ the natural surjective homomorphism G → G/K
-- (where G/K is the quotient group of G by K).
-- If K is a subset of ker(f) then there exists a unique homomorphism h: G/K → H such that f = h∘φ.
--     https://en.wikipedia.org/wiki/Fundamental_theorem_on_homomorphisms
--
--       f
--    G --→ H
--    |   /
--  φ |  / h
--    ↓ /
--    G/K
--

import Relation.Binary.Reasoning.Setoid as EqReasoning

open GroupMorphisms

-- import Axiom.Extensionality.Propositional
-- postulate f-extensionality : { n m : Level}  → Axiom.Extensionality.Propositional.Extensionality n m

open import Data.Empty
open import Relation.Nullary
open import NormalSubgroup

open import Data.Nat
open import Data.Fin hiding (_+_ ; _-_ )
open import Data.Unit
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import nat
open import logic
open import Relation.Binary.Definitions

open _∧_

Mod : (n : ℕ) → Group Level.zero Level.zero
Mod n = record {
      Carrier        = ℕ
    ; _≈_            = _==_
    ; _∙_            = _+_
    ; ε              = 0
    ; _⁻¹            = ?
    ; isGroup = record { isMonoid  = record { isSemigroup = record { isMagma = record {
       isEquivalence = record {refl = ? ; trans = ? ; sym = ? }
       ; ∙-cong = ? }
       ; assoc = ? }
       ; identity = ( (λ q → ? ) , (λ q → ?))  }
       ; inverse   = ( (λ x → ? ) , (λ x → ? ))  
       ; ⁻¹-cong   = λ i=j → ?
      }
   } where
       _==_ : (x y : ℕ) → Set
       x == y = x mod (suc n) ≡ y mod (suc n)
       =f : {x y : ℕ} → x == y → Factor (suc n) x ∧  Factor (suc n) y
       =f {x} {y} x=y = ⟪ record { factor = ? ; remain = ? ; is-factor = ? }  ,  record { factor = ? ; remain = ?; is-factor = ?  } ⟫
       f=f : {x y : ℕ} → (x=y : x == y ) → Factor.remain (proj1 (=f {x} {y} x=y)) ≡ Factor.remain (proj2 (=f {x} {y} x=y))
       f=f = ?
       inv : ℕ → ℕ 
       inv x = suc n - (toℕ (x mod (suc n)))
       mod00 : {x y u v : ℕ } → x == y → u == v → (x + u) == (y + v)
       mod00 = ?
       mod01 : (x y z : ℕ ) → ((x + y) + z) == (x + (y + z))
       mod01 zero y z = ?
       mod01 (suc x) y z = ? 

