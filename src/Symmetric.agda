{-# OPTIONS --cubical-compatible --safe #-}

module Symmetric where

open import Level hiding ( suc ; zero )
open import Algebra
open import Algebra.Structures
open import Data.Fin hiding ( _<_  ; _≤_ ; _-_ ; _+_ )
open import Data.Fin.Properties hiding ( <-trans ; ≤-trans ) renaming ( <-cmp to <-fcmp )
open import Data.Product
open import Data.Fin.Permutation
open import Function hiding (id ; flip)
open import Function.Inverse as Inverse using (_↔_; Inverse; _InverseOf_)
open import Function.LeftInverse  using ( _LeftInverseOf_ )
open import Function.Equality using (Π)
open import Data.Nat -- using (ℕ; suc; zero; s≤s ; z≤n )
open import Data.Nat.Properties -- using (<-trans)
open import Relation.Binary.PropositionalEquality 
open import Data.List using (List; []; _∷_ ; length ; _++_ ; head ) renaming (reverse to rev )
open import nat

fid : {p : ℕ } → Fin p → Fin p
fid x = x

-- Data.Fin.Permutation.id
pid : {p : ℕ } → Permutation p p
pid = permutation fid fid (λ x → refl) (λ x → refl) -- record { left-inverse-of = λ x → refl ; right-inverse-of = λ x → refl } 

-- Data.Fin.Permutation.flip
pinv : {p : ℕ } → Permutation p p → Permutation p p
pinv {p} P = permutation (_⟨$⟩ˡ_ P) (_⟨$⟩ʳ_ P ) (λ x → inverseˡ P ) ( λ x → inverseʳ P) -- record { left-inverse-of = λ x → inverseʳ P ; right-inverse-of = λ x → inverseˡ P }

record _=p=_ {p : ℕ } ( x y : Permutation p p )  : Set where
    field
       peq : ( q : Fin p ) → x ⟨$⟩ʳ q ≡ y ⟨$⟩ʳ q

open _=p=_

prefl : {p : ℕ } { x  : Permutation p p } → x =p= x
peq (prefl {p} {x}) q = refl

psym : {p : ℕ } { x y : Permutation p p } → x =p= y →  y =p= x
peq (psym {p} {x} {y}  eq ) q = sym (peq eq q)

ptrans : {p : ℕ } { x y z : Permutation p p } → x =p= y  → y =p= z →  x =p= z
peq (ptrans {p} {x} {y} x=y y=z ) q = trans (peq x=y q) (peq y=z q)

peqˡ :  {p : ℕ }{ x y : Permutation p p } → x =p= y → (q : Fin p)  →  x ⟨$⟩ˡ q ≡ y ⟨$⟩ˡ q
peqˡ {p} {x} {y} eq q = begin
       x ⟨$⟩ˡ q
   ≡⟨ sym ( inverseˡ y ) ⟩
       y ⟨$⟩ˡ (y ⟨$⟩ʳ ( x ⟨$⟩ˡ  q ))
   ≡⟨ cong (λ k → y ⟨$⟩ˡ k ) (sym (peq eq _ )) ⟩
       y ⟨$⟩ˡ (x ⟨$⟩ʳ ( x ⟨$⟩ˡ  q ))
   ≡⟨ cong (λ k → y ⟨$⟩ˡ k ) ( inverseʳ x ) ⟩
       y ⟨$⟩ˡ q
   ∎ where open ≡-Reasoning

presp : { p : ℕ } {x y u v : Permutation p p } → x =p= y → u =p= v → (x ∘ₚ u) =p= (y ∘ₚ v)
presp {p} {x} {y} {u} {v} x=y u=v = record { peq = λ q → lemma4 q } where
   lemma4 : (q : Fin p) → ((x ∘ₚ u) ⟨$⟩ʳ q) ≡ ((y ∘ₚ v) ⟨$⟩ʳ q)
   lemma4 q = begin
          ((x ∘ₚ u) ⟨$⟩ʳ q) ≡⟨ peq u=v _ ⟩
          ((x ∘ₚ v) ⟨$⟩ʳ q) ≡⟨ cong (λ k → Inverse.to v k  ) (peq x=y _) ⟩
          ((y ∘ₚ v) ⟨$⟩ʳ q) ∎  
     where 
       open ≡-Reasoning
   -- lemma4 q = trans (cong (λ k → Inverse.to u Π.⟨$⟩ k) (peq x=y q) ) (peq u=v _ )
passoc : { p : ℕ } (x y z : Permutation p p) → ((x ∘ₚ y) ∘ₚ z) =p=  (x ∘ₚ (y ∘ₚ z))
passoc x y z = record { peq = λ q → refl }
p-inv : { p : ℕ } {i j : Permutation p p} →  i =p= j → (q : Fin p) → pinv i ⟨$⟩ʳ q ≡ pinv j ⟨$⟩ʳ q
p-inv {p} {i} {j} i=j q = begin
   i ⟨$⟩ˡ q                      ≡⟨ cong (λ k → i ⟨$⟩ˡ k) (sym (inverseʳ j)  )  ⟩
   i ⟨$⟩ˡ ( j ⟨$⟩ʳ ( j ⟨$⟩ˡ q )) ≡⟨ cong (λ k  →  i ⟨$⟩ˡ k) (sym (peq i=j _ ))  ⟩
   i ⟨$⟩ˡ ( i ⟨$⟩ʳ ( j ⟨$⟩ˡ q )) ≡⟨ inverseˡ i  ⟩
   j ⟨$⟩ˡ q
   ∎ where open ≡-Reasoning

Symmetric : ℕ → Group  Level.zero Level.zero
Symmetric p = record {
      Carrier        = Permutation p p
    ; _≈_            = _=p=_
    ; _∙_            = _∘ₚ_
    ; ε              = pid
    ; _⁻¹            = pinv
    ; isGroup = record { isMonoid  = record { isSemigroup = record { isMagma = record {
       isEquivalence = record {refl = prefl ; trans = ptrans ; sym = psym }
       ; ∙-cong = presp }
       ; assoc = passoc }
       ; identity = ( (λ q → record { peq = λ q → refl } ) , (λ q → record { peq = λ q → refl } ))  }
       ; inverse   = ( (λ x → record { peq = λ q → inverseʳ x} ) , (λ x → record { peq = λ q → inverseˡ x} ))  
       ; ⁻¹-cong   = λ i=j → record { peq = λ q → p-inv i=j q }
      }
   } 

