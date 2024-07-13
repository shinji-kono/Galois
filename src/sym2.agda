{-# OPTIONS --cubical-compatible --safe #-}

open import Level hiding ( suc ; zero )
open import Algebra
module sym2 where

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
open import Data.Fin.Permutation

sym2solvable : solvable (Symmetric 2)
solvable.dervied-length sym2solvable = 1
solvable.end sym2solvable x d = solved x d where

   open import Data.List using ( List ; [] ; _∷_ )

   open Solvable (Symmetric 2)

   p0 :  FL→perm ((# 0) :: ((# 0 ) :: f0)) =p= pid
   p0 = pleq _ _ refl

   p0r :  perm→FL pid ≡  ((# 0) :: ((# 0 ) :: f0)) 
   p0r = refl

   p1 :  FL→perm ((# 1) :: ((# 0 ) :: f0)) =p= pswap pid
   p1 = pleq _ _ refl

   p1r :  perm→FL (pswap pid) ≡  ((# 1) :: ((# 0 ) :: f0)) 
   p1r = refl

   open _=p=_
   open ≡-Reasoning

   -- we cannot use sym2lem0 g h q with perm→FL g in g=00 | perm→FL h in h=00 
   --   because of Panic: uncaught pattern violation 

   sym2lem0 :  ( g h : Permutation 2 2 ) → (q : Fin 2)  → ([ g , h ]  ⟨$⟩ʳ q) ≡ (pid ⟨$⟩ʳ q)
   sym2lem0 g h q = s00 (perm→FL g) ( perm→FL h) refl refl  where
       s00 : (pg : FL 2) (ph : FL 2 ) → pg ≡ perm→FL g → ph ≡ perm→FL h → [ g , h ]  ⟨$⟩ʳ q ≡ (pid ⟨$⟩ʳ q)
       s00 (zero :: zero :: f0) _ ge he = begin
            [ g , h ]  ⟨$⟩ʳ q ≡⟨⟩
             h ⟨$⟩ʳ  (g ⟨$⟩ʳ ( h ⟨$⟩ˡ ( g ⟨$⟩ˡ q ))) 
                 ≡⟨ cong (λ k → h ⟨$⟩ʳ  (g ⟨$⟩ʳ ( h ⟨$⟩ˡ  k))) ((peqˡ {2} {g} {pid} (FL-inject (sym ge)) _ )) ⟩
             h ⟨$⟩ʳ  (g ⟨$⟩ʳ ( h ⟨$⟩ˡ ( pid ⟨$⟩ˡ q ))) ≡⟨ cong (λ k →  h ⟨$⟩ʳ k ) (peq {2} {g} {pid} (FL-inject (sym ge)) _ )  ⟩
             h ⟨$⟩ʳ  (pid ⟨$⟩ʳ ( h ⟨$⟩ˡ ( pid ⟨$⟩ˡ q ))) ≡⟨⟩
            [ pid , h ]  ⟨$⟩ʳ q ≡⟨ peq (idcomtl h) q ⟩
            q ∎ 
       s00 (suc zero :: zero :: f0) (zero :: zero :: f0) ge he = begin
            [ g , h ]  ⟨$⟩ʳ q ≡⟨⟩
             h ⟨$⟩ʳ  (g ⟨$⟩ʳ ( h ⟨$⟩ˡ ( g ⟨$⟩ˡ q ))) ≡⟨ peq sym2lem2 _   ⟩
             pid ⟨$⟩ʳ  (g ⟨$⟩ʳ ( h ⟨$⟩ˡ ( g ⟨$⟩ˡ q ))) ≡⟨ cong (λ k → pid ⟨$⟩ʳ  (g ⟨$⟩ʳ k)) (peqˡ sym2lem2 _ ) ⟩
             pid ⟨$⟩ʳ  (g ⟨$⟩ʳ ( pid ⟨$⟩ˡ ( g ⟨$⟩ˡ q ))) ≡⟨⟩
            [ g , pid ]  ⟨$⟩ʳ q ≡⟨ peq (idcomtr g) q ⟩
            q ∎ where
                sym2lem2 :  h =p= pid
                sym2lem2 = FL-inject (sym he)
       s00 (suc zero :: zero :: f0) (suc zero :: zero :: f0) ge he = begin
            [ g , h ]  ⟨$⟩ʳ q ≡⟨⟩
             h ⟨$⟩ʳ  (g ⟨$⟩ʳ ( h ⟨$⟩ˡ ( g ⟨$⟩ˡ q ))) ≡⟨ peq (psym g=h ) _  ⟩
             g ⟨$⟩ʳ  (g ⟨$⟩ʳ ( h ⟨$⟩ˡ ( g ⟨$⟩ˡ q ))) ≡⟨ cong (λ k →   g ⟨$⟩ʳ  (g ⟨$⟩ʳ  k) ) (peqˡ (psym g=h) _)  ⟩
             g ⟨$⟩ʳ  (g ⟨$⟩ʳ ( g ⟨$⟩ˡ ( g ⟨$⟩ˡ q ))) ≡⟨ cong (λ k → g  ⟨$⟩ʳ k) ( inverseʳ g )  ⟩
             g ⟨$⟩ʳ  ( g ⟨$⟩ˡ q ) ≡⟨ inverseʳ g   ⟩
            q ∎ where
             g=h :  g =p= h
             g=h =  FL-inject (trans (sym ge) he)

   solved :  (x : Permutation 2 2) → Commutator  (λ x₁ → Lift (Level.suc Level.zero) ⊤) x → x =p= pid
   solved x (comm {f} {g} _ _ eq ) = record { peq = cc }  where
      cc : (q : Fin 2) → x ⟨$⟩ʳ q ≡ pid ⟨$⟩ʳ q 
      cc q = begin
             x ⟨$⟩ʳ q ≡⟨ peq eq q ⟩
             [ f , g ] ⟨$⟩ʳ q ≡⟨ sym2lem0 f g q ⟩
             q ∎ where open ≡-Reasoning

