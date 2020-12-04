open import Level hiding ( suc ; zero )
open import Algebra
module sym2 where

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
   -- open Group (Symmetric 2) using (_⁻¹)


   p0 :  FL→perm ((# 0) :: ((# 0 ) :: f0)) =p= pid
   p0 = pleq _ _ refl

   p0r :  perm→FL pid ≡  ((# 0) :: ((# 0 ) :: f0)) 
   p0r = refl

   p1 :  FL→perm ((# 1) :: ((# 0 ) :: f0)) =p= pswap pid
   p1 = pleq _ _ refl

   p1r :  perm→FL (pswap pid) ≡  ((# 1) :: ((# 0 ) :: f0)) 
   p1r = refl

   -- FL→iso : (fl : FL 2 )  → perm→FL ( FL→perm fl ) ≡ fl
   -- FL→iso  (zero :: (zero :: f0)) = refl
   -- FL→iso ((suc zero) :: (zero :: f0)) = refl

   open _=p=_
   open ≡-Reasoning

   sym2lem0 :  ( g h : Permutation 2 2 ) → (q : Fin 2)  → ([ g , h ]  ⟨$⟩ʳ q) ≡ (pid ⟨$⟩ʳ q)
   sym2lem0 g h q with perm→FL g | perm→FL h | inspect perm→FL g | inspect perm→FL h
   sym2lem0 g h q | zero :: (zero :: f0) | _ | record { eq = g=00} | record { eq = h=00}  = begin
             [ g , h ]  ⟨$⟩ʳ q
           ≡⟨⟩
              h ⟨$⟩ʳ  (g ⟨$⟩ʳ ( h ⟨$⟩ˡ ( g ⟨$⟩ˡ q ))) 
           ≡⟨ cong (λ k → h ⟨$⟩ʳ  (g ⟨$⟩ʳ ( h ⟨$⟩ˡ  k))) ((peqˡ sym2lem1 _ )) ⟩
              h ⟨$⟩ʳ  (g ⟨$⟩ʳ ( h ⟨$⟩ˡ ( pid ⟨$⟩ˡ q ))) 
           ≡⟨ cong (λ k →  h ⟨$⟩ʳ k ) (peq sym2lem1 _ )  ⟩
              h ⟨$⟩ʳ  (pid ⟨$⟩ʳ ( h ⟨$⟩ˡ ( pid ⟨$⟩ˡ q ))) 
           ≡⟨⟩
             [ pid , h ]  ⟨$⟩ʳ q
           ≡⟨ peq (idcomtl h) q ⟩
             q
           ∎ where
             sym2lem1 :  g =p= pid
             sym2lem1 = FL-inject  g=00
   sym2lem0 g h q | _ | zero :: (zero :: f0) | record { eq = g=00} | record { eq = h=00} = begin
             [ g , h ]  ⟨$⟩ʳ q
           ≡⟨⟩
              h ⟨$⟩ʳ  (g ⟨$⟩ʳ ( h ⟨$⟩ˡ ( g ⟨$⟩ˡ q ))) 
           ≡⟨ peq sym2lem2 _   ⟩
              pid ⟨$⟩ʳ  (g ⟨$⟩ʳ ( h ⟨$⟩ˡ ( g ⟨$⟩ˡ q ))) 
           ≡⟨ cong (λ k → pid ⟨$⟩ʳ  (g ⟨$⟩ʳ k)) (peqˡ sym2lem2 _ ) ⟩
              pid ⟨$⟩ʳ  (g ⟨$⟩ʳ ( pid ⟨$⟩ˡ ( g ⟨$⟩ˡ q ))) 
           ≡⟨⟩
             [ g , pid ]  ⟨$⟩ʳ q
           ≡⟨ peq (idcomtr g) q ⟩
             q
          ∎ where
             sym2lem2 :  h =p= pid
             sym2lem2 = FL-inject h=00
   sym2lem0 g h q | suc zero :: (zero :: f0) | suc zero :: (zero :: f0) | record { eq = g=00} | record { eq = h=00}= begin
             [ g , h ]  ⟨$⟩ʳ q
           ≡⟨⟩
              h ⟨$⟩ʳ  (g ⟨$⟩ʳ ( h ⟨$⟩ˡ ( g ⟨$⟩ˡ q ))) 
           ≡⟨ peq (psym g=h ) _  ⟩
              g ⟨$⟩ʳ  (g ⟨$⟩ʳ ( h ⟨$⟩ˡ ( g ⟨$⟩ˡ q ))) 
           ≡⟨ cong (λ k →   g ⟨$⟩ʳ  (g ⟨$⟩ʳ  k) ) (peqˡ (psym g=h) _)  ⟩
              g ⟨$⟩ʳ  (g ⟨$⟩ʳ ( g ⟨$⟩ˡ ( g ⟨$⟩ˡ q ))) 
           ≡⟨ cong (λ k → g  ⟨$⟩ʳ k) ( inverseʳ g )  ⟩
              g ⟨$⟩ʳ  ( g ⟨$⟩ˡ q ) 
           ≡⟨ inverseʳ g   ⟩
             q
          ∎ where
              g=h :  g =p= h
              g=h =  FL-inject (trans g=00 (sym h=00))
   solved :  (x : Permutation 2 2) → Commutator  (λ x₁ → Lift (Level.suc Level.zero) ⊤) x → x =p= pid
   solved x uni = prefl
   solved x (comm {g} {h} _ _) = record { peq = sym2lem0 g h  } 
   solved x (gen {f} {g} d d₁) with solved f d | solved g d₁
   ... | record { peq = f=e } | record { peq = g=e } = record { peq = λ q → genlem q } where
      genlem : ( q : Fin 2 ) → g ⟨$⟩ʳ ( f ⟨$⟩ʳ q ) ≡ q
      genlem q = begin
             g ⟨$⟩ʳ ( f ⟨$⟩ʳ q )
          ≡⟨ g=e ( f ⟨$⟩ʳ q ) ⟩
             f ⟨$⟩ʳ q 
          ≡⟨ f=e q ⟩
             q
          ∎ where open ≡-Reasoning
   solved x (ccong {f} {g} (record {peq = f=g}) d) with solved f d
   ... | record { peq = f=e }  =  record  { peq = λ q → cc q } where
      cc : ( q : Fin 2 ) → x ⟨$⟩ʳ q ≡ q
      cc q = begin
             x ⟨$⟩ʳ q
          ≡⟨ sym (f=g q) ⟩
             f ⟨$⟩ʳ q
          ≡⟨ f=e q ⟩
             q
          ∎ where open ≡-Reasoning




