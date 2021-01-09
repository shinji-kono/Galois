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
open import Data.Unit hiding (_≤_)
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

open import Algebra 
open Group (Symmetric n) hiding (refl)
open Solvable (Symmetric n) 
open _∧_
-- open import Relation.Nary using (⌊_⌋)
open import Relation.Nullary.Decidable hiding (⌊_⌋)

open import fin

-- all cobmbination in P and Q (could be more general)
record AnyComm {n m l : ℕ}  (P : FList n) (Q : FList m) (fpq : (p : FL n) (q : FL m) → FL l) : Set where
   field
     commList : FList l
     commAny : (p : FL n) (q : FL m)
         → Any ( p ≡_ ) P →  Any ( q ≡_ ) Q
         → Any (fpq p q ≡_) commList

-------------
--    (p,q)   (p,qn) ....           (p,q0)
--    pn,q       
--     :        AnyComm FL0 FL0 P  Q
--    p0,q       

open AnyComm 
anyComm : {n m l : ℕ } → (P : FList n) (Q : FList m) → (fpq : (p : FL n) (q : FL m) → FL l)  → AnyComm P Q fpq
anyComm [] [] _ = record { commList = [] ; commAny = λ _ _ () }
anyComm [] (cons q Q qr) _ = record { commList = [] ; commAny = λ _ _ () }
anyComm (cons p P pr) [] _ = record { commList = [] ; commAny = λ _ _ _ () }
anyComm {n} {m} {l} (cons p P pr) (cons q Q qr) fpq = record { commList = FLinsert (fpq p q) (commListQ Q)  ; commAny = anyc0n } where 
  commListP : (P1 : FList n) → FList l
  commListP [] = commList (anyComm P Q fpq)
  commListP (cons p₁ P1 x) =  FLinsert (fpq p₁ q) (commListP P1)
  commListQ : (Q1 : FList m) → FList l
  commListQ [] = commListP P
  commListQ (cons q₁ Q1 qr₁) = FLinsert (fpq p q₁) (commListQ Q1)
  anyc0n : (p₁ : FL n) (q₁ : FL m) → Any (_≡_ p₁) (cons p P pr) → Any (_≡_ q₁) (cons q Q qr)
    → Any (_≡_ (fpq p₁ q₁)) (FLinsert (fpq p q) (commListQ Q))
  anyc0n p₁ q₁ (here refl) (here refl) = x∈FLins _ (commListQ Q )
  anyc0n p₁ q₁ (here refl) (there anyq) = insAny (commListQ Q) (anyc01 Q anyq) where 
     anyc01 : (Q1 : FList m) → Any (_≡_ q₁) Q1 → Any (_≡_ (fpq p₁ q₁)) (commListQ Q1)
     anyc01 (cons q Q1 qr₂) (here refl) = x∈FLins _ _
     anyc01 (cons q₂ Q1 qr₂) (there any) = insAny _ (anyc01 Q1 any)
  anyc0n p₁ q₁ (there anyp) (here refl) = insAny _ (anyc02 Q) where
     anyc03 : (P1 : FList n) → Any (_≡_ p₁) P1  → Any (_≡_ (fpq p₁ q₁)) (commListP P1)
     anyc03 (cons a P1 x) (here refl) = x∈FLins _ _ 
     anyc03 (cons a P1 x) (there any) = insAny _ ( anyc03 P1 any) 
     anyc02 : (Q1 : FList m) → Any (_≡_ (fpq p₁ q₁)) (commListQ Q1)
     anyc02 [] = anyc03 P anyp
     anyc02 (cons a Q1 x) = insAny _ (anyc02 Q1)
  anyc0n p₁ q₁ (there anyp) (there anyq) = insAny (commListQ Q) (anyc04 Q) where
     anyc05 : (P1 : FList n) → Any (_≡_ (fpq p₁ q₁)) (commListP P1)
     anyc05 [] = commAny (anyComm P Q fpq) p₁ q₁ anyp anyq
     anyc05 (cons a P1 x) = insAny _ (anyc05 P1)
     anyc04 : (Q1 : FList m) → Any (_≡_ (fpq p₁ q₁)) (commListQ Q1)
     anyc04 [] = anyc05 P 
     anyc04 (cons a Q1 x) = insAny _ (anyc04 Q1)

-------------
--    # 0 :: # 0 :: # 0 : # 0 :: f0
--    # 0 :: # 0 :: # 1 : # 0 :: f0
--    # 0 :: # 1 :: # 0 : # 0 :: f0
--    # 0 :: # 1 :: # 1 : # 0 :: f0
--    # 0 :: # 2 :: # 0 : # 0 :: f0
--       ...
--    # 3 :: # 2 :: # 0 : # 0 :: f0
--    # 3 :: # 2 :: # 1 : # 0 :: f0

-- all FL
record AnyFL (n : ℕ) : Set where
   field
     allFL : FList n
     anyP : (x : FL n) → Any (x ≡_ ) allFL 

open AnyFL

--   all FL as all combination  
--      anyComm ( #0 :: FL0 ... # n :: FL0 ) (all n) (λ p q → FLpos p :: q ) = all (suc n)

anyFL01 :  (n : ℕ) → AnyFL (suc n) 
anyFL01 zero    = record { allFL = (zero :: f0) ∷# [] ; anyP = λ x → anyFL2 x ((zero :: f0) ∷# []) refl }  where
     anyFL2 : (x : FL 1) → (y : FList 1) → y ≡ ((zero :: f0) ∷# []) → Any (_≡_ x) y
     anyFL2 (zero :: f0) .(cons (zero :: f0) [] (Level.lift tt)) refl = here refl
anyFL01 (suc n) = record { allFL = commList anyC ;  anyP =  anyFL02 } where
     anyFL05 : {n i : ℕ} → (i < suc n) → FList (suc n)
     anyFL05 {_} {0} (s≤s z≤n) = zero :: FL0 ∷# []
     anyFL05 {n} {suc i} (s≤s i<n) = FLinsert (fromℕ< (s≤s i<n) :: FL0) (anyFL05 {n} {i} (<-trans i<n a<sa))
     anyFL08 : {n i : ℕ} {x : Fin (suc n)} {i<n : suc i < suc n}  → toℕ x ≡ suc i → x ≡ suc (fromℕ< (≤-pred i<n))
     anyFL08 {n} {i} {x} {i<n} eq = toℕ-injective ( begin
                toℕ x                               ≡⟨ eq ⟩
                suc i                               ≡⟨ cong suc (≡-sym (toℕ-fromℕ< _ )) ⟩
                suc (toℕ (fromℕ< (≤-pred i<n)) )
          ∎ ) where open ≡-Reasoning
     anyFL06 : {n i : ℕ} → (i<n : i < suc n) → (x : Fin (suc n)) → toℕ x < suc i → Any (_≡_ (x :: FL0)) (anyFL05 i<n)
     anyFL06 (s≤s z≤n) zero (s≤s lt) = here refl
     anyFL06 {n} {suc i} (s≤s (s≤s i<n)) x (s≤s lt) with <-cmp (toℕ x) (suc i)
     ... | tri< a ¬b ¬c = insAny _ (anyFL06 (<-trans (s≤s i<n) a<sa) x a) 
     ... | tri≈ ¬a b ¬c = subst (λ k →  Any (_≡_ (x :: FL0)) (FLinsert (k :: FL0) (anyFL05 {n} {i} (<-trans (s≤s i<n) a<sa))))
                  (anyFL08 {n} {i} {x} {s≤s (s≤s i<n)} b) (x∈FLins (x :: FL0)  (anyFL05 {n} {i} (<-trans (s≤s i<n) a<sa)))
     ... | tri> ¬a ¬b c = ⊥-elim ( nat-≤> c (s≤s lt) )
     anyC = anyComm (anyFL05 a<sa) (allFL (anyFL01 n)) (λ p q → FLpos p :: q )
     anyFL02 : (x : FL (suc (suc n))) → Any (_≡_ x) (commList anyC)
     anyFL02 (x :: y) = commAny anyC (x :: FL0) y
                       (subst (λ k → Any (_≡_ (k :: FL0) ) _) (fromℕ<-toℕ _ _) (anyFL06 a<sa (fromℕ< x≤n) fin<n) ) (anyP (anyFL01 n) y) where
         x≤n : suc (toℕ x)  ≤ suc (suc n)
         x≤n = toℕ<n x

anyFL :  (n : ℕ) → AnyFL n 
anyFL zero = record { allFL = f0 ∷# [] ; anyP = anyFL4 } where
    anyFL4 : (x : FL zero) → Any (_≡_ x) ( f0 ∷# [] )
    anyFL4 f0 = here refl
anyFL (suc n) = anyFL01 n

at1 = proj₁ (toList (allFL (anyFL 1)))
at2 = proj₁ (toList (allFL (anyFL 2)))
at3 = proj₁ (toList (allFL (anyFL 3)))
at4 = proj₁ (toList (allFL (anyFL 4)))

CommFListN  : ℕ →  FList n
CommFListN  zero = allFL (anyFL n)
CommFListN (suc i ) = commList (anyComm ( CommFListN i ) ( CommFListN i ) (λ p q →  perm→FL [ FL→perm p , FL→perm q ] ))

CommStage→ : (i : ℕ) → (x : Permutation n n ) → deriving i x → Any (perm→FL x ≡_) (CommFListN i)
CommStage→ zero x (Level.lift tt) = anyP (anyFL n) (perm→FL x)
CommStage→ (suc i) .( [ g , h ] ) (comm {g} {h} p q) = comm2 where
  G = perm→FL g
  H = perm→FL h
  comm3 :  perm→FL [ FL→perm G , FL→perm H ] ≡ perm→FL [ g , h ]
  comm3 = begin
              perm→FL [ FL→perm G , FL→perm H ] 
           ≡⟨ pcong-pF (comm-resp (FL←iso _) (FL←iso _)) ⟩
              perm→FL [ g , h ]
          ∎  where open ≡-Reasoning
  comm2 : Any (_≡_ (perm→FL [ g , h ])) (CommFListN (suc i))
  comm2 = subst (λ k → Any (_≡_ k) (CommFListN (suc i)) ) comm3
     ( commAny ( anyComm (CommFListN i) (CommFListN i) (λ p q →  perm→FL [ FL→perm p , FL→perm q ] )) G H (CommStage→ i g p) (CommStage→ i h q) )
CommStage→ (suc i) x (ccong {f} {x} eq p) =
      subst (λ k → Any (k ≡_) (commList (anyComm ( CommFListN i ) ( CommFListN i ) (λ p q →  perm→FL [ FL→perm p , FL→perm q ] ))))
          (comm4 eq) (CommStage→ (suc i) f p ) where
   comm4 : f =p= x →  perm→FL f ≡ perm→FL x
   comm4 = pcong-pF

CommSolved : (x : Permutation n n) → (y : FList n) → y ≡ FL0 ∷# [] → (FL→perm (FL0 {n}) =p= pid ) → Any (perm→FL x ≡_) y → x =p= pid
CommSolved x .(cons FL0 [] (Level.lift tt)) refl eq0 (here eq) = FLpid _ eq eq0
