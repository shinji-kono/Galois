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

-------------
--    # 0 :: # 0 :: # 0 : # 0 :: f0
--    # 0 :: # 0 :: # 1 : # 0 :: f0
--    # 0 :: # 1 :: # 0 : # 0 :: f0
--    # 0 :: # 1 :: # 1 : # 0 :: f0
--    # 0 :: # 2 :: # 0 : # 0 :: f0
--       ...

-- all FL
record AnyFL (n : ℕ) (y : FL n) : Set where
   field
     allFL : FList n
     anyP : (x : FL n) → Any (x ≡_ ) allFL 

open import fin
open AnyFL

anyFL0 :  (n : ℕ) → AnyFL (suc n) fmax
anyFL0 zero = record { allFL = (zero :: f0) ∷# [] ; anyP = anyFL2 } where 
    anyFL2 : (x : FL 1) → Any (_≡_ x) (cons (zero :: f0) [] (Level.lift tt))
    anyFL2 (zero :: f0) = here refl
anyFL0 (suc n)  = record { allFL = allListF a<sa []; anyP = λ x → anyFL3 a<sa x (fin≤n (FLpos x)) [] } where 
    allListFL : (x : Fin (suc (suc n))) → FList (suc n) → FList (suc (suc n)) → FList (suc (suc n))
    allListFL _ [] y = y
    allListFL x (cons y L yr) z = FLinsert (x :: y) (allListFL x L z) 
    allListF : {i : ℕ} → (i<n : i < suc (suc n)) → FList (suc (suc n)) → FList (suc (suc n))
    allListF (s≤s z≤n) z = allListFL zero (allFL (anyFL0 n)) z
    allListF (s≤s (s≤s i<n)) z = allListFL (suc (fromℕ< (s≤s i<n ))) (allFL (anyFL0 n)) (allListF (<-trans (s≤s i<n) a<sa) z)
    anyFL3 :  {i : ℕ} → (i<n : i < suc (suc n)) (x : FL (suc (suc n))) → (toℕ (FLpos x ) ≤ i) → (z : FList (suc (suc n))) → Any (_≡_ x) (allListF i<n z)
    anyFL3 {zero} (s≤s z≤n) (x :: y) x<i z = anyFL6 (allFL (anyFL0 n)) (anyP (anyFL0 n) y) (anyFL5 x<i) where
        anyFL5 : toℕ x ≤ zero → x ≡ zero
        anyFL5 lt with <-fcmp x zero
        ... | tri≈ ¬a b ¬c = b
        ... | tri> ¬a ¬b c = ⊥-elim (nat-≤> x<i c)
        anyFL6 : (L : FList (suc n)) → Any (_≡_ y) L → x ≡ zero → Any (_≡_ (x :: y)) (allListFL zero L z)
        anyFL6 (cons _ xs _) (here refl) refl = x∈FLins (x :: y)  (allListFL zero xs z)
        anyFL6 (cons _ xs  _) (there any) refl = insAny _ (anyFL6 xs any refl )
    anyFL3 {suc i} (s≤s (s≤s i<n)) (x :: y) x<i z with <-cmp (toℕ x) (suc i)
    ... | tri< a ¬b ¬c = anyFL1 (s≤s i<n) a where
        anyFL1  : {i : ℕ} → (i<n : i < suc n) → (x<i : suc (toℕ x) ≤ suc i )  →  Any (_≡_ (x :: y)) (allListF (s≤s i<n) z)
        anyFL10 : {i : ℕ} → (i<n : i < suc n ) → (x<i : suc (toℕ x) ≤ suc i) → (L : FList (suc n))  
            → Any (_≡_ (x :: y))  (allListFL (suc (fromℕ< i<n)) L (allListF (<-trans i<n a<sa) z) )
        anyFL10 {i} (s≤s j<n) (s≤s x<i) [] = anyFL3 (<-trans (s≤s j<n) a<sa) (x :: y) x<i z  
        anyFL10 {i} i<n x<i (cons _ xs _)  = insAny _ (anyFL10 {i} i<n x<i xs )
        anyFL1 {i} (s≤s i<n) x<i = anyFL10 (s≤s i<n ) x<i (allFL (anyFL0 n)) 
    ... | tri≈ ¬a b ¬c = anyFL7 (allFL (anyFL0 n)) (anyP (anyFL0 n) y) where
        anyFL9 : toℕ x ≡ suc i → x ≡ suc (fromℕ< (s≤s i<n))
        anyFL9 x=si = toℕ-injective ( begin
             toℕ x ≡⟨ x=si ⟩
             suc i  ≡⟨ cong suc (≡-sym (toℕ-fromℕ< _) ) ⟩
             suc (toℕ (fromℕ< (s≤s i<n)))  ≡⟨⟩
             toℕ (suc (fromℕ< (s≤s i<n)))
          ∎ ) where open ≡-Reasoning
        anyFL8 : (L : FList (suc n)) → Any (_≡_ y) L → Any (_≡_ (x :: y)) (allListFL x L (allListF (<-trans (s≤s i<n) a<sa) z))
        anyFL8 (cons _ xs _) (here refl) = x∈FLins (x :: y) (allListFL x xs (allListF (<-trans (s≤s i<n) a<sa) z))
        anyFL8 (cons _ xs _) (there any) = insAny _ (anyFL8 xs any)
        anyFL7 : (L : FList (suc n)) → Any (_≡_ y) L → Any (_≡_ (x :: y)) (allListF (s≤s (s≤s i<n)) z)
        anyFL7 (cons _ xs _) (there any) = anyFL7 xs any
        anyFL7 (cons _ xs _) (here refl) = subst (λ k →  Any (_≡_ (x :: y))
            (allListFL k (allFL (anyFL0 n)) (allListF (<-trans (s≤s i<n) a<sa) z)) ) (anyFL9 b) (anyFL8 (allFL (anyFL0 n)) (anyP (anyFL0 n) y) )
    ... | tri> ¬a ¬b c = ⊥-elim (nat-≤> x<i c)

anyFL :  (n : ℕ) → AnyFL n fmax
anyFL zero = record { allFL = f0 ∷# [] ; anyP = anyFL4 } where
    anyFL4 : (x : FL zero) → Any (_≡_ x) ( f0 ∷# [] )
    anyFL4 f0 = here refl
anyFL (suc n) = anyFL0 n

at1 = toList (allFL (anyFL 1))
at2 = toList (allFL (anyFL 2))
at3 = toList (allFL (anyFL 3))
at4 = toList (allFL (anyFL 4))

-- all cobmbination in P and Q
record AnyComm {n : ℕ}  (P Q : FList n) (fpq : (p q : FL n) → FL n) : Set where
   field
     commList : FList n
     commAny : (p q : FL n)
         → Any ( p ≡_ ) P →  Any ( q ≡_ ) Q
         → Any (fpq p q ≡_) commList

-------------
--    (p,q)   (p,qn) ....           (p,q0)
--    pn,q       
--     :        AnyComm FL0 FL0 P  Q
--    p0,q       

p<anyL : {n : ℕ } {p p₁ : FL n} {P : FList n} → {pr : fresh (FL n) ⌊ _f<?_ ⌋ p P } → Any (_≡_ p₁) (cons p P pr) → p f≤ p₁
p<anyL {n} {p} {p₁} {P} {pr} (here refl) = case1 refl
p<anyL {n} {p} {p₁} {cons a P x} { Data.Product._,_ (Level.lift p<a) snd} (there any) with p<anyL any
... | case1 refl = case2 (toWitness p<a)
... | case2 a<p₁ = case2 (f<-trans (toWitness p<a) a<p₁)

p<anyL1 : {n : ℕ } {p p₁ : FL n} {P : FList n} → {pr : fresh (FL n) ⌊ _f<?_ ⌋ p P } → Any (_≡_ p₁) (cons p P pr) → ¬ (p ≡ p₁)  → p f< p₁
p<anyL1 {n} {p} {p₁} {P} {pr} any neq with p<anyL any
... | case1 eq = ⊥-elim ( neq eq )
... | case2 x = x

open AnyComm 
anyComm : {n : ℕ } → (P Q : FList n) → (fpq : (p q : FL n) → FL n)  → AnyComm P Q fpq
anyComm [] [] _ = record { commList = [] ; commAny = λ _ _ () }
anyComm [] (cons q Q qr) _ = record { commList = [] ; commAny = λ _ _ () }
anyComm (cons p P pr) [] _ = record { commList = [] ; commAny = λ _ _ _ () }
anyComm {n} (cons p P pr) (cons q Q qr) fpq = record { commList = FLinsert (fpq p q) (commListQ Q)  ; commAny = anyc0n } where 
  commListP : (P1 : FList n) → FList n
  commListP [] = commList (anyComm {n} P Q fpq)
  commListP (cons p₁ P1 x) =  FLinsert (fpq p₁ q) (commListP P1)
  commListQ : (Q1 : FList n) → FList n
  commListQ [] = commListP P
  commListQ (cons q₁ Q1 qr₁) = FLinsert (fpq p q₁) (commListQ Q1)
  anyc0n : (p₁ q₁ : FL n) → Any (_≡_ p₁) (cons p P pr) → Any (_≡_ q₁) (cons q Q qr)
    → Any (_≡_ (fpq p₁ q₁)) (FLinsert (fpq p q) (commListQ Q))
  anyc0n p₁ q₁ (here refl) (here refl) = x∈FLins _ (commListQ Q )
  anyc0n p₁ q₁ (here refl) (there anyq) = insAny (commListQ Q) (anyc01 Q anyq) where 
     anyc01 : (Q1 : FList n) → Any (_≡_ q₁) Q1 → Any (_≡_ (fpq p₁ q₁)) (commListQ Q1)
     anyc01 (cons q Q1 qr₂) (here refl) = x∈FLins _ _
     anyc01 (cons q₂ Q1 qr₂) (there any) = insAny _ (anyc01 Q1 any)
  anyc0n p₁ q₁ (there anyp) (here refl) = insAny _ (anyc02 Q) where
     anyc03 : (P1 : FList n) → Any (_≡_ p₁) P1  → Any (_≡_ (fpq p₁ q₁)) (commListP P1)
     anyc03 (cons a P1 x) (here refl) = x∈FLins _ _ 
     anyc03 (cons a P1 x) (there any) = insAny _ ( anyc03 P1 any) 
     anyc02 : (Q1 : FList n) → Any (_≡_ (fpq p₁ q₁)) (commListQ Q1)
     anyc02 [] = anyc03 P anyp
     anyc02 (cons a Q1 x) = insAny _ (anyc02 Q1)
  anyc0n p₁ q₁ (there anyp) (there anyq) = insAny (commListQ Q) (anyc04 Q) where
     anyc05 : (P1 : FList n) → Any (_≡_ (fpq p₁ q₁)) (commListP P1)
     anyc05 [] = commAny (anyComm P Q fpq) p₁ q₁ anyp anyq
     anyc05 (cons a P1 x) = insAny _ (anyc05 P1)
     anyc04 : (Q1 : FList n) → Any (_≡_ (fpq p₁ q₁)) (commListQ Q1)
     anyc04 [] = anyc05 P 
     anyc04 (cons a Q1 x) = insAny _ (anyc04 Q1)

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
