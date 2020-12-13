{-# OPTIONS --allow-unsolved-metas #-} 
module Putil where

open import Level hiding ( suc ; zero )
open import Algebra
open import Algebra.Structures
open import Data.Fin hiding ( _<_  ; _≤_ ; _-_ ; _+_ ; _≟_)
open import Data.Fin.Properties hiding ( <-trans ; ≤-trans ; ≤-irrelevant ; _≟_ ) renaming ( <-cmp to <-fcmp )
open import Data.Fin.Permutation
open import Function hiding (id ; flip)
open import Function.Inverse as Inverse using (_↔_; Inverse; _InverseOf_)
open import Function.LeftInverse  using ( _LeftInverseOf_ )
open import Function.Equality using (Π)
open import Data.Nat -- using (ℕ; suc; zero; s≤s ; z≤n )
open import Data.Nat.Properties -- using (<-trans)
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.List using (List; []; _∷_ ; length ; _++_ ; head ; tail ) renaming (reverse to rev )
open import nat

open import Symmetric


open import Relation.Nullary
open import Data.Empty
open import  Relation.Binary.Core
open import  Relation.Binary.Definitions
open import fin

-- An inductive construction of permutation

pprep  : {n : ℕ }  → Permutation n n → Permutation (suc n) (suc n)
pprep {n} perm =  permutation p→ p← record { left-inverse-of = piso→ ; right-inverse-of = piso← } where
   p→ : Fin (suc n) → Fin (suc n)
   p→ zero = zero
   p→ (suc x) = suc ( perm  ⟨$⟩ʳ x)

   p← : Fin (suc n) → Fin (suc n)
   p← zero = zero
   p← (suc x) = suc ( perm  ⟨$⟩ˡ x)

   piso← : (x : Fin (suc n)) → p→ ( p← x ) ≡ x
   piso← zero = refl
   piso← (suc x) = cong (λ k → suc k ) (inverseʳ perm) 

   piso→ : (x : Fin (suc n)) → p← ( p→ x ) ≡ x
   piso→ zero = refl
   piso→ (suc x) = cong (λ k → suc k ) (inverseˡ perm) 

pswap  : {n : ℕ }  → Permutation n n → Permutation (suc (suc n)) (suc (suc  n ))
pswap {n} perm = permutation p→ p← record { left-inverse-of = piso→ ; right-inverse-of = piso← } where
   p→ : Fin (suc (suc n)) → Fin (suc (suc n)) 
   p→ zero = suc zero 
   p→ (suc zero) = zero 
   p→ (suc (suc x)) = suc ( suc ( perm  ⟨$⟩ʳ x) )

   p← : Fin (suc (suc n)) → Fin (suc (suc n)) 
   p← zero = suc zero 
   p← (suc zero) = zero 
   p← (suc (suc x)) = suc ( suc ( perm  ⟨$⟩ˡ x) )
   
   piso← : (x : Fin (suc (suc n)) ) → p→ ( p← x ) ≡ x
   piso← zero = refl
   piso← (suc zero) = refl
   piso← (suc (suc x)) = cong (λ k → suc (suc k) ) (inverseʳ perm) 

   piso→ : (x : Fin (suc (suc n)) ) → p← ( p→ x ) ≡ x
   piso→ zero = refl
   piso→ (suc zero) = refl
   piso→ (suc (suc x)) = cong (λ k → suc (suc k) ) (inverseˡ perm) 

psawpn : {n : ℕ} → 1 < n → Permutation n n
psawpn {suc zero}  (s≤s ())
psawpn {suc n} (s≤s (s≤s x)) = pswap pid 

pfill : { n m : ℕ } → m ≤ n → Permutation  m m → Permutation n n
pfill {n} {m} m≤n perm = pfill1 (n - m) (n-m<n n m ) (subst (λ k → Permutation k k ) (n-n-m=m m≤n ) perm) where
   pfill1 : (i : ℕ ) → i ≤ n  → Permutation (n - i) (n - i)  →  Permutation n n
   pfill1 0 _ perm = perm
   pfill1 (suc i) i<n perm = pfill1 i (≤to< i<n) (subst (λ k → Permutation k k ) (si-sn=i-n i<n ) ( pprep perm ) )

--
--  psawpim (inseert swap at position m )
--
psawpim : {n m : ℕ} → suc (suc m) ≤ n → Permutation n n
psawpim {n} {m} m≤n = pfill m≤n ( psawpn (s≤s (s≤s z≤n)) )

n≤ : (i : ℕ ) → {j : ℕ } → i ≤ i + j
n≤ (zero) {j} = z≤n
n≤ (suc i) {j} = s≤s ( n≤ i )

lem0 : {n : ℕ } → n ≤ n
lem0 {zero} = z≤n
lem0 {suc n} = s≤s lem0

lem00 : {n m : ℕ } → n ≡ m → n ≤ m
lem00 refl = lem0

plist1 : {n  : ℕ} → Permutation (suc n) (suc n) → (i : ℕ ) → i < suc n → List ℕ
plist1  {n} perm zero _           = toℕ ( perm ⟨$⟩ˡ (fromℕ< {zero} (s≤s z≤n))) ∷ []
plist1  {n} perm (suc i) (s≤s lt) = toℕ ( perm ⟨$⟩ˡ (fromℕ< (s≤s lt)))         ∷ plist1 perm  i (<-trans lt a<sa) 

plist  : {n  : ℕ} → Permutation n n → List ℕ
plist {0} perm = []
plist {suc n} perm = rev (plist1 perm n a<sa) 

-- 
--    from n-1 length create n length inserting new element at position m
--
-- 0 ∷ 1 ∷ 2 ∷ 3 ∷ []                               -- 0 ∷ 1 ∷ 2 ∷ 3 ∷ [] 
-- 1 ∷ 0 ∷ 2 ∷ 3 ∷ []    plist ( pins {3} (n≤ 1) )     1 ∷ 0 ∷ 2 ∷ 3 ∷ []
-- 1 ∷ 2 ∷ 0 ∷ 3 ∷ []    plist ( pins {3} (n≤ 2) )     2 ∷ 0 ∷ 1 ∷ 3 ∷ []
-- 1 ∷ 2 ∷ 3 ∷ 0 ∷ []    plist ( pins {3} (n≤ 3) )     3 ∷ 0 ∷ 1 ∷ 2 ∷ []
--
-- defined by pprep and pswap
--
-- pins  : {n m : ℕ} → m ≤ n → Permutation (suc n) (suc n)
-- pins {_} {zero} _ = pid
-- pins {suc _} {suc zero} _ = pswap pid
-- pins {suc (suc n)} {suc m} (s≤s m<n) =  pins1 (suc m) (suc (suc n)) lem0 where
--     pins1 : (i j : ℕ ) → j ≤ suc (suc n)  → Permutation (suc (suc (suc n ))) (suc (suc (suc n)))
--     pins1 _ zero _ = pid
--     pins1 zero _ _ = pid
--     pins1 (suc i) (suc j) (s≤s si≤n) = psawpim {suc (suc (suc n))} {j}  (s≤s (s≤s si≤n))  ∘ₚ  pins1 i j (≤-trans si≤n a≤sa ) 

open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ )
open ≡-Reasoning

pins  : {n m : ℕ} → m ≤ n → Permutation (suc n) (suc n)
pins {_} {zero} _ = pid
pins {suc n} {suc m} (s≤s  m≤n) = permutation p← p→  record { left-inverse-of = piso← ; right-inverse-of = piso→ } where

   next : Fin (suc (suc n)) → Fin (suc (suc n))
   next zero = suc zero
   next (suc x) = fromℕ< (≤-trans (fin<n {_} {x} ) a≤sa )

   p→ : Fin (suc (suc n)) → Fin (suc (suc n)) 
   p→ x with <-cmp (toℕ x) (suc m)
   ... | tri< a ¬b ¬c = fromℕ< (≤-trans (s≤s  a) (s≤s (s≤s  m≤n) )) 
   ... | tri≈ ¬a b ¬c = zero
   ... | tri> ¬a ¬b c = x

   p← : Fin (suc (suc n)) → Fin (suc (suc n)) 
   p← zero = fromℕ< (s≤s (s≤s m≤n))
   p← (suc x) with <-cmp (toℕ x) (suc m)
   ... | tri< a ¬b ¬c = fromℕ< (≤-trans (fin<n {_} {x}) a≤sa )
   ... | tri≈ ¬a b ¬c = suc x
   ... | tri> ¬a ¬b c = suc x

   mm : toℕ (fromℕ< {suc m} {suc (suc n)} (s≤s (s≤s m≤n))) ≡ suc m 
   mm = toℕ-fromℕ< (s≤s (s≤s  m≤n)) 

   mma : (x : Fin (suc n) ) → suc (toℕ x) ≤ suc m → toℕ ( fromℕ< (≤-trans (fin<n {_} {x}) a≤sa ) ) ≤ m
   mma x (s≤s x<sm) = subst (λ k → k ≤ m) (sym (toℕ-fromℕ< (≤-trans fin<n a≤sa ) )) x<sm
   
   p3 : (x : Fin (suc n) ) →  toℕ (fromℕ< (≤-trans (fin<n {_} {suc x} ) (s≤s a≤sa))) ≡ suc (toℕ x)
   p3 x = begin
            toℕ (fromℕ< (≤-trans (fin<n {_} {suc x} ) (s≤s a≤sa)))
          ≡⟨ toℕ-fromℕ< ( s≤s ( ≤-trans fin<n  a≤sa ) ) ⟩
            suc (toℕ x)
          ∎ 

   piso→ : (x : Fin (suc (suc n)) ) → p← ( p→ x ) ≡ x
   piso→ zero with <-cmp (toℕ (fromℕ< (≤-trans (s≤s z≤n) (s≤s (s≤s  m≤n) )))) (suc m)
   ... | tri< a ¬b ¬c = refl
   piso→ (suc x) with <-cmp (toℕ (suc x)) (suc m)
   ... | tri≈ ¬a refl ¬c = p13 where
       p13 : fromℕ< (s≤s (s≤s m≤n)) ≡ suc x
       p13 = cong (λ k → suc k ) (fromℕ<-toℕ _ (s≤s m≤n) )
   ... | tri> ¬a ¬b c = p16 (suc x) refl where
       p16 : (y :  Fin (suc (suc n))) → y ≡ suc x → p← y ≡ suc x
       p16 zero eq = ⊥-elim ( nat-≡< (cong (λ k → suc (toℕ k) ) eq) (s≤s (s≤s (z≤n))))
       p16 (suc y) eq with <-cmp (toℕ y) (suc m)   -- suc (suc m) < toℕ (suc x)
       ... | tri< a ¬b ¬c = ⊥-elim ( nat-≡< refl ( ≤-trans c (subst (λ k → k < suc m) p17 a )) ) where
           --  x = suc m case, c : suc (suc m) ≤ suc (toℕ x), a : suc (toℕ y) ≤ suc m,  suc y ≡ suc x
           p17 : toℕ y ≡ toℕ x
           p17 with <-cmp (toℕ y) (toℕ x) | cong toℕ eq
           ... | tri< a ¬b ¬c | seq =  ⊥-elim ( nat-≡< seq (s≤s a) )
           ... | tri≈ ¬a b ¬c | seq = b
           ... | tri> ¬a ¬b c | seq =  ⊥-elim ( nat-≡< (sym seq) (s≤s c))
       ... | tri≈ ¬a b ¬c = eq 
       ... | tri> ¬a ¬b c₁ = eq 
   ... | tri< a ¬b ¬c = p10 (fromℕ< (≤-trans (s≤s  a) (s≤s (s≤s  m≤n) ))) refl  where
       p10 : (y : Fin (suc (suc n)) ) → y ≡ fromℕ< (≤-trans (s≤s  a) (s≤s (s≤s  m≤n) ))  → p← y ≡ suc x
       p10 zero ()
       p10 (suc y) eq = p15 where
          p12 : toℕ y ≡ suc (toℕ x)
          p12 = begin
               toℕ y
             ≡⟨ cong (λ k → Data.Nat.pred (toℕ k)) eq ⟩
               toℕ (fromℕ< (≤-trans a (s≤s m≤n)))
             ≡⟨ toℕ-fromℕ< {suc (toℕ x)} {suc n} (≤-trans a (s≤s m≤n)) ⟩
               suc (toℕ x)
             ∎
          p15 : p← (suc y) ≡ suc x
          p15 with <-cmp (toℕ y) (suc m) -- eq : suc y ≡ suc (suc (fromℕ< (≤-pred (≤-trans a (s≤s m≤n))))) ,  a : suc x < suc m
          ... | tri< a₁ ¬b ¬c = p11 where
            p11 : fromℕ< (≤-trans (fin<n {_} {y}) a≤sa ) ≡ suc x
            p11 = begin
               fromℕ< (≤-trans (fin<n {_} {y}) a≤sa )
              ≡⟨ lemma10 {suc (suc n)} {_} {_} p12 {≤-trans (fin<n {_} {y}) a≤sa} {s≤s (fin<n {suc n} {x} )}  ⟩
               suc (fromℕ< (fin<n {suc n} {x} )) 
              ≡⟨ cong suc (fromℕ<-toℕ x _ ) ⟩
               suc x
              ∎
          ... | tri≈ ¬a b ¬c = ⊥-elim ( nat-≡< b (subst (λ k → k < suc m) (sym p12) a ))  --  suc x < suc m -> y = suc x  → toℕ y < suc m 
          ... | tri> ¬a ¬b c = ⊥-elim ( nat-<> c (subst (λ k → k < suc m) (sym p12) a ))  

   piso← : (x : Fin (suc (suc n)) ) → p→ ( p← x ) ≡ x
   piso← zero with <-cmp (toℕ (fromℕ< (s≤s (s≤s m≤n)))) (suc m) | mm
   ... | tri< a ¬b ¬c | t = ⊥-elim ( ¬b t )
   ... | tri≈ ¬a b ¬c | t = refl
   ... | tri> ¬a ¬b c | t = ⊥-elim ( ¬b t )
   piso← (suc x) with <-cmp (toℕ x) (suc m)
   ... | tri> ¬a ¬b c with <-cmp (toℕ (suc x)) (suc m)
   ... | tri< a ¬b₁ ¬c = ⊥-elim ( nat-<> a (<-trans c a<sa ) )
   ... | tri≈ ¬a₁ b ¬c = ⊥-elim (  nat-≡< (sym b) (<-trans c a<sa ))
   ... | tri> ¬a₁ ¬b₁ c₁ = refl
   piso← (suc x) | tri≈ ¬a b ¬c with <-cmp (toℕ (suc x)) (suc m)
   ... | tri< a ¬b ¬c₁ = ⊥-elim (  nat-≡< b (<-trans a<sa a) ) 
   ... | tri≈ ¬a₁ refl ¬c₁ = ⊥-elim ( nat-≡< b a<sa )
   ... | tri> ¬a₁ ¬b c = refl
   piso← (suc x) | tri< a ¬b ¬c with <-cmp (toℕ ( fromℕ< (≤-trans (fin<n {_} {x}) a≤sa ) )) (suc m)
   ... | tri≈ ¬a b ¬c₁ = ⊥-elim ( ¬a (s≤s (mma x a)))
   ... | tri> ¬a ¬b₁ c = ⊥-elim ( ¬a (s≤s (mma x a)))
   ... | tri< a₁ ¬b₁ ¬c₁ = p0 where
       p2 : suc (suc (toℕ x)) ≤ suc (suc n)
       p2 = s≤s (fin<n {suc n} {x})
       p6 : suc (toℕ (fromℕ< (≤-trans (fin<n {_} {suc x}) (s≤s a≤sa)))) ≤ suc (suc n)
       p6 = s≤s (≤-trans a₁ (s≤s m≤n))
       p0 : fromℕ< (≤-trans (s≤s  a₁) (s≤s (s≤s  m≤n) ))  ≡ suc x
       p0 = begin
             fromℕ< (≤-trans (s≤s  a₁) (s≤s (s≤s  m≤n) ))
          ≡⟨⟩
             fromℕ< (s≤s (≤-trans a₁ (s≤s m≤n))) 
          ≡⟨ lemma10 {suc (suc n)} (p3 x) {p6} {p2} ⟩
             fromℕ< ( s≤s (fin<n {suc n} {x}) )
          ≡⟨⟩
             suc (fromℕ< (fin<n {suc n} {x} )) 
          ≡⟨ cong suc (fromℕ<-toℕ x _ ) ⟩
             suc x
          ∎ 

t7 =  plist (pins {3} (n≤ 3)) ∷ plist (flip ( pins {3} (n≤ 3) )) ∷  plist ( pins {3} (n≤ 3)  ∘ₚ  flip ( pins {3} (n≤ 3))) ∷ []
-- t8 =  {!!}

open import logic 

open _∧_

perm1 :  {perm : Permutation 1 1 } {q : Fin 1}  → (perm ⟨$⟩ʳ q ≡ # 0)  ∧ ((perm ⟨$⟩ˡ q ≡ # 0))
perm1 {p} {q} = ⟪ perm01 _ _ , perm00 _ _ ⟫ where
   perm01 : (x y : Fin 1) → (p ⟨$⟩ʳ x) ≡  y
   perm01 x y with p ⟨$⟩ʳ x
   perm01 zero zero | zero = refl
   perm00 : (x y : Fin 1) → (p ⟨$⟩ˡ x) ≡  y
   perm00 x y with p ⟨$⟩ˡ x
   perm00 zero zero | zero = refl


----
--  find insertion point of pins
----
p=0 : {n : ℕ }  → (perm : Permutation (suc n) (suc n) ) → ((perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))) ⟨$⟩ˡ (# 0)) ≡ # 0
p=0 {zero} perm with ((perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))) ⟨$⟩ˡ (# 0)) 
... | zero = refl
p=0 {suc n} perm with perm ⟨$⟩ʳ (# 0) | inspect (_⟨$⟩ʳ_ perm ) (# 0)| toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0)) | inspect toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))
... | zero |  record { eq = e} |  m<n | _ = p001 where
   p001 : perm ⟨$⟩ˡ ( pins m<n ⟨$⟩ʳ zero) ≡ zero
   p001 = subst (λ k → perm ⟨$⟩ˡ k ≡ zero ) e (inverseˡ perm)
... | suc t |  record { eq = e } | m<n | record { eq = e1 }  = p002 where   -- m<n  : suc (toℕ t) ≤ suc n
   p002 : perm ⟨$⟩ˡ ( pins m<n ⟨$⟩ʳ zero) ≡ zero
   p002 = p005 zero (toℕ t)  refl m<n refl where   -- suc (toℕ t) ≤ suc n
      p003 : (s : Fin (suc (suc n))) → s ≡ (perm ⟨$⟩ʳ (# 0)) → perm ⟨$⟩ˡ s  ≡ # 0
      p003 s eq = subst (λ k → perm ⟨$⟩ˡ k ≡ zero ) (sym eq) (inverseˡ perm)
      p005 : (x :  Fin (suc (suc n))) → (m : ℕ ) → x ≡ zero → (m≤n : suc m ≤ suc n ) → m ≡ toℕ t → perm ⟨$⟩ˡ ( pins m≤n ⟨$⟩ʳ zero) ≡ zero
      p005 zero m eq (s≤s m≤n) meq = p004 where
          p004 :  perm ⟨$⟩ˡ (fromℕ< (s≤s (s≤s m≤n))) ≡ zero
          p004 = p003  (fromℕ< (s≤s (s≤s m≤n))) (
             begin
                fromℕ< (s≤s (s≤s m≤n))
             ≡⟨  lemma10 {suc (suc n)}  (cong suc meq) {s≤s (s≤s m≤n)} {subst (λ k →  suc k < suc (suc n)) meq (s≤s (s≤s m≤n)) } ⟩
                fromℕ< (subst (λ k →  suc k < suc (suc n)) meq (s≤s (s≤s m≤n)) )
             ≡⟨ fromℕ<-toℕ {suc (suc n)} (suc t) (subst (λ k →  suc k < suc (suc n)) meq (s≤s (s≤s m≤n)) ) ⟩
                suc t
             ≡⟨ sym e ⟩
                (perm ⟨$⟩ʳ (# 0))
             ∎ )

----
--  other elements are preserved in pins
----
px=x : {n : ℕ }  → (x : Fin (suc n)) → pins ( toℕ≤pred[n] x ) ⟨$⟩ʳ (# 0) ≡ x
px=x {n} zero = refl
px=x {suc n} (suc x) = p001 where
     p002 : fromℕ< (s≤s (toℕ≤pred[n] x)) ≡ x
     p002 =  fromℕ<-toℕ x (s≤s (toℕ≤pred[n] x)) 
     p001 :  (pins (toℕ≤pred[n] (suc x)) ⟨$⟩ʳ (# 0)) ≡ suc x
     p001 with <-cmp 0 ((toℕ x))
     ... | tri< a ¬b ¬c = cong suc p002
     ... | tri≈ ¬a b ¬c = cong suc p002

-- pp : {n : ℕ }  → (perm : Permutation (suc n) (suc n) ) →  Fin (suc n)
-- pp  perm → (( perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))) ⟨$⟩ˡ (# 0))

plist2 : {n  : ℕ} → Permutation (suc n) (suc n) → (i : ℕ ) → i < suc n → List ℕ
plist2  {n} perm zero _           = toℕ ( perm ⟨$⟩ʳ (fromℕ< {zero} (s≤s z≤n))) ∷ []
plist2  {n} perm (suc i) (s≤s lt) = toℕ ( perm ⟨$⟩ʳ (fromℕ< (s≤s lt)))         ∷ plist2 perm  i (<-trans lt a<sa) 

plist0  : {n  : ℕ} → Permutation n n → List ℕ
plist0 {0} perm = []
plist0 {suc n} perm = plist2 perm n a<sa

open _=p=_

--
-- plist cong
--
←pleq  : {n  : ℕ} → (x y : Permutation n n ) → x =p= y → plist0 x ≡ plist0 y 
←pleq {zero} x y eq = refl
←pleq {suc n} x y eq =  ←pleq1  n a<sa where
   ←pleq1  :   (i : ℕ ) → (i<sn : i < suc n ) →  plist2 x i i<sn ≡ plist2 y i i<sn
   ←pleq1  zero _           = cong ( λ k → toℕ k ∷ [] ) ( peq eq (fromℕ< {zero} (s≤s z≤n)))
   ←pleq1  (suc i) (s≤s lt) = cong₂ ( λ j k → toℕ j ∷ k ) ( peq eq (fromℕ< (s≤s lt)))  ( ←pleq1  i (<-trans lt a<sa) )

headeq : {A : Set } →  {x y : A } → {xt yt : List A } → (x ∷ xt)  ≡ (y ∷ yt)  →  x ≡ y
headeq refl = refl

taileq : {A : Set } →  {x y : A } → {xt yt : List A } → (x ∷ xt)  ≡ (y ∷ yt)  →  xt ≡ yt
taileq refl = refl

--
-- plist injection / equalizer 
--
--    if plist0 of two perm looks the same, the permutations are the same
--
pleq  : {n  : ℕ} → (x y : Permutation n n ) → plist0 x ≡ plist0 y → x =p= y
pleq  {0} x y refl = record { peq = λ q → pleq0 q } where
  pleq0 : (q : Fin 0 ) → (x ⟨$⟩ʳ q) ≡ (y ⟨$⟩ʳ q)
  pleq0 ()
pleq  {suc n} x y eq = record { peq = λ q → pleq1 n a<sa eq q fin<n } where
  pleq1 : (i : ℕ ) → (i<sn : i < suc n ) →  plist2 x i i<sn ≡ plist2 y i i<sn → (q : Fin (suc n)) → toℕ q < suc i → x ⟨$⟩ʳ q ≡ y ⟨$⟩ʳ q
  pleq1 zero i<sn eq q q<i with  <-cmp (toℕ q) zero
  ... | tri< () ¬b ¬c
  ... | tri> ¬a ¬b c = ⊥-elim (nat-≤> c q<i )
  ... | tri≈ ¬a b ¬c = begin
          x ⟨$⟩ʳ q
       ≡⟨ cong ( λ k → x ⟨$⟩ʳ k ) (toℕ-injective b )⟩
          x ⟨$⟩ʳ zero
       ≡⟨ toℕ-injective (headeq eq) ⟩
          y ⟨$⟩ʳ zero
       ≡⟨ cong ( λ k → y ⟨$⟩ʳ k ) (sym (toℕ-injective b )) ⟩
          y ⟨$⟩ʳ q
       ∎ 
  pleq1 (suc i) (s≤s i<sn) eq q q<i with <-cmp (toℕ q) (suc i)
  ... | tri< a ¬b ¬c = pleq1 i (<-trans i<sn a<sa ) (taileq eq) q a
  ... | tri> ¬a ¬b c = ⊥-elim (nat-≤> c q<i )
  ... | tri≈ ¬a b ¬c = begin
            x ⟨$⟩ʳ q
       ≡⟨ cong (λ k → x ⟨$⟩ʳ k) (pleq3 b) ⟩
            x ⟨$⟩ʳ (suc (fromℕ< i<sn))
       ≡⟨ toℕ-injective pleq2  ⟩
            y ⟨$⟩ʳ (suc (fromℕ< i<sn))
       ≡⟨ cong (λ k → y ⟨$⟩ʳ k) (sym (pleq3 b)) ⟩
            y ⟨$⟩ʳ q
       ∎ where
          pleq3 : toℕ q ≡ suc i → q ≡ suc (fromℕ< i<sn)
          pleq3 tq=si = toℕ-injective ( begin
                  toℕ  q
               ≡⟨ b ⟩
                  suc i
               ≡⟨ sym (toℕ-fromℕ< (s≤s i<sn)) ⟩
                  toℕ (fromℕ< (s≤s i<sn))
               ≡⟨⟩
                  toℕ (suc (fromℕ< i<sn))
               ∎ ) 
          pleq2 : toℕ ( x ⟨$⟩ʳ (suc (fromℕ< i<sn)) ) ≡ toℕ ( y ⟨$⟩ʳ (suc (fromℕ< i<sn)) )
          pleq2 = headeq eq

is-=p= : {n  : ℕ} → (x y : Permutation n n ) → Dec (x =p= y )
is-=p= {zero} x y = yes record { peq = λ () }
is-=p= {suc n} x y with ℕL-eq? (plist0 x ) ( plist0 y )
... | yes t = yes (pleq x y t)
... | no t = no ( contra-position (←pleq x y) t )

pprep-cong : {n  : ℕ} → {x y : Permutation n n } → x =p= y → pprep x =p= pprep y
pprep-cong {n} {x} {y} x=y = record { peq = pprep-cong1 } where
   pprep-cong1 : (q : Fin (suc n)) → (pprep x ⟨$⟩ʳ q) ≡ (pprep y ⟨$⟩ʳ q)
   pprep-cong1 zero = refl
   pprep-cong1 (suc q) = begin
          pprep x ⟨$⟩ʳ suc q
        ≡⟨⟩
          suc ( x ⟨$⟩ʳ q )
        ≡⟨ cong ( λ k → suc k ) ( peq x=y q ) ⟩
          suc ( y ⟨$⟩ʳ q )
        ≡⟨⟩
          pprep y ⟨$⟩ʳ suc q
        ∎  

pprep-dist : {n  : ℕ} → {x y : Permutation n n } → pprep (x ∘ₚ y) =p= (pprep x ∘ₚ pprep y)
pprep-dist {n} {x} {y} = record { peq = pprep-dist1 } where
   pprep-dist1 : (q : Fin (suc n)) → (pprep (x ∘ₚ y) ⟨$⟩ʳ q) ≡ ((pprep x ∘ₚ pprep y) ⟨$⟩ʳ q)
   pprep-dist1 zero = refl
   pprep-dist1 (suc q) =  cong ( λ k → suc k ) refl

pswap-cong : {n  : ℕ} → {x y : Permutation n n } → x =p= y → pswap x =p= pswap y
pswap-cong {n} {x} {y} x=y = record { peq = pswap-cong1 } where
   pswap-cong1 : (q : Fin (suc (suc n))) → (pswap x ⟨$⟩ʳ q) ≡ (pswap y ⟨$⟩ʳ q)
   pswap-cong1 zero = refl
   pswap-cong1 (suc zero) = refl
   pswap-cong1 (suc (suc q)) = begin
          pswap x ⟨$⟩ʳ suc (suc q)
        ≡⟨⟩
          suc (suc (x ⟨$⟩ʳ q))
        ≡⟨ cong ( λ k → suc (suc k) ) ( peq x=y q ) ⟩
          suc (suc (y ⟨$⟩ʳ q))
        ≡⟨⟩
          pswap y ⟨$⟩ʳ suc (suc q)
        ∎  
 
pswap-dist : {n  : ℕ} → {x y : Permutation n n } → pprep (pprep (x ∘ₚ y)) =p= (pswap x ∘ₚ pswap y)
pswap-dist {n} {x} {y} = record { peq = pswap-dist1 } where
   pswap-dist1 : (q : Fin (suc (suc n))) → ((pprep (pprep (x ∘ₚ y))) ⟨$⟩ʳ q) ≡ ((pswap x ∘ₚ pswap y) ⟨$⟩ʳ q)
   pswap-dist1 zero = refl
   pswap-dist1 (suc zero) = refl
   pswap-dist1 (suc (suc q)) =  cong ( λ k → suc (suc k) ) refl

shlem→ : {n  : ℕ} → (perm : Permutation (suc n) (suc n) ) → (p0=0 : perm ⟨$⟩ˡ (# 0) ≡ # 0 ) → (x : Fin (suc n) ) →  perm ⟨$⟩ˡ x ≡ zero → x ≡ zero
shlem→ perm p0=0 x px=0 = begin
          x                                  ≡⟨ sym ( inverseʳ perm ) ⟩
          perm ⟨$⟩ʳ ( perm ⟨$⟩ˡ x)           ≡⟨ cong (λ k →  perm ⟨$⟩ʳ k ) px=0 ⟩
          perm ⟨$⟩ʳ zero                     ≡⟨ cong (λ k →  perm ⟨$⟩ʳ k ) (sym p0=0) ⟩
          perm ⟨$⟩ʳ ( perm ⟨$⟩ˡ zero)        ≡⟨ inverseʳ perm  ⟩
          zero
       ∎ 

shlem← : {n  : ℕ} → (perm : Permutation (suc n) (suc n) ) → (p0=0 : perm ⟨$⟩ˡ (# 0) ≡ # 0 ) → (x : Fin (suc n)) → perm ⟨$⟩ʳ x ≡ zero → x ≡ zero
shlem← perm p0=0 x px=0 =  begin
          x                                  ≡⟨ sym (inverseˡ perm ) ⟩
          perm ⟨$⟩ˡ ( perm ⟨$⟩ʳ x )          ≡⟨ cong (λ k →  perm ⟨$⟩ˡ k ) px=0 ⟩
          perm ⟨$⟩ˡ zero                     ≡⟨ p0=0  ⟩
          zero
       ∎ 

sh2 : {n  : ℕ} → (perm : Permutation (suc n) (suc n) ) → (p0=0 : perm ⟨$⟩ˡ (# 0) ≡ # 0 ) → {x : Fin n} → ¬ perm ⟨$⟩ˡ (suc x) ≡ zero
sh2 perm p0=0 {x} eq with shlem→ perm p0=0 (suc x) eq
sh2 perm p0=0 {x} eq | ()

sh1 : {n  : ℕ} → (perm : Permutation (suc n) (suc n) ) → (p0=0 : perm ⟨$⟩ˡ (# 0) ≡ # 0 ) → {x : Fin n} → ¬ perm ⟨$⟩ʳ (suc x) ≡ zero
sh1 perm p0=0 {x} eq with shlem← perm p0=0 (suc x) eq
sh1 perm p0=0 {x} eq | ()


-- 0 ∷ 1 ∷ 2 ∷ 3 ∷ [] → 0 ∷ 1 ∷ 2 ∷ [] 
shrink : {n  : ℕ} → (perm : Permutation (suc n) (suc n) ) → perm ⟨$⟩ˡ (# 0) ≡ # 0 → Permutation n n
shrink {n} perm p0=0  = permutation p→ p← record { left-inverse-of = piso→ ; right-inverse-of = piso← } where

   p→ : Fin n → Fin n 
   p→ x with perm ⟨$⟩ʳ (suc x) | inspect (_⟨$⟩ʳ_ perm ) (suc x) 
   p→ x | zero  | record { eq = e } = ⊥-elim ( sh1 perm p0=0 {x} e )
   p→ x | suc t | _ = t

   p← : Fin n → Fin n 
   p← x with perm ⟨$⟩ˡ (suc x) | inspect (_⟨$⟩ˡ_ perm ) (suc x) 
   p← x | zero  | record { eq = e } = ⊥-elim ( sh2 perm p0=0 {x} e )
   p← x | suc t | _ = t

   piso← : (x : Fin n ) → p→ ( p← x ) ≡ x
   piso← x with perm ⟨$⟩ˡ (suc x) | inspect (_⟨$⟩ˡ_ perm ) (suc x) 
   piso← x | zero  | record { eq = e } = ⊥-elim ( sh2 perm p0=0 {x} e )
   piso← x | suc t | _ with perm ⟨$⟩ʳ (suc t) | inspect (_⟨$⟩ʳ_ perm ) (suc t)
   piso← x | suc t | _ | zero |  record { eq = e } =  ⊥-elim ( sh1 perm p0=0 e )
   piso← x | suc t |  record { eq = e0 } | suc t1 |  record { eq = e1 } = begin
          t1
       ≡⟨ plem0 plem1 ⟩
          x
       ∎ where
          open ≡-Reasoning
          plem0 :  suc t1 ≡ suc x → t1 ≡ x
          plem0 refl = refl
          plem1 :  suc t1 ≡ suc x
          plem1 = begin
               suc t1
            ≡⟨ sym e1 ⟩
               Inverse.to perm Π.⟨$⟩ suc t
            ≡⟨ cong (λ k →  Inverse.to perm Π.⟨$⟩ k ) (sym e0) ⟩
               Inverse.to perm Π.⟨$⟩ ( Inverse.from perm Π.⟨$⟩ suc x )
            ≡⟨ inverseʳ perm   ⟩
               suc x
            ∎ 

   piso→ : (x : Fin n ) → p← ( p→ x ) ≡ x
   piso→ x with perm ⟨$⟩ʳ (suc x) | inspect (_⟨$⟩ʳ_ perm ) (suc x)
   piso→ x | zero  | record { eq = e } = ⊥-elim ( sh1 perm p0=0 {x} e )
   piso→ x | suc t | _ with perm ⟨$⟩ˡ (suc t) | inspect (_⟨$⟩ˡ_ perm ) (suc t)
   piso→ x | suc t | _ | zero |  record { eq = e } =  ⊥-elim ( sh2 perm p0=0 e )
   piso→ x | suc t |  record { eq = e0 } | suc t1 |  record { eq = e1 } = begin
          t1
       ≡⟨ plem2 plem3 ⟩
          x
       ∎ where
          plem2 :  suc t1 ≡ suc x → t1 ≡ x
          plem2 refl = refl
          plem3 :  suc t1 ≡ suc x
          plem3 = begin
               suc t1
            ≡⟨ sym e1 ⟩
               Inverse.from perm Π.⟨$⟩ suc t
            ≡⟨ cong (λ k →  Inverse.from perm Π.⟨$⟩ k ) (sym e0 ) ⟩
               Inverse.from perm Π.⟨$⟩ ( Inverse.to perm Π.⟨$⟩ suc x )
            ≡⟨ inverseˡ perm   ⟩
               suc x
            ∎

shrink-iso : { n : ℕ } → {perm : Permutation n n} → shrink (pprep perm)  refl =p=  perm
shrink-iso {n} {perm} = record { peq = λ q → refl  } 

shrink-iso2 : { n : ℕ } → {perm : Permutation (suc n) (suc n)} 
   → (p=0 : perm ⟨$⟩ˡ (# 0) ≡ # 0)  → pprep (shrink perm p=0) =p= perm
shrink-iso2 {n} {perm} p=0 = record { peq =  s001 } where
    s001 : (q : Fin (suc n)) → (pprep (shrink perm p=0) ⟨$⟩ʳ q) ≡ perm ⟨$⟩ʳ q
    s001 zero = begin
         zero
       ≡⟨ sym ( inverseʳ perm ) ⟩
         perm ⟨$⟩ʳ ( perm ⟨$⟩ˡ zero )
       ≡⟨ cong (λ k → perm ⟨$⟩ʳ k ) p=0 ⟩
         perm ⟨$⟩ʳ zero
       ∎ 
    s001 (suc q) with perm ⟨$⟩ʳ (suc q) | inspect (_⟨$⟩ʳ_ perm ) (suc q) 
    ... | zero | record {eq = e}  = ⊥-elim (sh1 perm p=0 {q} e)
    ... | suc t | e = refl


shrink-cong : { n : ℕ } → {x y : Permutation (suc n) (suc n)}
    → x =p= y
    → (x=0 :  x ⟨$⟩ˡ (# 0) ≡ # 0 ) → (y=0 : y ⟨$⟩ˡ (# 0) ≡ # 0 )  → shrink x x=0 =p=  shrink y y=0 
shrink-cong {n} {x} {y} x=y x=0 y=0  = record  { peq = p002 } where
    p002 : (q : Fin n) → (shrink x x=0 ⟨$⟩ʳ q) ≡ (shrink y y=0 ⟨$⟩ʳ q)
    p002 q with x ⟨$⟩ʳ (suc q) | inspect (_⟨$⟩ʳ_ x ) (suc q) | y ⟨$⟩ʳ (suc q) | inspect (_⟨$⟩ʳ_ y ) (suc q)
    p002 q | zero   | record { eq = ex } | zero   | ey                  = ⊥-elim ( sh1 x x=0 ex )
    p002 q | zero   | record { eq = ex } | suc py | ey                  = ⊥-elim ( sh1 x x=0 ex )
    p002 q | suc px | ex                 | zero   | record { eq = ey }  = ⊥-elim ( sh1 y y=0 ey )
    p002 q | suc px | record { eq = ex } | suc py | record { eq = ey }  = p003 ( begin
           suc px
         ≡⟨ sym ex ⟩
           x ⟨$⟩ʳ (suc q)
         ≡⟨ peq x=y (suc q) ⟩
           y ⟨$⟩ʳ (suc q)
         ≡⟨ ey ⟩
           suc py
         ∎ ) where
        p003 : suc px ≡ suc py → px ≡ py
        p003 refl = refl

open import FLutil

FL→perm   : {n : ℕ }  → FL n → Permutation n n 
FL→perm f0 = pid
FL→perm (x :: fl) = pprep (FL→perm fl)  ∘ₚ pins ( toℕ≤pred[n] x )

t40 =                (# 2) :: ( (# 1) :: (( # 0 ) :: f0 )) 
t4 =  FL→perm ((# 2) :: t40 )

-- t1 = plist (shrink (pid {3}  ∘ₚ (pins (n≤ 1))) refl)
t2 = plist ((pid {5} ) ∘ₚ transpose (# 2) (# 4)) ∷ plist (pid {5} ∘ₚ reverse )   ∷  []
t3 = plist (FL→perm t40) -- ∷ plist (pprep (FL→perm t40))
    -- ∷ plist ( pprep (FL→perm t40) ∘ₚ  pins ( n≤ 0 {3}  ))
    -- ∷ plist ( pprep (FL→perm t40 )∘ₚ  pins ( n≤ 1 {2}  ))
    -- ∷ plist ( pprep (FL→perm t40 )∘ₚ  pins ( n≤ 2 {1}  ))
    -- ∷ plist ( pprep (FL→perm t40 )∘ₚ  pins ( n≤ 3 {0}  ))
    ∷ plist ( FL→perm ((# 0) :: t40))  --  (0 ∷ 1 ∷ 2 ∷ []) ∷
    ∷ plist ( FL→perm ((# 1) :: t40))  --  (0 ∷ 2 ∷ 1 ∷ []) ∷
    ∷ plist ( FL→perm ((# 2) :: t40))  --  (1 ∷ 0 ∷ 2 ∷ []) ∷
    ∷ plist ( FL→perm ((# 3) :: t40))  --  (2 ∷ 0 ∷ 1 ∷ []) ∷
    -- ∷ plist ( FL→perm ((# 3) :: ((# 2) :: ( (# 0) :: (( # 0 ) :: f0 )) )))  --  (1 ∷ 2 ∷ 0 ∷ []) ∷
    -- ∷ plist ( FL→perm ((# 3) :: ((# 2) :: ( (# 1) :: (( # 0 ) :: f0 )) )))  --  (2 ∷ 1 ∷ 0 ∷ []) ∷ 
    -- ∷ plist ( (flip (FL→perm ((# 3) :: ((# 1) :: ( (# 0) :: (( # 0 ) :: f0 )) )))))
    -- ∷ plist ( (flip (FL→perm ((# 3) :: ((# 1) :: ( (# 0) :: (( # 0 ) :: f0 )) ))) ∘ₚ (FL→perm ((# 3) :: (((# 1) :: ( (# 0) :: (( # 0 ) :: f0 )) )))) ))
    ∷ []


-- FL→plist-iso : {n : ℕ} → (f : FL n ) → plist→FL (FL→plist f ) ≡ f
-- FL→plist-inject : {n : ℕ} → (f g : FL n ) → FL→plist f ≡ FL→plist g → f ≡ g

perm→FL   : {n : ℕ }  → Permutation n n → FL n
perm→FL {zero} perm = f0
perm→FL {suc n} perm = (perm ⟨$⟩ʳ (# 0)) :: perm→FL (shrink (perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))) (p=0 perm) ) 

---FL→perm   : {n : ℕ }  → FL n → Permutation n n 
---FL→perm   x = plist→perm ( FL→plis x)
-- perm→FL   : {n : ℕ }  → Permutation n n → FL n
-- perm→FL p  = plist→FL (plist p)

-- pcong-pF : {n : ℕ }  → {x y : Permutation n n}  → x =p= y → perm→FL x ≡ perm→FL y
-- pcong-pF {n} {x} {y} x=y = FL→plist-inject (subst ... (pleq← eq)) (perm→FL x) (perm→FL y)

-- FL→iso : {n : ℕ }  → (fl : FL n )  → perm→FL ( FL→perm fl ) ≡ fl
-- FL→iso = 
-- pcong-Fp : {n : ℕ }  → {x y : FL n}  → x ≡ y → FL→perm x =p= FL→perm y
-- FL←iso : {n : ℕ }  → (perm : Permutation n n )  → FL→perm ( perm→FL perm  ) =p= perm

_p<_ : {n : ℕ } ( x y : Permutation n n ) → Set
x p< y = perm→FL x f<  perm→FL y

pcong-pF : {n : ℕ }  → {x y : Permutation n n}  → x =p= y → perm→FL x ≡ perm→FL y
pcong-pF {zero} eq = refl
pcong-pF {suc n} {x} {y} eq = cong₂ (λ j k → j :: k ) ( peq eq (# 0)) (pcong-pF (shrink-cong (presp eq p001 ) (p=0 x) (p=0 y))) where
    p002 : x ⟨$⟩ʳ (# 0) ≡  y ⟨$⟩ʳ (# 0)
    p002 = peq eq (# 0)
    p001 : flip (pins (toℕ≤pred[n] (x ⟨$⟩ʳ (# 0)))) =p=  flip (pins (toℕ≤pred[n] (y ⟨$⟩ʳ (# 0))))
    p001 = subst ( λ k →  flip (pins (toℕ≤pred[n] (x ⟨$⟩ʳ (# 0)))) =p=  flip (pins (toℕ≤pred[n] k ))) p002 prefl 

-- t5 = plist t4 ∷ plist ( t4  ∘ₚ flip (pins ( n≤  3 ) ))
t5 = plist (t4) ∷ plist (flip t4)
    ∷ ( toℕ (t4 ⟨$⟩ˡ fromℕ< a<sa) ∷ [] )
    ∷ ( toℕ (t4 ⟨$⟩ʳ (# 0)) ∷ [] )
    -- ∷  plist ( t4  ∘ₚ flip (pins ( n≤  1 ) ))
    ∷  plist (remove (# 0) t4  )
    ∷  plist ( FL→perm t40 )
    ∷ []
 
t6 = perm→FL t4

FL→iso : {n : ℕ }  → (fl : FL n )  → perm→FL ( FL→perm fl ) ≡ fl
FL→iso f0 = refl
FL→iso {suc n} (x :: fl) = cong₂ ( λ j k → j :: k ) f001 f002 where
    perm = pprep (FL→perm fl)  ∘ₚ pins ( toℕ≤pred[n] x )
    f001 : perm ⟨$⟩ʳ (# 0) ≡ x
    f001 = begin
       (pprep (FL→perm fl)  ∘ₚ pins ( toℕ≤pred[n] x )) ⟨$⟩ʳ (# 0) 
     ≡⟨⟩
       pins ( toℕ≤pred[n] x ) ⟨$⟩ʳ (# 0) 
     ≡⟨ px=x x ⟩
       x 
     ∎
    x=0 :  (perm ∘ₚ flip (pins (toℕ≤pred[n] x))) ⟨$⟩ˡ (# 0) ≡ # 0
    x=0 = subst ( λ k → (perm ∘ₚ flip (pins (toℕ≤pred[n] k))) ⟨$⟩ˡ (# 0) ≡ # 0 ) f001 (p=0 perm)
    x=0' : (pprep (FL→perm fl) ∘ₚ pid) ⟨$⟩ˡ (# 0) ≡ # 0
    x=0' = refl
    f003 : (q : Fin (suc n)) →
            ((perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))) ⟨$⟩ʳ q) ≡
            ((perm ∘ₚ flip (pins (toℕ≤pred[n] x))) ⟨$⟩ʳ q)
    f003 q = cong (λ k → (perm ∘ₚ flip (pins (toℕ≤pred[n] k))) ⟨$⟩ʳ q ) f001 
    f002 : perm→FL (shrink (perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))) (p=0 perm) )  ≡ fl
    f002 = begin
        perm→FL (shrink (perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))) (p=0 perm) )  
     ≡⟨ pcong-pF (shrink-cong {n} {perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))} {perm ∘ₚ flip (pins (toℕ≤pred[n] x))} record {peq = f003 }  (p=0 perm)  x=0) ⟩
        perm→FL (shrink (perm ∘ₚ flip (pins (toℕ≤pred[n] x))) x=0 ) 
     ≡⟨⟩
        perm→FL (shrink ((pprep (FL→perm fl)  ∘ₚ pins ( toℕ≤pred[n] x )) ∘ₚ flip (pins (toℕ≤pred[n] x))) x=0 )
     ≡⟨ pcong-pF (shrink-cong (passoc (pprep (FL→perm fl)) (pins ( toℕ≤pred[n] x )) (flip (pins (toℕ≤pred[n] x))) )  x=0 x=0) ⟩
        perm→FL (shrink (pprep (FL→perm fl)  ∘ₚ (pins ( toℕ≤pred[n] x ) ∘ₚ flip (pins (toℕ≤pred[n] x)))) x=0 )
     ≡⟨ pcong-pF (shrink-cong {n} {pprep (FL→perm fl)  ∘ₚ (pins ( toℕ≤pred[n] x ) ∘ₚ flip (pins (toℕ≤pred[n] x)))} {pprep (FL→perm fl)  ∘ₚ pid}
             ( presp {suc n} {pprep (FL→perm fl) }  {_} {(pins ( toℕ≤pred[n] x ) ∘ₚ flip (pins (toℕ≤pred[n] x)))} {pid} prefl
             record { peq = λ q → inverseˡ (pins ( toℕ≤pred[n] x )) } )  x=0 x=0') ⟩
        perm→FL (shrink (pprep (FL→perm fl)  ∘ₚ pid) x=0' )
     ≡⟨ pcong-pF (shrink-cong {n} {pprep (FL→perm fl)  ∘ₚ pid} {pprep (FL→perm fl)} record {peq = λ q → refl }  x=0' x=0') ⟩ -- prefl won't work
        perm→FL (shrink (pprep (FL→perm fl)) x=0' )
     ≡⟨ pcong-pF shrink-iso ⟩
        perm→FL ( FL→perm fl ) 
     ≡⟨ FL→iso fl  ⟩
        fl 
     ∎ 

pcong-Fp : {n : ℕ }  → {x y : FL n}  → x ≡ y → FL→perm x =p= FL→perm y
pcong-Fp {n} {x} {x} refl = prefl

FL←iso : {n : ℕ }  → (perm : Permutation n n )  → FL→perm ( perm→FL perm  ) =p= perm
FL←iso {0} perm = record { peq = λ () }
FL←iso {suc n} perm = record { peq = λ q → ( begin
        FL→perm ( perm→FL perm  ) ⟨$⟩ʳ q
     ≡⟨⟩
        (pprep (FL→perm (perm→FL (shrink (perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))) (p=0 perm) )))  ∘ₚ pins ( toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0)) ) ) ⟨$⟩ʳ q
     ≡⟨  peq (presp {suc n} {_} {_} {pins ( toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0)))} (pprep-cong {n} {FL→perm (perm→FL (shrink (perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))) (p=0 perm) ))} (FL←iso _ ) ) prefl ) q  ⟩
         (pprep (shrink (perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))) (p=0 perm))   ∘ₚ pins ( toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0)) ))  ⟨$⟩ʳ q 
     ≡⟨ peq (presp {suc n} {pprep (shrink (perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))) (p=0 perm))} {perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))} {pins ( toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0)) )} (shrink-iso2 (p=0 perm)) prefl) q  ⟩
         ((perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))) ∘ₚ pins ( toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0)) ))  ⟨$⟩ʳ q 
     ≡⟨ peq (presp {suc n} {perm} {_} {flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0)))) ∘ₚ pins ( toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0)))} {pid} prefl record { peq = λ q → inverseʳ (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0)))) }) q  ⟩
        ( perm ∘ₚ pid ) ⟨$⟩ʳ q
     ≡⟨⟩
        perm ⟨$⟩ʳ q
     ∎  ) } 

FL-inject : {n : ℕ }  → {g h : Permutation n n }  → perm→FL g ≡  perm→FL h → g =p= h
FL-inject {n} {g} {h} g=h = record { peq = λ q → ( begin
       g ⟨$⟩ʳ q
     ≡⟨ peq (psym (FL←iso g )) q ⟩
        (  FL→perm (perm→FL g) ) ⟨$⟩ʳ q
     ≡⟨ cong ( λ k → FL→perm  k ⟨$⟩ʳ q  ) g=h  ⟩
        (  FL→perm (perm→FL h) ) ⟨$⟩ʳ q
     ≡⟨ peq (FL←iso h) q ⟩
        h ⟨$⟩ʳ q
     ∎  ) }

FLpid :  {n : ℕ} → (x : Permutation n n) → perm→FL x ≡ FL0 → FL→perm FL0 =p= pid   → x =p= pid
FLpid x eq p0id = ptrans pf2 (ptrans pf0 p0id ) where
   pf2 : x =p= FL→perm (perm→FL x)
   pf2 = psym (FL←iso x)
   pf0 : FL→perm (perm→FL x) =p= FL→perm FL0
   pf0 = pcong-Fp eq

pFL0 : {n : ℕ } → FL0 {n} ≡ perm→FL pid
pFL0 {zero} = refl
pFL0 {suc n} = cong (λ k → zero :: k ) pFL0
