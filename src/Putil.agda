{-# OPTIONS --cubical-compatible --safe #-}
module Putil where

open import Level hiding ( suc ; zero )
open import Algebra
open import Algebra.Structures
open import Data.Fin hiding ( _<_  ; _≤_ ; _-_ ; _+_ ; _≟_)
open import Data.Fin.Properties as DFP hiding ( <-trans ; ≤-trans ; ≤-irrelevant ; _≟_ ) renaming ( <-cmp to <-fcmp )
open import Data.Fin.Permutation
open import Function hiding (id ; flip)
-- open import Function.Inverse as Inverse using (_↔_; Inverse; _InverseOf_)
-- open import Function.LeftInverse  using ( _LeftInverseOf_ )
open import Function.Bundles -- using (Π)
open import Data.Nat -- using (ℕ; suc; zero; s≤s ; z≤n )
open import Data.Nat.Properties -- using (<-trans)
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.List using (List; []; _∷_ ; length ; _++_ ; head ; tail ) renaming (reverse to rev )
open import nat
open import Symmetric
open import Relation.Nullary hiding (⌊_⌋)
open import Data.Empty
open import  Relation.Binary.Core
open import  Relation.Binary.Definitions -- hiding (⌊_⌋)
open import fin

-- An inductive construction of permutation

pprep  : {n : ℕ }  → Permutation n n → Permutation (suc n) (suc n)
pprep {n} perm =  permutation p→ p← piso←  piso→ where
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
pswap {n} perm = permutation p→ p← piso←  piso→ where
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
   pfill1 (suc i) i<n perm = pfill1 i (<to≤ i<n) (subst (λ k → Permutation k k ) (si-sn=i-n i<n ) ( pprep perm ) )

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

-- open import Relation.Binary.HeterogeneousEquality as HE using (_≅_ )
-- open ≡-Reasoning

pins  : {n m : ℕ} → m ≤ n → Permutation (suc n) (suc n)
pins {_} {zero} _ = pid
pins {suc n} {suc m} (s≤s  m≤n) = permutation p← p→ piso→   piso← where

   next : Fin (suc (suc n)) → Fin (suc (suc n))
   next zero = suc zero
   next (suc x) = fromℕ< (≤-trans (fin<n {_} x ) a≤sa )

   p→ : Fin (suc (suc n)) → Fin (suc (suc n)) 
   p→ x with <-cmp (toℕ x) (suc m)
   ... | tri< a ¬b ¬c = fromℕ< (≤-trans (s≤s  a) (s≤s (s≤s  m≤n) )) 
   ... | tri≈ ¬a b ¬c = zero
   ... | tri> ¬a ¬b c = x

   p← : Fin (suc (suc n)) → Fin (suc (suc n)) 
   p← zero = fromℕ< (s≤s (s≤s m≤n))
   p← (suc x) with <-cmp (toℕ x) (suc m)
   ... | tri< a ¬b ¬c = fromℕ< (≤-trans (fin<n {_} x) a≤sa )
   ... | tri≈ ¬a b ¬c = suc x
   ... | tri> ¬a ¬b c = suc x

   mm : toℕ (fromℕ< {suc m} {suc (suc n)} (s≤s (s≤s m≤n))) ≡ suc m 
   mm = toℕ-fromℕ< (s≤s (s≤s  m≤n)) 

   mma : (x : Fin (suc n) ) → suc (toℕ x) ≤ suc m → toℕ ( fromℕ< (≤-trans (fin<n {_} x) a≤sa ) ) ≤ m
   mma x (s≤s x<sm) = subst (λ k → k ≤ m) (sym (toℕ-fromℕ< (≤-trans (fin<n _ ) a≤sa ) )) x<sm
   
   p3 : (x : Fin (suc n) ) →  toℕ (fromℕ< (≤-trans (fin<n {_} (suc x) ) (s≤s a≤sa))) ≡ suc (toℕ x)
   p3 x = begin
            toℕ (fromℕ< (≤-trans (fin<n {_} (suc x) ) (s≤s a≤sa)))
          ≡⟨ toℕ-fromℕ< ( s≤s ( ≤-trans (fin<n _) a≤sa ) ) ⟩
            suc (toℕ x)
          ∎ where open ≡-Reasoning

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
              ∎ where open ≡-Reasoning
          p15 : p← (suc y) ≡ suc x
          p15 with <-cmp (toℕ y) (suc m) -- eq : suc y ≡ suc (suc (fromℕ< (≤-pred (≤-trans a (s≤s m≤n))))) ,  a : suc x < suc m
          ... | tri< a₁ ¬b ¬c = p11 where
            p11 : fromℕ< (≤-trans (fin<n {_} y) a≤sa ) ≡ suc x
            p11 = begin
               fromℕ< (≤-trans (fin<n {_} y) a≤sa )
              ≡⟨ fromℕ<-cong  _ _ p12 _  (s≤s (fin<n {suc n} x )) ⟩ -- lemma10 {suc (suc n)} p12 (≤-trans (fin<n {_} y) a≤sa) (s≤s (fin<n {suc n} x ))  ⟩
               suc (fromℕ< (fin<n {suc n} x )) 
              ≡⟨ cong suc (fromℕ<-toℕ x _ ) ⟩
               suc x
              ∎ where open ≡-Reasoning
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
   piso← (suc x) | tri< a ¬b ¬c with <-cmp (toℕ ( fromℕ< (≤-trans (fin<n {_} x) a≤sa ) )) (suc m)
   ... | tri≈ ¬a b ¬c₁ = ⊥-elim ( ¬a (s≤s (mma x a)))
   ... | tri> ¬a ¬b₁ c = ⊥-elim ( ¬a (s≤s (mma x a)))
   ... | tri< a₁ ¬b₁ ¬c₁ = p0 where
       p2 : suc (suc (toℕ x)) ≤ suc (suc n)
       p2 = s≤s (fin<n {suc n} x)
       p6 : suc (toℕ (fromℕ< (≤-trans (fin<n {_} (suc x)) (s≤s a≤sa)))) ≤ suc (suc n)
       p6 = s≤s (≤-trans a₁ (s≤s m≤n))
       p0 : fromℕ< (≤-trans (s≤s  a₁) (s≤s (s≤s  m≤n) ))  ≡ suc x
       p0 = begin
             fromℕ< (≤-trans (s≤s  a₁) (s≤s (s≤s  m≤n) ))
          ≡⟨⟩
             fromℕ< (s≤s (≤-trans a₁ (s≤s m≤n))) 
          ≡⟨ lemma10 {suc (suc n)} (p3 x) p6 p2 ⟩
             fromℕ< ( s≤s (fin<n {suc n} x) )
          ≡⟨⟩
             suc (fromℕ< (fin<n {suc n} x )) 
          ≡⟨ cong suc (fromℕ<-toℕ x _ ) ⟩
             suc x
          ∎ where open ≡-Reasoning

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

pred-fin : {n : ℕ } → (y : Fin (suc n)) → 0 < toℕ y → (y<n : Data.Nat.pred (toℕ y) < n) → suc (fromℕ< y<n) ≡ y 
pred-fin {.(suc _)} zero () (s≤s z≤n)
pred-fin {suc n} (suc zero) 0<y (s≤s z≤n) = refl
pred-fin {suc n} (suc (suc y)) 0<y y<n = p13 where
  p14 : toℕ (suc y) < suc n
  p14 = y<n
  sy<n : Data.Nat.pred (toℕ (suc y)) < n
  sy<n = px≤py ( begin 
     suc (suc (toℕ y))  ≡⟨ refl ⟩
     suc (toℕ (suc y))  ≤⟨ p14 ⟩
     suc n  ∎ ) where open ≤-Reasoning 
  p12 : suc (fromℕ< sy<n ) ≡ suc y 
  p12 = pred-fin (suc y) (s≤s z≤n) sy<n
  p16 : fromℕ< y<n ≡ suc (fromℕ< sy<n)
  p16 = lemma10 refl y<n (s≤s sy<n)
  p13 : suc (fromℕ< y<n) ≡ suc (suc y)
  p13 = cong suc (trans p16 p12  )

----
--  find insertion point of pins
----

p011 : (n m : ℕ) → (perm : Permutation (suc n) (suc n) ) → (m≤n : m ≤ n) → 0 < m → (perm ∘ₚ flip (pins m≤n )) ⟨$⟩ˡ (# 0) ≡ perm ⟨$⟩ˡ (fromℕ< (s≤s m≤n))
p011 zero zero perm z≤n _ = refl
p011 zero (suc t) perm () _
p011 (suc n) (suc m) perm (s≤s m≤n) _ with <-cmp (toℕ {suc (suc n)} (# 0)) (suc m)
... | tri< a ¬b ¬c = refl
... | tri≈ ¬a () ¬c
... | tri> ¬a ¬b ()
p011 (suc n) zero perm m≤n ()

p=0 : {n : ℕ }  → (perm : Permutation (suc n) (suc n) ) → ((perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))) ⟨$⟩ˡ (# 0)) ≡ # 0
p=0 {zero} perm with ((perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))) ⟨$⟩ˡ (# 0)) 
... | zero = refl
p=0 {suc n} perm with Inverse.to perm zero in eq
... | zero = p002 where
    p002 : Inverse.from perm (Inverse.to (pins (toℕ≤pred[n] zero)) zero) ≡ zero
    p002 = subst (λ k → perm ⟨$⟩ˡ k ≡ zero ) eq (inverseˡ perm)
... | suc t = p012 where
    p003 : 0 < toℕ (Inverse.to perm zero)
    p003 = subst ( λ k → 0 < k ) (cong toℕ (sym eq)) (s≤s z≤n)
    p008 : toℕ (Data.Fin.pred (Inverse.to perm zero)) ≡ toℕ (Inverse.to perm zero) ∸ 1
    p008 = fpred-comm (Inverse.to perm zero)
    p002 : toℕ (Inverse.to perm zero) ≤ suc n
    p002 = toℕ≤pred[n] (Inverse.to perm zero)
    p007 : Data.Nat.pred (toℕ (Inverse.to perm zero)) < suc n
    p007 = subst (λ k → k < suc n ) p008 (<-≤-trans (pred< _ (λ ne → DFP.<⇒≢ p003 (sym ne))) p002)
    p012 : Inverse.from perm (Inverse.to (pins (toℕ≤pred[n] (suc t))) zero) ≡ # 0 
    p012 = begin
        Inverse.from perm (Inverse.to (pins (toℕ≤pred[n] (suc t))) zero) ≡⟨ p011 _ _ perm (toℕ≤pred[n] (suc t)) (s≤s z≤n) ⟩
        perm ⟨$⟩ˡ suc (fromℕ< (s≤s (toℕ≤pred[n] t))) ≡⟨ cong (λ k → perm ⟨$⟩ˡ k ) (fromℕ<-cong _ _  (
           begin
           suc (toℕ t) ≡⟨ refl ⟩
           suc (toℕ (suc t) ∸ 1) ≡⟨ cong (λ k → suc (toℕ k ∸ 1) ) (sym eq) ⟩
           suc (toℕ (Inverse.to perm zero) ∸ 1) ∎ ) (s≤s (fin<n _) ) (subst (λ k → k < 2+ n) p013 (s≤s (fin<n _)))) ⟩
        perm ⟨$⟩ˡ suc (fromℕ< p007) ≡⟨ cong (λ k → perm ⟨$⟩ˡ k ) (pred-fin (Inverse.to perm zero) p003 p007 ) ⟩
        perm ⟨$⟩ˡ (Inverse.to perm zero) ≡⟨ inverseˡ perm  ⟩
        # 0 ∎ where 
            open ≡-Reasoning
            p013 : suc (toℕ t) ≡ suc (toℕ (Inverse.to perm zero) ∸ 1)
            p013 = begin
                suc (toℕ t) ≡⟨ refl ⟩ 
                toℕ (suc t) ≡⟨ cong toℕ (sym eq) ⟩ 
                toℕ (Inverse.to perm zero) ≡⟨ sym (sucprd p003) ⟩ 
                suc (toℕ (Inverse.to perm zero) ∸ 1) ∎

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
pleq  {suc n} x y eq = record { peq = λ q → pleq1 n a<sa eq q (fin<n _) } where
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
       ∎ where open ≡-Reasoning 
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
          open ≡-Reasoning 
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

ℕL-inject : {h h1 : ℕ } {x y : List ℕ } → h ∷ x ≡ h1 ∷ y → h ≡ h1
ℕL-inject refl = refl

ℕL-inject-t : {h h1 : ℕ } {x y : List ℕ } → h ∷ x ≡ h1 ∷ y → x ≡ y
ℕL-inject-t refl = refl
                    
ℕL-eq? : (x y : List ℕ ) → Dec (x ≡ y )  
ℕL-eq? [] [] = yes refl                             
ℕL-eq? [] (x ∷ y) = no (λ ())          
ℕL-eq? (x ∷ x₁) [] = no (λ ())                 
ℕL-eq? (h ∷ x) (h1 ∷ y) with h ≟ h1 | ℕL-eq? x y                               
... | yes y1 | yes y2 = yes ( cong₂ (λ j k → j ∷ k ) y1 y2 )              
... | yes y1 | no n = no (λ e → n (ℕL-inject-t e))                          
... | no n  | t = no (λ e → n (ℕL-inject e))                              

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
        ∎  where
          open ≡-Reasoning 

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
        ∎  where
          open ≡-Reasoning 
 
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
       ∎ where
          open ≡-Reasoning 

shlem← : {n  : ℕ} → (perm : Permutation (suc n) (suc n) ) → (p0=0 : perm ⟨$⟩ˡ (# 0) ≡ # 0 ) → (x : Fin (suc n)) → perm ⟨$⟩ʳ x ≡ zero → x ≡ zero
shlem← perm p0=0 x px=0 =  begin
          x                                  ≡⟨ sym (inverseˡ perm ) ⟩
          perm ⟨$⟩ˡ ( perm ⟨$⟩ʳ x )          ≡⟨ cong (λ k →  perm ⟨$⟩ˡ k ) px=0 ⟩
          perm ⟨$⟩ˡ zero                     ≡⟨ p0=0  ⟩
          zero
       ∎ where
          open ≡-Reasoning 

sh2 : {n  : ℕ} → (perm : Permutation (suc n) (suc n) ) → (p0=0 : perm ⟨$⟩ˡ (# 0) ≡ # 0 ) → {x : Fin n} → ¬ perm ⟨$⟩ˡ (suc x) ≡ zero
sh2 perm p0=0 {x} eq with shlem→ perm p0=0 (suc x) eq
sh2 perm p0=0 {x} eq | ()

sh1 : {n  : ℕ} → (perm : Permutation (suc n) (suc n) ) → (p0=0 : perm ⟨$⟩ˡ (# 0) ≡ # 0 ) → {x : Fin n} → ¬ perm ⟨$⟩ʳ (suc x) ≡ zero
sh1 perm p0=0 {x} eq with shlem← perm p0=0 (suc x) eq
sh1 perm p0=0 {x} eq | ()

0<x→px<n : {n  : ℕ} → (x : Fin n) → (c :  0 < toℕ x ) 
     → Data.Nat.pred (toℕ x) < n
0<x→px<n {n} x c = sx≤py→x≤y ( begin
     suc (suc (Data.Nat.pred (toℕ x))) ≡⟨ cong suc (sucprd c) ⟩
     suc (toℕ x) <⟨ fin<n _  ⟩
     suc n ∎ ) where
        open Data.Nat.Properties.≤-Reasoning

sh1p<n : {n : ℕ } → (perm : Permutation (suc n) (suc n) ) → (x : Fin n) → (c :  0 < toℕ (perm ⟨$⟩ʳ (suc x) ) ) 
       → Data.Nat.pred (toℕ (Inverse.to perm (suc x))) < n
sh1p<n {n} perm x c = sx≤py→x≤y ( begin
     suc (suc (Data.Nat.pred (toℕ (Inverse.to perm (suc x))))) ≡⟨ cong suc (sucprd c) ⟩
     suc (toℕ (Inverse.to perm (suc x))) ≤⟨ fin<n _ ⟩
     suc n ∎ ) where
        open Data.Nat.Properties.≤-Reasoning

sh2p<n : {n : ℕ } → (perm : Permutation (suc n) (suc n) ) → (x : Fin n) → (c :  0 < toℕ (perm ⟨$⟩ˡ (suc x) ) ) 
       → Data.Nat.pred (toℕ (Inverse.from perm (suc x))) < n
sh2p<n {n} perm x c = sx≤py→x≤y ( begin
     suc (suc (Data.Nat.pred (toℕ (Inverse.from perm (suc x))))) ≡⟨ cong suc (sucprd c) ⟩
     suc (toℕ (Inverse.from perm (suc x))) ≤⟨ fin<n  _ ⟩
     suc n ∎ ) where
        open Data.Nat.Properties.≤-Reasoning

-- 0 ∷ 1 ∷ 2 ∷ 3 ∷ [] → 0 ∷ 1 ∷ 2 ∷ [] 
shrink : {n  : ℕ} → (perm : Permutation (suc n) (suc n) ) → perm ⟨$⟩ˡ (# 0) ≡ # 0 → Permutation n n
shrink {n} perm p0=0  = permutation p→ p← piso← piso→  where

   p→ : Fin n → Fin n 
   p→ x with <-fcmp (perm ⟨$⟩ʳ (suc x) ) (# 0)
   p→ x | tri≈ ¬a b ¬c = ⊥-elim (sh1 perm p0=0 b)
   p→ x | tri> ¬a ¬b c = fromℕ< {Data.Nat.pred (toℕ (Inverse.to perm (suc x)))} (sh1p<n perm  x c) 

   p← : Fin n → Fin n 
   p← x with <-fcmp (perm ⟨$⟩ˡ (suc x)) (# 0)
   p← x | tri≈ ¬a b ¬c = ⊥-elim (sh2 perm p0=0 b)
   p← x | tri> ¬a ¬b c = fromℕ< {Data.Nat.pred (toℕ (Inverse.from perm (suc x)))} (sh2p<n perm x c)

   --  using "with" something binded in ≡ is prohibited
   --  with perm ⟨$⟩ʳ (suc q) in e generates w != Inverse.to perm (suc q) of type Fin (suc n)  error
   piso← : (x : Fin n ) → p→ ( p← x ) ≡ x
   piso← x = p02 _ _ refl refl  where
      p02 : (y z : Fin n) → p← x ≡ y → p→ y ≡ z → z ≡ x
      p02 y z px=y py=z with <-fcmp (perm ⟨$⟩ˡ (suc x)) (# 0) 
      ... | tri≈ ¬a b ¬c = ⊥-elim (sh2 perm p0=0 b)
      ... | tri> ¬a ¬b c with <-fcmp (perm ⟨$⟩ʳ (suc y)) (# 0) 
      ... | tri≈ ¬a₁ b ¬c = ⊥-elim (sh1 perm p0=0 b)
      ... | tri> ¬a₁ ¬b₁ c₁ = p08 where
           open ≡-Reasoning 
           p15 : toℕ (Inverse.to perm (suc y)) ∸ 1 ≡ toℕ x
           p15 = begin
              toℕ (Inverse.to perm (suc y)) ∸ 1  ≡⟨ cong (λ k → toℕ (Inverse.to perm (suc k))  ∸ 1   ) (sym px=y) ⟩
              toℕ (Inverse.to perm (suc (fromℕ< (sh2p<n perm x c)))) ∸ 1  ≡⟨ cong (λ k → toℕ (Inverse.to perm k)  ∸ 1) (pred-fin _ c (sh2p<n perm x c) ) ⟩
              toℕ (Inverse.to perm (Inverse.from perm (suc x))) ∸ 1  ≡⟨ cong (λ k → toℕ k  ∸ 1) (inverseʳ perm) ⟩
              toℕ (suc x) ∸ 1  ≡⟨ refl ⟩
              toℕ x ∎
           p08 : z ≡ x
           p08 = begin
             z ≡⟨ sym (py=z) ⟩
             fromℕ< {Data.Nat.pred (toℕ (Inverse.to perm (suc y)))} (sh1p<n perm  y c₁)  ≡⟨ lemma10 p15 (subst (λ k → k < n) (sym p15) (fin<n _)) (fin<n _) ⟩
             fromℕ< {toℕ x} (fin<n _)  ≡⟨ fromℕ<-toℕ _ _  ⟩
             x ∎  

   piso→ : (x : Fin n ) → p← ( p→ x ) ≡ x
   piso→ x = p02 _ _ refl refl  where
      p02 : (y z : Fin n) → p→  x ≡ y → p← y ≡ z → z ≡ x
      p02 y z px=y py=z with <-fcmp (perm ⟨$⟩ʳ (suc x)) (# 0) 
      ... | tri≈ ¬a b ¬c = ⊥-elim (sh1 perm p0=0 b)
      ... | tri> ¬a ¬b c with <-fcmp (perm ⟨$⟩ˡ (suc y)) (# 0) 
      ... | tri≈ ¬a₁ b ¬c = ⊥-elim (sh2 perm p0=0 b)
      ... | tri> ¬a₁ ¬b₁ c₁ = p08 where
           open ≡-Reasoning 
           p15 : toℕ (Inverse.from perm (suc y)) ∸ 1 ≡ toℕ x
           p15 = begin
              toℕ (Inverse.from perm (suc y)) ∸ 1  ≡⟨ cong (λ k → toℕ (Inverse.from perm (suc k))  ∸ 1   ) (sym px=y) ⟩
              toℕ (Inverse.from perm (suc (fromℕ< (sh1p<n perm  x c)))) ∸ 1  ≡⟨ cong (λ k → toℕ (Inverse.from perm k)  ∸ 1) (pred-fin _ c (sh1p<n perm  x c) ) ⟩
              toℕ (Inverse.from perm (Inverse.to perm (suc x))) ∸ 1  ≡⟨ cong (λ k → toℕ k  ∸ 1) (inverseˡ perm) ⟩
              toℕ (suc x) ∸ 1  ≡⟨ refl ⟩
              toℕ x ∎
           p08 : z ≡ x
           p08 = begin
             z ≡⟨ sym (py=z) ⟩
             fromℕ< {Data.Nat.pred (toℕ (Inverse.from perm (suc y)))} (sh2p<n perm y c₁)  ≡⟨ lemma10 p15 (subst (λ k → k < n) (sym p15) (fin<n _)) (fin<n _) ⟩
             fromℕ< {toℕ x} (fin<n _)  ≡⟨ fromℕ<-toℕ _ _  ⟩
             x ∎  

shrink-iso : { n : ℕ } → {perm : Permutation n n} → shrink (pprep perm)  refl =p=  perm
shrink-iso {n} {perm} = record { peq = λ q → s001 q } where
    s001 : (x : Fin n) → shrink (pprep perm) refl ⟨$⟩ʳ x ≡ perm ⟨$⟩ʳ x
    s001 zero with <-fcmp (suc (perm ⟨$⟩ʳ zero)) (# 0) 
    ... | tri> ¬a ¬b c = s002 where
        s002 :  fromℕ< (≤-trans (fin<n _) (s≤s (Data.Nat.Properties.≤-reflexive refl))) ≡ perm ⟨$⟩ʳ zero
        s002 = begin
            fromℕ< (≤-trans (fin<n _) (s≤s (Data.Nat.Properties.≤-reflexive refl))) ≡⟨ lemma10 refl (≤-trans (fin<n _) (s≤s (Data.Nat.Properties.≤-reflexive refl))) (fin<n _) ⟩ 
            fromℕ< (fin<n  _) ≡⟨ fromℕ<-toℕ (perm ⟨$⟩ʳ zero) (fin<n _) ⟩ 
            perm ⟨$⟩ʳ zero ∎ where open ≡-Reasoning
    s001 (suc x) with <-fcmp (suc (perm ⟨$⟩ʳ (suc x))) (# 0) 
    ... | tri> ¬a ¬b c = s002 where
        s002 :  fromℕ< (≤-trans (fin<n _) (s≤s (Data.Nat.Properties.≤-reflexive refl))) ≡ perm ⟨$⟩ʳ (suc x)
        s002 = begin
            fromℕ< (≤-trans (fin<n _) (s≤s (Data.Nat.Properties.≤-reflexive refl))) ≡⟨ lemma10 refl (≤-trans (fin<n _) (s≤s (Data.Nat.Properties.≤-reflexive refl))) (fin<n _) ⟩ 
            fromℕ< (fin<n _) ≡⟨ fromℕ<-toℕ (perm ⟨$⟩ʳ (suc x)) (fin<n _) ⟩ 
            perm ⟨$⟩ʳ (suc x) ∎ where open ≡-Reasoning

shrink-iso2 : { n : ℕ } → {perm : Permutation (suc n) (suc n)} 
   → (p=0 : perm ⟨$⟩ˡ (# 0) ≡ # 0)  → pprep (shrink perm p=0) =p= perm
shrink-iso2 {n} {perm} p=0 = record { peq =  s001 } where
    s001 : (q : Fin (suc n)) → (pprep (shrink perm p=0) ⟨$⟩ʳ q) ≡ perm ⟨$⟩ʳ q
    s001 zero = begin
         zero ≡⟨ sym ( inverseʳ perm ) ⟩
         perm ⟨$⟩ʳ ( perm ⟨$⟩ˡ zero ) ≡⟨ cong (λ k → perm ⟨$⟩ʳ k ) p=0 ⟩
         perm ⟨$⟩ʳ zero ∎ where open ≡-Reasoning 
    s001 (suc q) with <-fcmp ((perm ⟨$⟩ʳ (suc q))) (# 0) 
    ... | tri> ¬a ¬b c = begin
         suc (fromℕ< (sh1p<n perm q c)) ≡⟨ pred-fin (perm ⟨$⟩ʳ suc q) c (sh1p<n perm q c)  ⟩
         perm ⟨$⟩ʳ (suc q) ∎ where open ≡-Reasoning 
    ... | tri≈ ¬a b ¬c = ⊥-elim (sh1 perm p=0 b)


shrink-cong : { n : ℕ } → {x y : Permutation (suc n) (suc n)}
    → x =p= y
    → (x=0 :  x ⟨$⟩ˡ (# 0) ≡ # 0 ) → (y=0 : y ⟨$⟩ˡ (# 0) ≡ # 0 )  → shrink x x=0 =p=  shrink y y=0 
shrink-cong {n} {x} {y} x=y x=0 y=0  = record  { peq = p002 } where
    p002 : (q : Fin n) → (shrink x x=0 ⟨$⟩ʳ q) ≡ (shrink y y=0 ⟨$⟩ʳ q)
    p002 q with  <-fcmp (x ⟨$⟩ʳ (suc q) ) (# 0) | <-fcmp (y ⟨$⟩ʳ (suc q) ) (# 0)
    ... | tri≈ ¬a b ¬c | _ = ⊥-elim ( sh1 x x=0 b )
    ... | _ | tri≈ ¬a₁ b ¬c = ⊥-elim ( sh1 y y=0 b )
    ... | tri> ¬a ¬b c | tri> ¬a' ¬b' c' = lemma10 (cong (λ k → toℕ k ∸ 1) (peq x=y _)) p004 p005 where
       p004 : toℕ (x ⟨$⟩ʳ suc q) ∸ 1 < n 
       p004 = sh1p<n x q c
       p005 : toℕ (y ⟨$⟩ʳ suc q) ∸ 1 < n 
       p005 = sh1p<n y q c'

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
     ∎ where
          open ≡-Reasoning 
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
     ∎ where
          open ≡-Reasoning 

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
      where open ≡-Reasoning 

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
      where open ≡-Reasoning 

FLpid :  {n : ℕ} → (x : Permutation n n) → perm→FL x ≡ FL0 → FL→perm FL0 =p= pid   → x =p= pid
FLpid x eq p0id = ptrans pf2 (ptrans pf0 p0id ) where
   pf2 : x =p= FL→perm (perm→FL x)
   pf2 = psym (FL←iso x)
   pf0 : FL→perm (perm→FL x) =p= FL→perm FL0
   pf0 = pcong-Fp eq

shrink-pid : {n : ℕ} → (shrink (pid ∘ₚ flip (pins (toℕ≤pred[n] {suc n} (pid ⟨$⟩ʳ # 0)))) (p=0 pid)) =p= pid
shrink-pid {zero}  = record { peq = λ () }
shrink-pid {suc n} = record { peq = pf5 } where
    pf5 :  (q : Fin (suc n)) → (shrink (pid ∘ₚ flip (pins (toℕ≤pred[n] {suc (suc n)} (pid ⟨$⟩ʳ # 0)))) (p=0 pid)) ⟨$⟩ʳ q ≡ pid ⟨$⟩ʳ q
    pf5 zero = refl
    pf5 (suc q) with <-fcmp ((pid ⟨$⟩ʳ (suc q))) (# 0) 
    ... | tri> ¬a ¬b c = pf6 where
      pf6 : suc (fromℕ< (≤-trans (fin<n {_} q) (Data.Nat.Properties.≤-reflexive refl))) ≡ suc q
      pf6 = cong suc ( begin
          fromℕ< (≤-trans (fin<n {_} q) (Data.Nat.Properties.≤-reflexive refl)) ≡⟨ lemma10 refl (≤-trans (fin<n {_} q) (Data.Nat.Properties.≤-reflexive refl)) (fin<n _)  ⟩ 
          fromℕ< (fin<n _) ≡⟨  fromℕ<-toℕ _ (fin<n  _) ⟩ 
          q ∎  ) where 
             open ≡-Reasoning 


pFL0 : {n : ℕ } → FL0 {n} ≡ perm→FL pid
pFL0 {zero} = refl
pFL0 {suc n} = cong (λ k → zero :: k ) (trans pFL0 (pcong-pF (psym shrink-pid) )) 
