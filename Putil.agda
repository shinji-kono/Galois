module Putil where

open import Level hiding ( suc ; zero )
open import Algebra
open import Algebra.Structures
open import Data.Fin hiding ( _<_  ; _≤_ ; _-_ ; _+_ )
open import Data.Fin.Properties hiding ( <-trans ; ≤-trans ) renaming ( <-cmp to <-fcmp )
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

open import Symmetric


open import Relation.Nullary
open import Data.Empty
open import  Relation.Binary.Core
open import fin

-- An inductive construction of permutation

-- Todo
--
--   complete perm→FL
--   describe property of pprep and pswap
--   describe property of pins    ( move 0 to any position)
--   describe property of shrink  ( remove one column )
--   prove FL→iso 
--   prove FL←iso 
--   prove FL enumerate all permutations

-- we already have refl and trans in the Symmetric Group

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

-- enumeration

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

-- pconcat :  {n m : ℕ } → Permutation  m m → Permutation n n → Permutation (m + n)  (m + n) 
-- pconcat {n} {m} p q = pfill {n + m} {m} ? p ∘ₚ ?

-- inductivley enmumerate permutations
--    from n-1 length create n length inserting new element at position m

-- 0 ∷ 1 ∷ 2 ∷ 3 ∷ [] 
-- 1 ∷ 0 ∷ 2 ∷ 3 ∷ []    plist ( pins {3} (n≤ 1) )
-- 1 ∷ 2 ∷ 0 ∷ 3 ∷ []
-- 1 ∷ 2 ∷ 3 ∷ 0 ∷ []

pins  : {n m : ℕ} → m ≤ n → Permutation (suc n) (suc n)
pins {_} {zero} _ = pid
pins {suc _} {suc zero} _ = pswap pid
pins {suc (suc n)} {suc m} (s≤s m<n) =  pins1 (suc m) (suc (suc n)) lem0 where
    pins1 : (i j : ℕ ) → j ≤ suc (suc n)  → Permutation (suc (suc (suc n ))) (suc (suc (suc n)))
    pins1 _ zero _ = pid
    pins1 zero _ _ = pid
    pins1 (suc i) (suc j) (s≤s si≤n) = psawpim {suc (suc (suc n))} {j}  (s≤s (s≤s si≤n))  ∘ₚ  pins1 i j (≤-trans si≤n refl-≤s ) 

plist  : {n  : ℕ} → Permutation n n → List ℕ
plist {0} perm = []
plist {suc j} perm = rev (plist1 j a<sa) where
    n = suc j
    plist1 : (i : ℕ ) → i < n → List ℕ
    plist1  zero _           = toℕ ( perm ⟨$⟩ˡ (fromℕ≤ {zero} (s≤s z≤n))) ∷ []
    plist1  (suc i) (s≤s lt) = toℕ ( perm ⟨$⟩ˡ (fromℕ≤ (s≤s lt)))         ∷ plist1  i (<-trans lt a<sa) 

data  FL : (n : ℕ )→ Set where
   f0 :  FL 0 
   _::_ :  { n : ℕ } → Fin (suc n ) → FL n → FL (suc n)

open import logic 

-- 0 ∷ 1 ∷ 2 ∷ 3 ∷ [] → 0 ∷ 1 ∷ 2 ∷ [] 
shrink : {n  : ℕ} → (perm : Permutation (suc n) (suc n) ) → perm ⟨$⟩ˡ (# 0) ≡ # 0 → Permutation n n
shrink {n} perm p0=0  = permutation p→ p← record { left-inverse-of = piso→ ; right-inverse-of = piso← } where
   shlem→ : (x : Fin (suc n) ) →  perm ⟨$⟩ˡ x ≡ zero → x ≡ zero
   shlem→ x px=0 = begin
          x                                  ≡⟨ sym ( inverseʳ perm ) ⟩
          perm ⟨$⟩ʳ ( perm ⟨$⟩ˡ x)           ≡⟨ cong (λ k →  perm ⟨$⟩ʳ k ) px=0 ⟩
          perm ⟨$⟩ʳ zero                     ≡⟨ cong (λ k →  perm ⟨$⟩ʳ k ) (sym p0=0) ⟩
          perm ⟨$⟩ʳ ( perm ⟨$⟩ˡ zero)        ≡⟨ inverseʳ perm  ⟩
          zero
       ∎ where open ≡-Reasoning

   shlem← : (x : Fin (suc n)) → perm ⟨$⟩ʳ x ≡ zero → x ≡ zero
   shlem← x px=0 =  begin
          x                                  ≡⟨ sym (inverseˡ perm ) ⟩
          perm ⟨$⟩ˡ ( perm ⟨$⟩ʳ x )          ≡⟨ cong (λ k →  perm ⟨$⟩ˡ k ) px=0 ⟩
          perm ⟨$⟩ˡ zero                     ≡⟨ p0=0  ⟩
          zero
       ∎ where open ≡-Reasoning

   sh2 : {x : Fin n} → ¬ perm ⟨$⟩ˡ (suc x) ≡ zero
   sh2 {x} eq with shlem→ (suc x) eq
   sh2 {x} eq | ()

   p→ : Fin n → Fin n 
   p→ x with perm ⟨$⟩ˡ (suc x) | inspect (_⟨$⟩ˡ_ perm ) (suc x) 
   p→ x | zero  | record { eq = e } = ⊥-elim ( sh2 {x} e )
   p→ x | suc t | _ = t

   sh1 : {x : Fin n} → ¬ perm ⟨$⟩ʳ (suc x) ≡ zero
   sh1 {x} eq with shlem← (suc x) eq
   sh1 {x} eq | ()

   p← : Fin n → Fin n 
   p← x with perm ⟨$⟩ʳ (suc x) | inspect (_⟨$⟩ʳ_ perm ) (suc x) 
   p← x | zero  | record { eq = e } = ⊥-elim ( sh1 {x} e )
   p← x | suc t | _ = t

   piso← : (x : Fin n ) → p→ ( p← x ) ≡ x
   piso← x with perm ⟨$⟩ʳ (suc x) | inspect (_⟨$⟩ʳ_ perm ) (suc x) 
   piso← x | zero  | record { eq = e } = ⊥-elim ( sh1 {x} e )
   piso← x | suc t | _ with perm ⟨$⟩ˡ (suc t) | inspect (_⟨$⟩ˡ_ perm ) (suc t)
   piso← x | suc t | _ | zero |  record { eq = e } =  ⊥-elim ( sh2 e )
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
               Inverse.from perm Π.⟨$⟩ suc t
            ≡⟨ cong (λ k →  Inverse.from perm Π.⟨$⟩ k ) (sym e0 ) ⟩
               Inverse.from perm Π.⟨$⟩ ( Inverse.to perm Π.⟨$⟩ suc x )
            ≡⟨ inverseˡ perm   ⟩
               suc x
            ∎ 

   piso→ : (x : Fin n ) → p← ( p→ x ) ≡ x
   piso→ x with perm ⟨$⟩ˡ (suc x) | inspect (_⟨$⟩ˡ_ perm ) (suc x)
   piso→ x | zero  | record { eq = e } = ⊥-elim ( sh2 {x} e )
   piso→ x | suc t | _ with perm ⟨$⟩ʳ (suc t) | inspect (_⟨$⟩ʳ_ perm ) (suc t)
   piso→ x | suc t | _ | zero |  record { eq = e } =  ⊥-elim ( sh1 e )
   piso→ x | suc t |  record { eq = e0 } | suc t1 |  record { eq = e1 } = begin
          t1
       ≡⟨ plem2 plem3 ⟩
          x
       ∎ where
          open ≡-Reasoning
          plem2 :  suc t1 ≡ suc x → t1 ≡ x
          plem2 refl = refl
          plem3 :  suc t1 ≡ suc x
          plem3 = begin
               suc t1
            ≡⟨ sym e1 ⟩
               Inverse.to perm Π.⟨$⟩ suc t
            ≡⟨ cong (λ k →  Inverse.to perm Π.⟨$⟩ k ) (sym e0 ) ⟩
               Inverse.to perm Π.⟨$⟩ ( Inverse.from perm Π.⟨$⟩ suc x )
            ≡⟨ inverseʳ perm   ⟩
               suc x
            ∎

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

-- postulate
--    p=0 : {n : ℕ }  → (perm : Permutation (suc n) (suc n) ) → ((perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))) ⟨$⟩ˡ (# 0)) ≡ # 0

perm→FL   : {n : ℕ }  → Permutation n n → FL n
perm→FL {zero} perm = f0
perm→FL {suc n} perm = (perm ⟨$⟩ʳ (# 0)) :: perm→FL (remove (# 0) perm)  
-- perm→FL {suc n} perm = (perm ⟨$⟩ʳ (# 0)) :: perm→FL (shrink (perm ∘ₚ flip (pins (toℕ≤pred[n] (perm ⟨$⟩ʳ (# 0))))) (p=0 perm) ) 

-- t5 = plist t4 ∷ plist ( t4  ∘ₚ flip (pins ( n≤  3 ) ))
t5 = plist (t4) ∷ plist (flip t4)
    ∷ ( toℕ (t4 ⟨$⟩ˡ fromℕ≤ a<sa) ∷ [] )
    ∷ ( toℕ (t4 ⟨$⟩ʳ (# 0)) ∷ [] )
    -- ∷  plist ( t4  ∘ₚ flip (pins ( n≤  1 ) ))
    ∷  plist (remove (# 0) t4  )
    ∷  plist ( FL→perm t40 )
    ∷ []
 
t6 = perm→FL t4

postulate
   FL→iso : {n : ℕ }  → (fl : FL n )  → perm→FL ( FL→perm fl ) ≡ fl
-- FL→iso f0 = refl
-- FL→iso (x :: fl) = {!!} -- with FL→iso fl
-- ... | t = {!!}

open _=p=_
postulate
   FL←iso : {n : ℕ }  → (perm : Permutation n n )  → FL→perm ( perm→FL perm  ) =p= perm
-- FL←iso {0} perm = record { peq = λ () }
-- FL←iso {suc n} perm = {!!}

lem2 : {i n : ℕ } → i ≤ n → i ≤ suc n
lem2 i≤n = ≤-trans i≤n ( refl-≤s )

∀-FL : (n : ℕ ) → List (FL (suc n))
∀-FL  x  = fls6 x  where
   fls4 :  ( i n : ℕ ) → (i<n : i ≤ n ) → FL  n → List (FL  (suc n))  → List (FL  (suc n)) 
   fls4 zero n i≤n perm x = (zero :: perm ) ∷ x
   fls4 (suc i) n i≤n  perm x = fls4 i n (≤-trans refl-≤s i≤n ) perm ((fromℕ≤ (s≤s i≤n) :: perm ) ∷ x)
   fls5 :  ( n : ℕ ) → List (FL n) → List (FL  (suc n))  → List (FL (suc n)) 
   fls5 n [] x = x
   fls5 n (h ∷ x) y = fls5  n x (fls4 n n lem0 h y)
   fls6 :  ( n : ℕ ) → List (FL  (suc n)) 
   fls6 zero = (zero :: f0) ∷ []
   fls6 (suc n) =  fls5 (suc n) (fls6 n) []   

all-perm : (n : ℕ ) → List (Permutation (suc n) (suc n) )
all-perm n = pls6 n where
   lem1 : {i n : ℕ } → i ≤ n → i < suc n
   lem1 z≤n = s≤s z≤n
   lem1 (s≤s lt) = s≤s (lem1 lt)
   pls4 :  ( i n : ℕ ) → (i<n : i ≤ n ) → Permutation n n → List (Permutation (suc n) (suc n))  → List (Permutation (suc n) (suc n)) 
   pls4 zero n i≤n perm x = (pprep perm ∘ₚ pins i≤n ) ∷ x
   pls4 (suc i) n i≤n  perm x = pls4 i n (≤-trans refl-≤s i≤n ) perm (pprep perm ∘ₚ pins {n} {suc i} i≤n  ∷ x)
   pls5 :  ( n : ℕ ) → List (Permutation n n) → List (Permutation (suc n) (suc n))  → List (Permutation (suc n) (suc n)) 
   pls5 n [] x = x
   pls5 n (h ∷ x) y = pls5  n x (pls4 n n lem0 h y)
   pls6 :  ( n : ℕ ) → List (Permutation (suc n) (suc n)) 
   pls6 zero = pid ∷ []
   pls6 (suc n) =  pls5 (suc n) (rev (pls6 n) ) []   -- rev to put id first

pls : (n : ℕ ) → List (List ℕ )
pls n = Data.List.map plist (all-perm n) where
