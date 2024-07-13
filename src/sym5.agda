{-# OPTIONS --cubical-compatible  --safe #-}

open import Level hiding ( suc ; zero )
open import Algebra
module sym5 where

open import Symmetric 
open import Data.Unit using (⊤ ; tt )
open import Function.Bundles -- as Inverse using (_↔_; Inverse; _InverseOf_)
open import Function hiding (flip)
open import Data.Nat hiding (_⊔_) -- using (ℕ; suc; zero)
open import Data.Nat.Properties
open import Relation.Nullary
open import Data.Empty
open import Data.Product

open import Gutil 
open import Putil 
open import Solvable using (solvable)
open import  Relation.Binary.PropositionalEquality hiding ( [_] )

open import Data.Fin hiding (_<_ ; _≤_  ; lift )
open import Data.Fin.Permutation  hiding (_∘ₚ_)

infixr  200 _∘ₚ_
_∘ₚ_ = Data.Fin.Permutation._∘ₚ_

open import Data.List  hiding ( [_] )
open import nat
open import fin
open import logic

open _∧_

¬sym5solvable : ¬ ( solvable (Symmetric 5) )
¬sym5solvable sol = counter-example (end5 (abc 0<3 0<4 ) (dervie-any-3rot0 (dervied-length sol) 0<3 0<4 ) ) where
--
--    dba       1320      d → b → a → d
--    (dba)⁻¹   3021      a → b → d → a
--    aec       21430
--    (aec)⁻¹   41032
--    [ dba , aec ] = (abd)(cea)(dba)(aec) = abc
--      so commutator always contains abc, dba and aec

     open ≡-Reasoning

     open solvable
     open Solvable ( Symmetric 5) 
     end5 : (x : Permutation 5 5) → deriving (dervied-length sol) x →  x =p= pid  
     end5 x der = end sol x der

     0<4 : 0 < 4
     0<4 = s≤s z≤n

     0<3 : 0 < 3
     0<3 = s≤s z≤n

     --- 1 ∷ 2 ∷ 0 ∷ []      abc
     3rot : Permutation 3 3
     3rot = pid {3} ∘ₚ pins (n≤ 2)

     save2 : {i j : ℕ }  → (i ≤ 3 ) → ( j ≤ 4 ) →  Permutation  5 5 
     save2 i<3 j<4 = flip (pins (s≤s i<3)) ∘ₚ flip (pins j<4) 

     ins2 : {i j : ℕ }  → Permutation 3 3  → (i ≤ 3 ) → ( j ≤ 4 ) → Permutation  5 5
     ins2 abc i<3 j<4 = (save2 i<3 j<4 ∘ₚ (pprep (pprep abc))) ∘ₚ flip (save2 i<3 j<4 ) 

     ins2cong : {i j : ℕ }  → {x y : Permutation 3 3 } → {i<3 : i ≤ 3 } → {j<4 : j ≤ 4 } → x =p= y → ins2 x i<3 j<4  =p= ins2 y i<3 j<4
     ins2cong {i} {j} {x} {y} {i<3} {j<4} x=y = presp {5} {save2 i<3 j<4 ∘ₚ (pprep (pprep x))} {_} {flip (save2 i<3 j<4 )}
         (presp {5} {save2 i<3 j<4} prefl (pprep-cong (pprep-cong x=y)) ) prefl 

     open _=p=_

     abc : {i j : ℕ }  → (i ≤ 3 ) → ( j ≤ 4 ) → Permutation  5 5
     abc i<3 j<4 = ins2 3rot i<3 j<4
     dba : {i j : ℕ }  → (i ≤ 3 ) → ( j ≤ 4 ) → Permutation  5 5
     dba i<3 j<4 = ins2 (3rot ∘ₚ 3rot) i<3 j<4

     counter-example :  ¬ (abc 0<3 0<4  =p= pid )
     counter-example eq with ←pleq _ _ eq
     ...  | ()

     record Triple {i j : ℕ } (i<3 : i ≤ 3) (j<4 : j ≤ 4) (rot : Permutation 3 3) : Set where
       field 
         dba0<3 : Fin 4
         dba1<4 : Fin 5
         aec0<3 : Fin 4
         aec1<4 : Fin 5
         abc= : ins2 rot i<3 j<4 =p= [ ins2 (rot ∘ₚ rot)  (fin≤n {3} dba0<3) (fin≤n {4} dba1<4)  , ins2 (rot ∘ₚ rot) (fin≤n {3} aec0<3) (fin≤n {4} aec1<4) ]

     open Triple
     triple : {i j : ℕ } → (i<3 : i ≤ 3) (j<4 : j ≤ 4) → Triple i<3 j<4 3rot
     triple z≤n z≤n =                               record { dba0<3 = # 0 ; dba1<4 = # 4 ; aec0<3 = # 2 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     triple z≤n (s≤s z≤n) =                         record { dba0<3 = # 0 ; dba1<4 = # 4 ; aec0<3 = # 2 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     triple z≤n (s≤s (s≤s z≤n)) =                   record { dba0<3 = # 1 ; dba1<4 = # 0 ; aec0<3 = # 3 ; aec1<4 = # 2 ; abc= = pleq _ _ refl }
     triple z≤n (s≤s (s≤s (s≤s z≤n))) =             record { dba0<3 = # 1 ; dba1<4 = # 3 ; aec0<3 = # 0 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     triple z≤n (s≤s (s≤s (s≤s (s≤s z≤n)))) =       record { dba0<3 = # 0 ; dba1<4 = # 0 ; aec0<3 = # 2 ; aec1<4 = # 4 ; abc= = pleq _ _ refl } 
     triple (s≤s z≤n) z≤n =                         record { dba0<3 = # 0 ; dba1<4 = # 2 ; aec0<3 = # 3 ; aec1<4 = # 1 ; abc= = pleq _ _ refl }
     triple (s≤s z≤n) (s≤s z≤n) =                   record { dba0<3 = # 0 ; dba1<4 = # 2 ; aec0<3 = # 3 ; aec1<4 = # 1 ; abc= = pleq _ _ refl }
     triple (s≤s z≤n) (s≤s (s≤s z≤n)) =             record { dba0<3 = # 1 ; dba1<4 = # 0 ; aec0<3 = # 3 ; aec1<4 = # 2 ; abc= = pleq _ _ refl }
     triple (s≤s z≤n) (s≤s (s≤s (s≤s z≤n))) =       record { dba0<3 = # 0 ; dba1<4 = # 3 ; aec0<3 = # 1 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     triple (s≤s z≤n) (s≤s (s≤s (s≤s (s≤s z≤n)))) = record { dba0<3 = # 2 ; dba1<4 = # 4 ; aec0<3 = # 0 ; aec1<4 = # 2 ; abc= = pleq _ _ refl }
     triple (s≤s (s≤s z≤n)) z≤n =                   record { dba0<3 = # 3 ; dba1<4 = # 0 ; aec0<3 = # 1 ; aec1<4 = # 3 ; abc= = pleq _ _ refl }
     triple (s≤s (s≤s z≤n)) (s≤s z≤n) =             record { dba0<3 = # 3 ; dba1<4 = # 0 ; aec0<3 = # 1 ; aec1<4 = # 3 ; abc= = pleq _ _ refl }
     triple (s≤s (s≤s z≤n)) (s≤s (s≤s z≤n)) =       record { dba0<3 = # 1 ; dba1<4 = # 3 ; aec0<3 = # 0 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     triple (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n))) = record { dba0<3 = # 0 ; dba1<4 = # 3 ; aec0<3 = # 1 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     triple (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s (s≤s z≤n)))) = record { dba0<3 = # 1 ; dba1<4 = # 4 ; aec0<3 = # 2 ; aec1<4 = # 2 ; abc= = pleq _ _ refl }
     triple (s≤s (s≤s (s≤s z≤n))) z≤n =             record { dba0<3 = # 2 ; dba1<4 = # 4 ; aec0<3 = # 1 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     triple (s≤s (s≤s (s≤s z≤n))) (s≤s z≤n) =       record { dba0<3 = # 2 ; dba1<4 = # 4 ; aec0<3 = # 1 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     triple (s≤s (s≤s (s≤s z≤n))) (s≤s (s≤s z≤n)) = record { dba0<3 = # 0 ; dba1<4 = # 0 ; aec0<3 = # 2 ; aec1<4 = # 4 ; abc= = pleq _ _ refl }
     triple (s≤s (s≤s (s≤s z≤n))) (s≤s (s≤s (s≤s z≤n))) = record { dba0<3 = # 2 ; dba1<4 = # 4 ; aec0<3 = # 0 ; aec1<4 = # 2 ; abc= = pleq _ _ refl }
     triple (s≤s (s≤s (s≤s z≤n))) (s≤s (s≤s (s≤s (s≤s z≤n)))) = 
                                                    record { dba0<3 = # 1 ; dba1<4 = # 4 ; aec0<3 = # 0 ; aec1<4 = # 3 ; abc= = pleq _ _ refl }  
     
     _⁻¹ : {n : ℕ } ( x : Permutation n n) → Permutation n n 
     _⁻¹ = pinv 

     -- tt5 : (i : Fin 4) (j : Fin 5) → (z : Fin 4) → (w : Fin 5) → (x : Fin 5) (y : Fin 4)  → (rot : Permutation 3 3 )  → List (List ℕ) → List (List ℕ)
     -- tt5 i j z w x y rot t with is-=p= (ins2 rot (fin≤n  i) (fin≤n  j)) 
     --             [ ins2 (rot ∘ₚ rot)   (fin≤n  z) (fin≤n  x)  , ins2 (pinv rot) (fin≤n  y)  (fin≤n  w) ]
     -- ... | yes _ = ( toℕ i ∷ toℕ j ∷ 9 ∷ toℕ z ∷ toℕ x ∷ toℕ y ∷ toℕ w  ∷ [] ) ∷ t
     -- ... | no _ = t

     -- open import  Relation.Binary.Definitions

     -- tt2 : (i : Fin 4) (j : Fin 5) →  (rot : Permutation 3 3 ) → List (List ℕ)
     -- tt2  i j rot = tt3 (# 4) (# 3) (# 3) (# 4) [] where
     --     tt3 : (w : Fin 5) (z : Fin 4) (x : Fin 4) (y : Fin 5) → List (List ℕ) → List (List ℕ)
     --     tt3 zero zero zero zero t =                                       ( tt5 i j zero zero zero zero    rot [] ) ++ t
     --     tt3 (suc w)  zero zero zero t =  tt3 (fin+1 w) (# 3) (# 3) (# 4)       ((tt5 i j zero (suc w) zero zero    rot [] ) ++ t)
     --     tt3 w z zero (suc y) t =       tt3 w z         (# 3) (fin+1 y)   ((tt5 i j z w (suc y) zero    rot [] ) ++ t) 
     --     tt3 w z (suc x) y    t =       tt3 w z         (fin+1 x)    y    ((tt5 i j z  w y    (suc x) rot [] ) ++ t) 
     --     tt3 w (suc z) zero zero t =    tt3 w (fin+1 z) (# 3) (# 4)       ((tt5 i j (suc z) w zero zero    rot [] ) ++ t)

     -- tt4 :  List (List (List ℕ))
     -- tt4  = tt2 (# 0) (# 0) (pinv 3rot) ∷
     --       tt2 (# 1) (# 0) (pinv 3rot) ∷
     --       tt2 (# 2) (# 0) (pinv 3rot) ∷
     --       tt2 (# 3) (# 0) (pinv 3rot) ∷
     --       tt2 (# 0) (# 1) (pinv 3rot) ∷
     --       tt2 (# 1) (# 1) (pinv 3rot) ∷
     --       tt2 (# 2) (# 1) (pinv 3rot) ∷
     --       tt2 (# 3) (# 1) (pinv 3rot) ∷
     --       tt2 (# 0) (# 2) (pinv 3rot) ∷
     --       tt2 (# 1) (# 2) (pinv 3rot) ∷
     --       tt2 (# 2) (# 2) (pinv 3rot) ∷
     --       tt2 (# 3) (# 2) (pinv 3rot) ∷
     --       tt2 (# 0) (# 3) (pinv 3rot) ∷
     --       tt2 (# 1) (# 3) (pinv 3rot) ∷
     --       tt2 (# 2) (# 3) (pinv 3rot) ∷
     --       tt2 (# 3) (# 3) (pinv 3rot) ∷
     --       tt2 (# 0) (# 4) (pinv 3rot) ∷
     --       tt2 (# 1) (# 4) (pinv 3rot) ∷
     --       tt2 (# 2) (# 4) (pinv 3rot) ∷
     --       tt2 (# 3) (# 4) (pinv 3rot) ∷
     --       []

     open Triple 
     dba-triple : {i j : ℕ }  → (i<3 : i ≤ 3 ) → (j<4 :  j ≤ 4 ) → Triple i<3 j<4 (3rot  ∘ₚ 3rot )
     dba-triple z≤n z≤n =                               record { dba0<3 = # 0 ; dba1<4 = # 2 ; aec0<3 = # 2 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     dba-triple z≤n (s≤s z≤n) =                         record { dba0<3 = # 0 ; dba1<4 = # 2 ; aec0<3 = # 2 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     dba-triple z≤n (s≤s (s≤s z≤n)) =                   record { dba0<3 = # 1 ; dba1<4 = # 3 ; aec0<3 = # 3 ; aec1<4 = # 2 ; abc= = pleq _ _ refl }
     dba-triple z≤n (s≤s (s≤s (s≤s z≤n))) =             record { dba0<3 = # 0 ; dba1<4 = # 2 ; aec0<3 = # 2 ; aec1<4 = # 4 ; abc= = pleq _ _ refl }
     dba-triple z≤n (s≤s (s≤s (s≤s (s≤s z≤n)))) =       record { dba0<3 = # 3 ; dba1<4 = # 0 ; aec0<3 = # 0 ; aec1<4 = # 2 ; abc= = pleq _ _ refl } 
     dba-triple (s≤s z≤n) z≤n =                         record { dba0<3 = # 0 ; dba1<4 = # 0 ; aec0<3 = # 1 ; aec1<4 = # 3 ; abc= = pleq _ _ refl }
     dba-triple (s≤s z≤n) (s≤s z≤n) =                   record { dba0<3 = # 0 ; dba1<4 = # 0 ; aec0<3 = # 1 ; aec1<4 = # 3 ; abc= = pleq _ _ refl }
     dba-triple (s≤s z≤n) (s≤s (s≤s z≤n)) =             record { dba0<3 = # 1 ; dba1<4 = # 3 ; aec0<3 = # 3 ; aec1<4 = # 2 ; abc= = pleq _ _ refl }
     dba-triple (s≤s z≤n) (s≤s (s≤s (s≤s z≤n))) =       record { dba0<3 = # 1 ; dba1<4 = # 4 ; aec0<3 = # 2 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     dba-triple (s≤s z≤n) (s≤s (s≤s (s≤s (s≤s z≤n)))) = record { dba0<3 = # 1 ; dba1<4 = # 3 ; aec0<3 = # 3 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     dba-triple (s≤s (s≤s z≤n)) z≤n =                   record { dba0<3 = # 2 ; dba1<4 = # 4 ; aec0<3 = # 0 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     dba-triple (s≤s (s≤s z≤n)) (s≤s z≤n) =             record { dba0<3 = # 2 ; dba1<4 = # 4 ; aec0<3 = # 0 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     dba-triple (s≤s (s≤s z≤n)) (s≤s (s≤s z≤n)) =       record { dba0<3 = # 0 ; dba1<4 = # 2 ; aec0<3 = # 2 ; aec1<4 = # 4 ; abc= = pleq _ _ refl }
     dba-triple (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n))) = record { dba0<3 = # 1 ; dba1<4 = # 4 ; aec0<3 = # 2 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     dba-triple (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s (s≤s z≤n)))) = record { dba0<3 = # 2 ; dba1<4 = # 0 ; aec0<3 = # 3 ; aec1<4 = # 2 ; abc= = pleq _ _ refl }
     dba-triple (s≤s (s≤s (s≤s z≤n))) z≤n =             record { dba0<3 = # 0 ; dba1<4 = # 4 ; aec0<3 = # 1 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     dba-triple (s≤s (s≤s (s≤s z≤n))) (s≤s z≤n) =       record { dba0<3 = # 0 ; dba1<4 = # 4 ; aec0<3 = # 1 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     dba-triple (s≤s (s≤s (s≤s z≤n))) (s≤s (s≤s z≤n)) = record { dba0<3 = # 3 ; dba1<4 = # 0 ; aec0<3 = # 0 ; aec1<4 = # 2 ; abc= = pleq _ _ refl }
     dba-triple (s≤s (s≤s (s≤s z≤n))) (s≤s (s≤s (s≤s z≤n))) = record { dba0<3 = # 1 ; dba1<4 = # 3 ; aec0<3 = # 3 ; aec1<4 = # 0 ; abc= = pleq _ _ refl }
     dba-triple (s≤s (s≤s (s≤s z≤n))) (s≤s (s≤s (s≤s (s≤s z≤n)))) = 
                                                    record { dba0<3 = # 2 ; dba1<4 = # 0 ; aec0<3 = # 3 ; aec1<4 = # 2 ; abc= = pleq _ _ refl }  
     
     -3=33 : pinv 3rot =p= (3rot ∘ₚ 3rot )
     -3=33 = pleq _ _ refl

     4=1 : (3rot ∘ₚ 3rot) ∘ₚ (3rot ∘ₚ 3rot ) =p= 3rot
     4=1 = pleq _ _ refl

     dervie-any-3rot0 : (n : ℕ ) → {i j : ℕ }  → (i<3 : i ≤ 3 ) → (j<4 : j ≤ 4 )
          → deriving n (abc i<3 j<4 ) 
     dervie-any-3rot1 : (n : ℕ ) → {i j : ℕ }  → (i<3 : i ≤ 3 ) → (j<4 : j ≤ 4 )
          → deriving n (dba i<3 j<4 ) 

     commd : {n : ℕ } → (f g : Permutation 5 5)
           →  deriving n f
           →  deriving n g
           → Commutator (deriving n) [ f , g ]
     commd {n} f g df dg =  comm {deriving n} {f} {g} df dg prefl

     dervie-any-3rot0 0 i<3 j<4 = lift tt 
     dervie-any-3rot0 (suc i) i<3 j<4 = ccong _  (psym ceq) (commd dba0 aec0 df dg )where
        tc = triple i<3 j<4
        dba0 = dba (fin≤n {3} (dba0<3 tc)) (fin≤n {4} (dba1<4 tc))
        aec0 = dba (fin≤n {3} (aec0<3 tc)) (fin≤n {4} (aec1<4 tc))
        ceq : abc i<3 j<4  =p=  [ dba0 , aec0 ]  
        ceq = record { peq = peq (abc= tc) }
        df =  dervie-any-3rot1 i  (fin≤n {3} (dba0<3 tc)) (fin≤n {4} (dba1<4 tc))
        dg =  dervie-any-3rot1 i  (fin≤n {3} (aec0<3 tc)) (fin≤n {4} (aec1<4 tc)) 

     dervie-any-3rot1 0 i<3 j<4 = lift tt 
     dervie-any-3rot1 (suc n) {i} {j} i<3 j<4 = ccong _  ( psym ceq )  (commd aec0 abc0 df dg ) where
        tdba = dba-triple i<3 j<4
        aec0 = ins2 ((3rot ∘ₚ 3rot) ∘ₚ (3rot ∘ₚ 3rot )) (fin≤n {3} (dba0<3 tdba)) (fin≤n {4} (dba1<4 tdba))
        abc0 = ins2 ((3rot ∘ₚ 3rot) ∘ₚ (3rot ∘ₚ 3rot )) (fin≤n {3} (aec0<3 tdba)) (fin≤n {4} (aec1<4 tdba))
        ceq : dba i<3 j<4 =p=  [ aec0 , abc0 ]  
        ceq = record { peq = peq (abc= tdba) }
        df : deriving n (ins2 ((3rot ∘ₚ 3rot) ∘ₚ (3rot ∘ₚ 3rot )) (fin≤n {3} (dba0<3 tdba)) (fin≤n {4} (dba1<4 tdba)))
        df = deriving-subst (psym (ins2cong {toℕ (dba0<3 (dba-triple i<3 j<4))} {toℕ (dba1<4 (dba-triple i<3 j<4))} 4=1 ))
             (dervie-any-3rot0 n  (fin≤n {3} (dba0<3 tdba)) (fin≤n {4} (dba1<4 tdba)))
        dg : deriving n (ins2 ((3rot ∘ₚ 3rot) ∘ₚ (3rot ∘ₚ 3rot )) (fin≤n {3} (aec0<3 tdba)) (fin≤n {4} (aec1<4 tdba)))
        dg = deriving-subst (psym (ins2cong {toℕ (aec0<3 (dba-triple i<3 j<4))} {toℕ (aec1<4 (dba-triple i<3 j<4))} 4=1 )) 
             (dervie-any-3rot0 n  (fin≤n {3} (aec0<3 tdba)) (fin≤n {4} (aec1<4 tdba)))

