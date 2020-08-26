open import Level hiding ( suc ; zero )
open import Algebra
module sym5 where

open import Symmetric 
open import Data.Unit using (⊤ ; tt )
open import Function.Inverse as Inverse using (_↔_; Inverse; _InverseOf_)
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
open import Data.Fin.Permutation
open import Data.List  hiding ( [_] )
open import nat
open import fin
open import logic

open _∧_

¬sym5solvable : ¬ ( solvable (Symmetric 5) )
¬sym5solvable sol = counter-example (end5 (abc 0<3 0<4 ) (proj1 (dervie-any-3rot (dervied-length sol) 0<3 0<4 ) )) where

--
--    dba       1320      d → b → a → d
--    (dba)⁻¹   3021      a → b → d → a
--    aec       21430
--    (aec)⁻¹   41032
--    (abd)(cea)(dba)(aec)
-- 

     open solvable
     open Solvable (Symmetric 5) 
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

     abc : {i j : ℕ }  → (i ≤ 3 ) → ( j ≤ 4 ) → Permutation  5 5
     abc i<3 j<4 = ins2 3rot i<3 j<4

     dba : {i j : ℕ }  → (i ≤ 3 ) → ( j ≤ 4 ) → Permutation  5 5
     dba i<3 j<4 = ins2 (3rot ∘ₚ 3rot) i<3 j<4
     aec : {i j : ℕ }  → (i ≤ 3 ) → ( j ≤ 4 ) → Permutation  5 5
     aec i<3 j<4 = ins2 (pinv 3rot) i<3 j<4

     import Relation.Binary.Reasoning.Setoid as EqReasoning
     abc→dba : {i j : ℕ }  → (i<3 : i ≤ 3 ) → (j<4 :  j ≤ 4 ) →  (abc i<3 j<4 ∘ₚ abc i<3 j<4 ) =p=  dba i<3 j<4 
     abc→dba i<3 j<4 = lemma where
       open EqReasoning (Algebra.Group.setoid (Symmetric 5))
       lemma : (abc i<3 j<4 ∘ₚ abc i<3 j<4 ) =p=  dba i<3 j<4 
       lemma = begin
          abc i<3 j<4 ∘ₚ abc i<3 j<4 
         ≈⟨ prefl ⟩
          ((save2 i<3 j<4 ∘ₚ (pprep (pprep 3rot))) ∘ₚ flip (save2 i<3 j<4 )) ∘ₚ
             ((save2 i<3 j<4 ∘ₚ (pprep (pprep 3rot))) ∘ₚ flip (save2 i<3 j<4 ))
         ≈⟨ {!!} ⟩
          (((save2 i<3 j<4 ∘ₚ (pprep (pprep 3rot))) ∘ₚ (flip (save2 i<3 j<4 ))) ∘ₚ
             (save2 i<3 j<4 ∘ₚ (pprep (pprep 3rot)))) ∘ₚ flip (save2 i<3 j<4 )
         ≈⟨ {!!} ⟩
          (save2 i<3 j<4 ∘ₚ (pprep (pprep 3rot) ∘ₚ pprep (pprep 3rot))) ∘ₚ flip (save2 i<3 j<4 )
         ≈⟨ {!!} ⟩
          (save2 i<3 j<4 ∘ₚ (pprep (pprep (3rot ∘ₚ 3rot)))) ∘ₚ flip (save2 i<3 j<4 )
         ≈⟨ prefl ⟩
          dba i<3 j<4
         ∎

     dba→aec : {i j : ℕ }  → (i<3 : i ≤ 3 ) → (j<4 :  j ≤ 4 ) →  (dba i<3 j<4 ∘ₚ dba i<3 j<4 ) =p=  aec i<3 j<4 
     dba→aec = {!!}

     aec→abc : {i j : ℕ }  → (i<3 : i ≤ 3 ) → (j<4 :  j ≤ 4 ) →  (aec i<3 j<4 ∘ₚ aec i<3 j<4 ) =p=  abc i<3 j<4 
     aec→abc = {!!}

     record Triple {i j : ℕ } (i<3 : i ≤ 3) (j<4 : j ≤ 4) : Set where
       field 
         dba0<3 : Fin 4
         dba1<4 : Fin 5
         aec0<3 : Fin 4
         aec1<4 : Fin 5
         abc= : abc i<3 j<4 =p= [ dba (fin≤n {3} dba0<3) (fin≤n {4} dba1<4)  , aec (fin≤n {3} aec0<3) (fin≤n {4} aec1<4) ]

     dba= :
         {a a' : ℕ }  → (a<3 : a ≤ 3 ) → ( a<4 : a' ≤ 4 ) →
         {b b' : ℕ }  → (b<3 : b ≤ 3 ) → ( b<4 : b' ≤ 4 ) →
         {c c' : ℕ }  → (c<3 : c ≤ 3 ) → ( c<4 : c' ≤ 4 ) →
         abc a<3 a<4 =p= [ dba b<3 b<4  , aec c<3 c<4 ] →
         dba a<3 a<4 =p= [ aec b<3 b<4  , abc c<3 c<4 ]
     dba= a<3 a<4 b<3 b<4 c<3 c<4 dq = {!!} where
         open EqReasoning (Algebra.Group.setoid (Symmetric 5))
         lemma1 : dba a<3 a<4 =p= [ aec b<3 b<4  , abc c<3 c<4 ]
         lemma1 = begin
               dba a<3 a<4
             ≈⟨ ? ⟩
               [ aec b<3 b<4  , abc c<3 c<4 ]
             ∎

     aec= :
         {a a' : ℕ }  → (a<3 : a ≤ 3 ) → ( a<4 : a' ≤ 4 ) →
         {b b' : ℕ }  → (b<3 : b ≤ 3 ) → ( b<4 : b' ≤ 4 ) →
         {c c' : ℕ }  → (c<3 : c ≤ 3 ) → ( c<4 : c' ≤ 4 ) →
         dba a<3 a<4 =p= [ aec b<3 b<4  , abc c<3 c<4 ] →
         aec a<3 a<4 =p= [ abc b<3 b<4  , dba c<3 c<4 ] 
     aec= = {!!}

     open Triple
     triple : {i j : ℕ } → (i<3 : i ≤ 3) (j<4 : j ≤ 4) → Triple i<3 j<4
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


     dervie-any-3rot : (n : ℕ ) → {i j : ℕ }  → (i<3 : i ≤ 3 ) → (j<4 : j ≤ 4 )
          → deriving n (abc i<3 j<4 ) ∧ deriving n (dba i<3 j<4 ) ∧ deriving n (aec i<3 j<4 )
     dervie-any-3rot 0 i<3 j<4 = ⟪ lift tt , ⟪ lift tt , lift tt ⟫ ⟫
     dervie-any-3rot (suc i) i<3 j<4 =  {!!}
     --    ccong {deriving i} ( abc= (triple  i<3 j<4 ) ) (
     --    comm {deriving i} {dba} {aec} 
     --         ( dervie-any-3rot i (fin<n {3} {dba0<3 tc}) (fin<n {4} {dba1<4 tc}) ) 
     --         ( dervie-any-3rot i (fin<n {3} {aec0<3 tc}) (fin<n {4} {aec1<4 tc}) )) where
     --             tc : Triple i<3 j<4
     --             tc = triple i<3 j<4
     --             dba : Permutation 5 5
     --             dba = abc (fin<n {3} {dba0<3 tc}) (fin<n {4} {dba1<4   tc})
     --             aec : Permutation 5 5
     --             aec = abc (fin<n {3} {aec0<3 tc}) (fin<n {4} {aec1<4   tc})

     open _=p=_
     counter-example :  ¬ (abc 0<3 0<4  =p= pid )
     counter-example eq with ←pleq _ _ eq
     ...  | ()


