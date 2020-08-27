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
       S = Symmetric 5
       open Group (Symmetric 5)
       postulate lemma : (abc i<3 j<4 ∘ₚ abc i<3 j<4 ) =p=  dba i<3 j<4 
       -- some kind of functional extentionaly required?
       -- lemma = begin
       --    abc i<3 j<4 ∘ₚ abc i<3 j<4 
       --   ≈⟨ prefl ⟩
       --    ((save2 i<3 j<4 ∘ₚ (pprep (pprep 3rot))) ∘ₚ flip (save2 i<3 j<4 )) ∘ₚ
       --       ((save2 i<3 j<4 ∘ₚ (pprep (pprep 3rot))) ∘ₚ flip (save2 i<3 j<4 ))
       --   ≈⟨  ∙-flatten (Symmetric 5) (((am (save2 i<3 j<4) o am (pprep (pprep 3rot))) o am (flip (save2 i<3 j<4 ))) o 
       --       ((am (save2 i<3 j<4) o am (pprep (pprep 3rot))) o am ( flip (save2 i<3 j<4 )))) ⟩
       --       save2 i<3 j<4 ∘ₚ (pprep (pprep 3rot) ∘ₚ (flip (save2 i<3 j<4 ) ∘ₚ (
       --         save2 i<3 j<4  ∘ₚ (pprep (pprep 3rot) ∘ₚ (flip (save2 i<3 j<4 ) ∘ₚ pid  )))))
       --   ≈⟨ ∙-cong prefl ( ∙-cong prefl (grm S (proj₁ inverse _))) ⟩
       --       save2 i<3 j<4 ∘ₚ (pprep (pprep 3rot) ∘ₚ (pprep (pprep 3rot) ∘ₚ (flip (save2 i<3 j<4 ) ∘ₚ pid  )))
       --   ≈⟨ ∙-cong prefl (grepl S (pprep-cong prefl ) ) ⟩
       --    (save2 i<3 j<4 ∘ₚ (pprep (pprep (3rot ∘ₚ 3rot)))) ∘ₚ flip (save2 i<3 j<4 )
       --   ≈⟨ prefl ⟩
       --    dba i<3 j<4
       --   ∎

     postulate  -- someday
        dba→aec : {i j : ℕ }  → (i<3 : i ≤ 3 ) → (j<4 :  j ≤ 4 ) →  (dba i<3 j<4 ∘ₚ dba i<3 j<4 ) =p=  aec i<3 j<4 
        aec→abc : {i j : ℕ }  → (i<3 : i ≤ 3 ) → (j<4 :  j ≤ 4 ) →  (aec i<3 j<4 ∘ₚ aec i<3 j<4 ) =p=  abc i<3 j<4 

     record Triple {i j : ℕ } (i<3 : i ≤ 3) (j<4 : j ≤ 4) (rot : Permutation 3 3) : Set where
       field 
         dba0<3 : Fin 4
         dba1<4 : Fin 5
         aec0<3 : Fin 4
         aec1<4 : Fin 5
         abc= : ins2 rot i<3 j<4 =p= [ ins2 (rot ∘ₚ rot)  (fin≤n {3} dba0<3) (fin≤n {4} dba1<4)  , ins2 (pinv rot) (fin≤n {3} aec0<3) (fin≤n {4} aec1<4) ]

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

     dba-triple : {i j : ℕ }  → (i<3 : i ≤ 3 ) → (j<4 :  j ≤ 4 ) → Triple i<3 j<4 (3rot  ∘ₚ 3rot )
     dba-triple = ?

     aec-triple : {i j : ℕ }  → (i<3 : i ≤ 3 ) → (j<4 :  j ≤ 4 ) → Triple i<3 j<4 (pinv 3rot ) 
     aec-triple = ?


     dervie-any-3rot : (n : ℕ ) → {i j : ℕ }  → (i<3 : i ≤ 3 ) → (j<4 : j ≤ 4 )
          → deriving n (abc i<3 j<4 ) ∧ deriving n (dba i<3 j<4 ) ∧ deriving n (aec i<3 j<4 )
     dervie-any-3rot 0 i<3 j<4 = ⟪ lift tt , ⟪ lift tt , lift tt ⟫ ⟫
     dervie-any-3rot (suc i) i<3 j<4 =  ⟪ d0 , ⟪ d1 , d2 ⟫ ⟫ where
        tc : Triple i<3 j<4 3rot
        tc = triple i<3 j<4
        abc0 =  abc i<3 j<4
        b<3 = fin≤n {3} (dba0<3 tc)
        b<4 = fin≤n {4} (dba1<4 tc)
        dba0 =  dba b<3 b<4
        c<3 = fin≤n {3} (aec0<3 tc)
        c<4 = fin≤n {4} (aec1<4 tc)
        aec0 =  aec c<3 c<4
        d0 : deriving (suc i) (abc i<3 j<4)
        d0 = 
         ccong {deriving i} ( psym (abc= tc )) (
          comm {deriving i} {dba0} {aec0}
              (proj1 (proj2 ( dervie-any-3rot i  b<3 b<4)))
              (proj2 (proj2 ( dervie-any-3rot i  c<3 c<4 ))))
        d1 : deriving (suc i) (dba i<3 j<4)
        d1 = 
         ccong {deriving i} ( psym {!!}) (   -- dba i<3 j<4 =p= [ aec0 , abc0 ]   --    dba= : dba b<3 b<4 =p= [ aec0 , abc0 ]  is not enough...
          comm {deriving i} {aec0} {abc0}
              (proj2 (proj2 ( dervie-any-3rot i  c<3 c<4 )))
              (proj1 ( dervie-any-3rot i  i<3 j<4 )))
        d2 : deriving (suc i) (aec i<3 j<4)
        d2 = 
         ccong {deriving i} ( psym {!!}) (
          comm {deriving i} {abc0} {dba0}
              (proj1 ( dervie-any-3rot i  i<3 j<4 ))
              (proj1 (proj2 ( dervie-any-3rot i  b<3 b<4 ) )))

     open _=p=_
     counter-example :  ¬ (abc 0<3 0<4  =p= pid )
     counter-example eq with ←pleq _ _ eq
     ...  | ()


