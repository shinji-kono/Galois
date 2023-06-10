--
-- checking does not terminate, sorry
--
open import Level hiding ( suc ; zero )
open import Algebra
module sym5a where

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
open import Data.Fin.Permutation  hiding (_∘ₚ_)

infixr  200 _∘ₚ_
_∘ₚ_ = Data.Fin.Permutation._∘ₚ_

open import Data.List  hiding ( [_] )
open import nat
open import fin
open import logic

open _∧_

¬sym5solvable : ¬ ( solvable (Symmetric 5) )
¬sym5solvable sol = counter-example (end5 (abc 0<3 0<4 ) (any3de (dervied-length sol) 3rot 0<3 0<4 ) ) where
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

     -- Permutation 5 5 include any Permutation 3 3
     any3 : {i j : ℕ }  → Permutation 3 3  → (i ≤ 3 ) → ( j ≤ 4 ) → Permutation  5 5
     any3 abc i<3 j<4 = (save2 i<3 j<4 ∘ₚ (pprep (pprep abc))) ∘ₚ flip (save2 i<3 j<4 ) 

     any3cong : {i j : ℕ }  → {x y : Permutation 3 3 } → {i<3 : i ≤ 3 } → {j<4 : j ≤ 4 } → x =p= y → any3 x i<3 j<4  =p= any3 y i<3 j<4
     any3cong {i} {j} {x} {y} {i<3} {j<4} x=y = presp {5} {save2 i<3 j<4 ∘ₚ (pprep (pprep x))} {_} {flip (save2 i<3 j<4 )}
         (presp {5} {save2 i<3 j<4} prefl (pprep-cong (pprep-cong x=y)) ) prefl 

     open _=p=_

     -- derving n includes any Permutation 3 3, 
     any3de : {i j : ℕ } → (n : ℕ) → (abc : Permutation 3 3) →  (i<3 : i ≤ 3 ) → (j<4 :  j ≤ 4 ) → deriving n (any3 abc i<3 j<4)
     any3de {i} {j} zero abc i<3 j<4 = Level.lift tt
     any3de {i} {j} (suc n) abc i<3 j<4 = ccong abc-from-comm (comm (any3de n (abc  ∘ₚ abc) i<3 j0<4 ) (any3de n (abc  ∘ₚ abc) i0<3 j<4 ))  where
         i0 : ℕ
         i0 = ?
         j0 : ℕ
         j0 = ?
         i0<3 : i0 ≤ 3
         i0<3 = {!!}
         j0<4 : j0 ≤ 4
         j0<4 = {!!}
         abc-from-comm : [ any3 (abc  ∘ₚ abc) i<3 j0<4  , any3 (abc  ∘ₚ abc) i0<3 j<4 ] =p= any3 abc i<3 j<4
         abc-from-comm = {!!}

     abc : {i j : ℕ }  → (i ≤ 3 ) → ( j ≤ 4 ) → Permutation  5 5
     abc i<3 j<4 = any3 3rot i<3 j<4

     counter-example :  ¬ (abc 0<3 0<4  =p= pid )
     counter-example eq with ←pleq _ _ eq
     ...  | ()

