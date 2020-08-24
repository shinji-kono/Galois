open import Level hiding ( suc ; zero )
open import Algebra
module Gutil {n m : Level} (G : Group n m ) where

open import Data.Unit
open import Function.Inverse as Inverse using (_↔_; Inverse; _InverseOf_)
open import Function
open import Data.Nat hiding (_⊔_) -- using (ℕ; suc; zero)
open import Relation.Nullary
open import Data.Empty
open import Data.Product
open import  Relation.Binary.PropositionalEquality hiding ( [_] )


open Group G

import Relation.Binary.Reasoning.Setoid as EqReasoning

gsym = Algebra.Group.sym G
grefl = Algebra.Group.refl G
gtrans = Algebra.Group.trans G

lemma3 : ε ≈ ε ⁻¹
lemma3 = begin
     ε          ≈⟨ gsym (proj₁ inverse _) ⟩
     ε ⁻¹ ∙ ε   ≈⟨ proj₂ identity _ ⟩
     ε ⁻¹
   ∎ where open EqReasoning (Algebra.Group.setoid G)

lemma6 : {f : Carrier } →  ( f ⁻¹ ) ⁻¹  ≈ f
lemma6 {f} = begin
     ( f ⁻¹ ) ⁻¹   ≈⟨ gsym ( proj₁ identity _) ⟩
      ε  ∙ ( f ⁻¹ ) ⁻¹   ≈⟨ ∙-cong (gsym ( proj₂ inverse _ )) grefl ⟩
     (f ∙ f ⁻¹ ) ∙ ( f ⁻¹ ) ⁻¹   ≈⟨ assoc _ _ _ ⟩
     f ∙ ( f ⁻¹  ∙ ( f ⁻¹ ) ⁻¹ )  ≈⟨ ∙-cong grefl (proj₂ inverse _) ⟩
     f ∙ ε  ≈⟨ proj₂ identity _ ⟩
     f
   ∎ where open EqReasoning (Algebra.Group.setoid G)

≡→≈ : {f g : Carrier } → f ≡ g → f ≈ g
≡→≈ refl = grefl

---
-- to avoid assoc storm, flatten multiplication according to the template
--

data MP  : Carrier → Set (Level.suc n) where
    am  : (x : Carrier )   →  MP  x
    _o_ : {x y : Carrier } →  MP  x →  MP  y → MP  ( x ∙ y )

mpf : {x : Carrier } → (m : MP x ) → Carrier → Carrier
mpf (am x) y = x ∙ y
mpf (m o m₁) y = mpf m ( mpf m₁ y )

mp-flatten : {x : Carrier } → (m : MP x ) → Carrier 
mp-flatten  m = mpf m ε 

mpl1 : Carrier → {x : Carrier } → MP x → Carrier
mpl1 x (am y) = x ∙ y
mpl1 x (y o y1) = mpl1 ( mpl1 x y ) y1

mpl : {x z : Carrier } → MP x → MP z  → Carrier
mpl (am x)  m = mpl1 x m 
mpl (m o m1) m2 = mpl m (m1 o m2)

mp-flattenl : {x : Carrier } → (m : MP x ) → Carrier
mp-flattenl m = mpl m (am ε)

test1 : ( f g : Carrier ) → Carrier
test1 f g = mp-flattenl ((am (g ⁻¹) o am (f ⁻¹) ) o ( (am f o am g) o am ((f ∙ g) ⁻¹ ))) 

test2 : ( f g : Carrier ) → test1 f g ≡  g ⁻¹ ∙ f ⁻¹ ∙ f ∙ g ∙  (f ∙ g) ⁻¹  ∙ ε
test2 f g = _≡_.refl

test3 : ( f g : Carrier ) → Carrier
test3 f g = mp-flatten ((am (g ⁻¹) o am (f ⁻¹) ) o ( (am f o am g) o am ((f ∙ g) ⁻¹ ))) 

test4 : ( f g : Carrier ) → test3 f g ≡ g ⁻¹ ∙ (f ⁻¹ ∙ (f ∙ (g ∙ ((f ∙ g) ⁻¹ ∙ ε))))
test4 f g = _≡_.refl

  
∙-flatten : {x : Carrier } → (m : MP x ) → x ≈ mp-flatten m
∙-flatten {x} (am x) = gsym (proj₂ identity _)
∙-flatten {_} (am x o q) = ∙-cong grefl ( ∙-flatten q )
∙-flatten (_o_ {_} {z} (_o_ {x} {y} p q) r) = lemma9 _ _ _ ( ∙-flatten {x ∙ y } (p o q )) ( ∙-flatten {z} r ) where
   mp-cong : {p q r : Carrier} → (P : MP p)  → q ≈ r → mpf P q ≈ mpf P r
   mp-cong (am x) q=r = ∙-cong grefl q=r
   mp-cong (P o P₁) q=r = mp-cong P ( mp-cong P₁ q=r )
   mp-assoc : {p q r : Carrier} → (P : MP p)  → mpf P q ∙ r ≈ mpf P (q ∙ r )
   mp-assoc (am x) = assoc _ _ _ 
   mp-assoc {p} {q} {r} (P o P₁) = begin
       mpf P (mpf  P₁ q) ∙ r      ≈⟨ mp-assoc P ⟩
       mpf P (mpf P₁ q ∙ r)       ≈⟨ mp-cong P (mp-assoc P₁)  ⟩ mpf P ((mpf  P₁) (q ∙ r))
    ∎ where open EqReasoning (Algebra.Group.setoid G)
   lemma9 : (x y z : Carrier) →  x ∙ y ≈ mpf p (mpf q ε) → z ≈ mpf r ε →  x ∙ y ∙ z ≈ mp-flatten ((p o q) o r)
   lemma9 x y z t s = begin
       x ∙ y ∙ z                    ≈⟨ ∙-cong t grefl  ⟩
       mpf p (mpf q ε) ∙ z          ≈⟨ mp-assoc p ⟩
       mpf p (mpf q ε ∙ z)          ≈⟨ mp-cong p (mp-assoc q ) ⟩
       mpf p (mpf q (ε ∙ z))        ≈⟨ mp-cong p (mp-cong q (proj₁ identity _  )) ⟩
       mpf p (mpf q z)              ≈⟨ mp-cong p (mp-cong q s) ⟩
       mpf p (mpf q (mpf r ε))
    ∎ where open EqReasoning (Algebra.Group.setoid G)

-- ∙-flattenl : {x : Carrier } → (m : MP x ) → x ≈ mp-flattenl m
-- ∙-flattenl (am x) = gsym (proj₂ identity _)
-- ∙-flattenl (q o am x) with ∙-flattenl q    -- x₁ ∙ x ≈ mpl q (am x o am ε) ,  t : x₁ ≈ mpl q (am ε)
-- ... | t = {!!}
-- ∙-flattenl (q o (x o y )) with ∙-flattenl q 
-- ... | t = gtrans (gsym (assoc _ _ _ )) {!!}

lemma5 : (f g : Carrier ) → g ⁻¹ ∙ f ⁻¹ ≈ (f ∙ g) ⁻¹
lemma5 f g = begin
     g ⁻¹ ∙ f ⁻¹                                     ≈⟨ gsym (proj₂ identity _) ⟩
     g ⁻¹ ∙ f ⁻¹  ∙ ε                                ≈⟨ gsym (∙-cong grefl (proj₂ inverse _ )) ⟩
     g ⁻¹ ∙ f ⁻¹  ∙ ( (f ∙ g) ∙ (f ∙ g) ⁻¹ )         ≈⟨ ∙-flatten ((am (g ⁻¹) o am (f ⁻¹) ) o ( (am f o am g) o am ((f ∙ g) ⁻¹ )))  ⟩
     g ⁻¹ ∙ (f ⁻¹ ∙ (f ∙ (g ∙ ((f ∙ g) ⁻¹ ∙ ε))))    ≈⟨ ∙-cong grefl (gsym (assoc _ _ _ )) ⟩
     g ⁻¹ ∙ ((f ⁻¹ ∙ f) ∙ (g ∙ ((f ∙ g) ⁻¹ ∙ ε)))    ≈⟨ ∙-cong grefl (gtrans (∙-cong (proj₁ inverse _ ) grefl) (proj₁ identity _)) ⟩
     g ⁻¹ ∙ (g ∙ ((f ∙ g) ⁻¹ ∙ ε))                   ≈⟨ gsym (assoc _ _ _) ⟩
     (g ⁻¹ ∙ g ) ∙ ((f ∙ g) ⁻¹ ∙ ε)                  ≈⟨ gtrans (∙-cong (proj₁ inverse _ ) grefl) (proj₁ identity _) ⟩
     (f ∙ g) ⁻¹ ∙ ε                                  ≈⟨ proj₂ identity _ ⟩
     (f ∙ g) ⁻¹
     ∎ where open EqReasoning (Algebra.Group.setoid G)

