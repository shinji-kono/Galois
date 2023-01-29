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

ε≈ε⁻¹ : ε ≈ ε ⁻¹
ε≈ε⁻¹ = begin
     ε          ≈⟨ gsym (proj₁ inverse _) ⟩
     ε ⁻¹ ∙ ε   ≈⟨ proj₂ identity _ ⟩
     ε ⁻¹
   ∎ where open EqReasoning (Algebra.Group.setoid G)

f⁻¹⁻¹≈f : {f : Carrier } →  ( f ⁻¹ ) ⁻¹  ≈ f
f⁻¹⁻¹≈f {f} = begin
     ( f ⁻¹ ) ⁻¹   ≈⟨ gsym ( proj₁ identity _) ⟩
      ε  ∙ ( f ⁻¹ ) ⁻¹   ≈⟨ ∙-cong (gsym ( proj₂ inverse _ )) grefl ⟩
     (f ∙ f ⁻¹ ) ∙ ( f ⁻¹ ) ⁻¹   ≈⟨ assoc _ _ _ ⟩
     f ∙ ( f ⁻¹  ∙ ( f ⁻¹ ) ⁻¹ )  ≈⟨ ∙-cong grefl (proj₂ inverse _) ⟩
     f ∙ ε  ≈⟨ proj₂ identity _ ⟩
     f
   ∎ where open EqReasoning (Algebra.Group.setoid G)

≡→≈ : {f g : Carrier } → f ≡ g → f ≈ g
≡→≈ refl = grefl

car : {f g h : Carrier } → f ≈ g → f ∙ h ≈ g ∙ h
car f=g = ∙-cong f=g grefl 

cdr : {f g h : Carrier } → f ≈ g → h ∙ f  ≈ h ∙ g 
cdr f=g = ∙-cong grefl f=g 

-- module _ where
--     open EqReasoning (Algebra.Group.setoid G)
--     _≈⟨⟩_ : (a : Carrier ) → {b : Carrier} → a IsRelatedTo b → a IsRelatedTo b
--     _ ≈⟨⟩ a  = a

open import Tactic.MonoidSolver using (solve; solve-macro)

lemma5 : (f g : Carrier ) → g ⁻¹ ∙ f ⁻¹ ≈ (f ∙ g) ⁻¹
lemma5 f g = begin
     g ⁻¹ ∙ f ⁻¹                                     ≈⟨ gsym (proj₂ identity _) ⟩
     g ⁻¹ ∙ f ⁻¹  ∙ ε                                ≈⟨ gsym (∙-cong grefl (proj₂ inverse _ )) ⟩
     g ⁻¹ ∙ f ⁻¹  ∙ ( (f ∙ g) ∙ (f ∙ g) ⁻¹ )         ≈⟨ solve monoid ⟩
     g ⁻¹ ∙ ((f ⁻¹ ∙ f) ∙ (g ∙ ((f ∙ g) ⁻¹ ∙ ε)))    ≈⟨ ∙-cong grefl (gtrans (∙-cong (proj₁ inverse _ ) grefl) (proj₁ identity _)) ⟩
     g ⁻¹ ∙ (g ∙ ((f ∙ g) ⁻¹ ∙ ε))                   ≈⟨ solve monoid ⟩
     (g ⁻¹ ∙ g ) ∙ ((f ∙ g) ⁻¹ ∙ ε)                  ≈⟨ gtrans (∙-cong (proj₁ inverse _ ) grefl) (proj₁ identity _) ⟩
     (f ∙ g) ⁻¹ ∙ ε                                  ≈⟨ solve monoid ⟩
     (f ∙ g) ⁻¹
     ∎ where open EqReasoning (Algebra.Group.setoid G)


