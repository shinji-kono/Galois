-- fundamental homomorphism theorem
--

open import Level hiding ( suc ; zero )
module FundamentalHomorphism (c : Level) where

open import Algebra
open import Algebra.Structures
open import Algebra.Definitions
open import Algebra.Core
open import Algebra.Bundles

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Gutil0
import Gutil
import Function.Definitions as FunctionDefinitions

import Algebra.Morphism.Definitions as MorphismDefinitions
open import Algebra.Morphism.Structures

open import Tactic.MonoidSolver using (solve; solve-macro)

--
-- Given two groups G and H and a group homomorphism f : G → H,
-- let K be a normal subgroup in G and φ the natural surjective homomorphism G → G/K
-- (where G/K is the quotient group of G by K).
-- If K is a subset of ker(f) then there exists a unique homomorphism h: G/K → H such that f = h∘φ.
--     https://en.wikipedia.org/wiki/Fundamental_theorem_on_homomorphisms
--
--       f
--    G --→ H
--    |   /
--  φ |  / h
--    ↓ /
--    G/K
--

import Relation.Binary.Reasoning.Setoid as EqReasoning

_<_∙_> :  (m : Group c c )  →    Group.Carrier m →  Group.Carrier m →  Group.Carrier m
m < x ∙ y > =  Group._∙_ m x y

_<_≈_> :  (m : Group c c )  →    (f  g : Group.Carrier m ) → Set c
m < x ≈ y > =  Group._≈_ m x y

infixr 9 _<_∙_>

--
--  Coset : N : NormalSubGroup →  { a ∙ n | G ∋ a , N ∋ n }
--

open GroupMorphisms

-- import Axiom.Extensionality.Propositional
-- postulate f-extensionality : { n m : Level}  → Axiom.Extensionality.Propositional.Extensionality n m

open import Data.Empty
open import Relation.Nullary

record NormalSubGroup (A : Group c c )  : Set c  where
   open Group A
   field
       ⟦_⟧ : Group.Carrier A → Group.Carrier A
       normal :  IsGroupHomomorphism (GR A) (GR A)  ⟦_⟧
       comm : {a b :  Carrier } → b ∙ ⟦ a ⟧  ≈ ⟦ a ⟧  ∙ b

-- Set of a ∙ ∃ n ∈ N
--
record an {A : Group c c }  (N : NormalSubGroup A ) (n x : Group.Carrier A  ) : Set c where
    open Group A
    open NormalSubGroup N
    field
        a : Carrier 
        aN=x :  a ∙ ⟦ n ⟧ ≈ x

record aN {A : Group c c }  (N : NormalSubGroup A )  : Set c where
    open Group A
    field
        n : Carrier 
        is-an : (x : Carrier) → an N n x

f0 :  {A : Group c c }  (N : NormalSubGroup A )  (x y : Group.Carrier A) → an N x y
f0 {A} N x y = record { a = y ∙ ⟦ x ⟧ ⁻¹ ; aN=x = gk02  } where
   open Group A
   open NormalSubGroup N
   open IsGroupHomomorphism normal
   open EqReasoning (Algebra.Group.setoid A)
   open Gutil A
   gk02 : {x g : Carrier } →  x ∙ ⟦ g ⟧ ⁻¹ ∙ ⟦ g ⟧ ≈ x
   gk02 {x} {g}  = begin  x ∙ ⟦ g ⟧ ⁻¹ ∙ ⟦ g ⟧ ≈⟨ solve monoid  ⟩ 
         x ∙  ( ⟦ g ⟧ ⁻¹ ∙ ⟦ g ⟧)  ≈⟨ ∙-cong grefl (proj₁ inverse _ ) ⟩ 
         x ∙ ε  ≈⟨ proj₂ identity _  ⟩ 
         x ∎

_/_ : (A : Group c c ) (N  : NormalSubGroup A ) → Group c c
_/_ A N  = record {
    Carrier  = aN N
    ; _≈_      = λ f g → ⟦ n f ⟧ ≈ ⟦ n g ⟧
    ; _∙_      = qadd
    ; ε        = qid 
    ; _⁻¹      = λ f → record { n = n f ⁻¹ ; is-an = λ x → record { a = an.a (is-an f x) ∙  ⟦ n f ⟧  ∙ ⟦ n f ⟧  ; aN=x = qinv0 f x } } 
    ; isGroup = record { isMonoid  = record { isSemigroup = record { isMagma = record {
       isEquivalence = record {refl = grefl ; trans = gtrans ; sym = gsym }
       ; ∙-cong = λ {x} {y} {u} {v} x=y u=v → gtrans (homo _ _) ( gtrans (∙-cong x=y u=v)  (gsym (homo _ _) )) }
       ; assoc = qassoc }
       ; identity = (λ q →   ⟦⟧-cong (proj₁ identity _) ) , (λ q → ⟦⟧-cong (proj₂ identity _) )  }
       ; inverse   =  (λ x → ⟦⟧-cong (proj₁ inverse _  )) , (λ x → ⟦⟧-cong (proj₂ inverse _ ) )
       ; ⁻¹-cong   = λ {x} {y} → i-conv  {x} {y}
      }
   } where
       open Group A
       open aN
       open an
       open NormalSubGroup N
       open IsGroupHomomorphism normal
       open EqReasoning (Algebra.Group.setoid A)
       open Gutil A
       qadd : (f g : aN N) → aN N
       qadd f g = record { n = n f ∙ n g  ; is-an = λ x → record { a = x ⁻¹ ∙ ( a (is-an f x) ∙ a (is-an g x))  ; aN=x = qadd0 }  } where
           qadd0 : {x : Carrier} →   x ⁻¹ ∙ (a (is-an f x) ∙ a (is-an g x)) ∙ ⟦ n f ∙ n g ⟧ ≈ x
           qadd0 {x} = begin
              x ⁻¹ ∙ (a (is-an f x) ∙ a (is-an g x)) ∙ ⟦ n f ∙ n g ⟧ ≈⟨ solve monoid ⟩
              x ⁻¹ ∙  (a (is-an f x) ∙ a (is-an g x) ∙ ⟦ n f ∙ n g ⟧) ≈⟨ ? ⟩
              x ⁻¹ ∙  (a (is-an f x) ∙ a (is-an g x) ∙ ( ⟦ n f ⟧  ∙ ⟦ n g ⟧ )) ≈⟨ solve monoid ⟩
              x ⁻¹ ∙  (a (is-an f x) ∙ ( a (is-an g x) ∙  ⟦ n f ⟧)  ∙ ⟦ n g ⟧)  ≈⟨ ? ⟩
              x ⁻¹ ∙  (a (is-an f x) ∙ ( ⟦ n f ⟧ ∙ a (is-an g x) )  ∙ ⟦ n g ⟧)  ≈⟨ ? ⟩
              x ⁻¹ ∙  ((a (is-an f x) ∙ ⟦ n f ⟧ ) ∙ ( a (is-an g x)   ∙ ⟦ n g ⟧))  ≈⟨ ? ⟩
              x ⁻¹ ∙  (x ∙ x)  ≈⟨ solve monoid ⟩
              (x ⁻¹ ∙  x ) ∙ x  ≈⟨ ? ⟩
              ε ∙ x  ≈⟨ solve monoid ⟩
              x ∎
       qinv0 : (f : aN N) → (x : Carrier ) → (a (is-an f x) ∙ ⟦ n f ⟧ ∙ ⟦ n f ⟧) ∙ ⟦ n f ⁻¹ ⟧ ≈ x
       qinv0 f x = begin
          (a (is-an f x) ∙ ⟦ n f ⟧ ∙ ⟦ n f ⟧) ∙ ⟦ n f ⁻¹ ⟧ ≈⟨ ? ⟩
           a (is-an f x) ∙ ⟦ n f ⟧  ≈⟨ an.aN=x (is-an f x) ⟩
          x ∎
       qid :  aN N
       qid = record { n = ε ; is-an = λ x → record { a = x ; aN=x = qid1 } } where
           qid1 : {x : Carrier } →  x ∙ ⟦ ε ⟧ ≈ x
           qid1 {x} = begin
             x ∙ ⟦ ε ⟧ ≈⟨ ∙-cong grefl ε-homo ⟩
             x ∙ ε  ≈⟨ proj₂ identity _ ⟩
             x ∎
       qassoc : (f g h : aN N) → ⟦ n ( qadd (qadd f g) h) ⟧ ≈  ⟦ n( qadd f (qadd g h)) ⟧
       qassoc f g h = ⟦⟧-cong (assoc  _ _ _ )
       i-conv : {x y : aN N} → ⟦ n x ⟧ ≈ ⟦ n y ⟧ →  ⟦ n x ⁻¹ ⟧ ≈ ⟦ n y ⁻¹ ⟧ 
       i-conv {x} {y} nx=ny = begin
          ⟦ n x ⁻¹ ⟧ ≈⟨ ⁻¹-homo _ ⟩
          ⟦ n x ⟧ ⁻¹  ≈⟨ ⁻¹-cong nx=ny ⟩
          ⟦ n y ⟧ ⁻¹  ≈⟨ gsym ( ⁻¹-homo _)  ⟩
          ⟦ n y ⁻¹ ⟧  ∎


-- K ⊂ ker(f)
K⊆ker : (G H : Group c c)  (K : NormalSubGroup G) (f : Group.Carrier G → Group.Carrier H ) → Set c
K⊆ker G H K f = (x : Group.Carrier G ) → f ( ⟦ x ⟧ ) ≈ ε   where
  open Group H
  open NormalSubGroup K

open import Function.Surjection
open import Function.Equality

module GK (G : Group c c) (K : NormalSubGroup G) where
    open Group G
    open aN
    open an
    open NormalSubGroup K
    open IsGroupHomomorphism normal
    open EqReasoning (Algebra.Group.setoid G)
    open Gutil G

    φ : Group.Carrier G → Group.Carrier (G / K )
    φ g = record { n = g ; is-an = λ x → record { a = x ∙ ( ⟦ g ⟧ ⁻¹)   ; aN=x = gk02  } } where
       gk02 : {x : Carrier } →  x ∙ ⟦ g ⟧ ⁻¹ ∙ ⟦ g ⟧ ≈ x
       gk02 {x} = begin  x ∙ ⟦ g ⟧ ⁻¹ ∙ ⟦ g ⟧ ≈⟨ solve monoid  ⟩ 
         x ∙  ( ⟦ g ⟧ ⁻¹ ∙ ⟦ g ⟧)  ≈⟨ ∙-cong grefl (proj₁ inverse _ ) ⟩ 
         x ∙ ε  ≈⟨ proj₂ identity _  ⟩ 
         x ∎

    φ-homo : IsGroupHomomorphism (GR G) (GR (G / K)) φ
    φ-homo = record {⁻¹-homo = λ g → ?  ; isMonoidHomomorphism = record { ε-homo = ? ; isMagmaHomomorphism = record { homo = ? ; isRelHomomorphism =
       record { cong = ? } }}}

    -- gk03 : {f : Group.Carrier (G / K) } → ⟦ n f  ⟧ ≈ ⟦ ⟦ n f ⟧ ⟧  -- a (is-an f x)  ∙ ⟦ n f ⟧ ≡ x
    -- gk03 {x} = ?                                                   --  

    φe : (Algebra.Group.setoid G)  Function.Equality.⟶ (Algebra.Group.setoid (G / K))
    φe = record { _⟨$⟩_ = φ ; cong = ?  }  where
           φ-cong : {f g : Carrier } → f ≈ g  → ⟦ n (φ f ) ⟧ ≈ ⟦ n (φ g ) ⟧
           φ-cong = ?

    inv-φ : Group.Carrier (G / K ) → Group.Carrier G
    inv-φ f =  n f    -- ⟦ n f ⟧ ( if we have gk03 )

    cong-i : {f g : Group.Carrier (G / K ) } → ⟦ n f ⟧ ≈ ⟦ n g ⟧ → inv-φ f ≈ inv-φ g
    cong-i {f} {g} nf=ng = ? 

    is-inverse : (f : aN K  ) →  ⟦ n (φ (inv-φ f) ) ⟧ ≈ ⟦ n f ⟧
    is-inverse f = begin
       ⟦ n (φ (inv-φ f) ) ⟧  ≈⟨ grefl  ⟩
       ⟦ n (φ ( n f  ) ) ⟧  ≈⟨ grefl  ⟩
       ⟦ n f ⟧ ∎

    φ-surjective : Surjective φe
    φ-surjective = record { from = record { _⟨$⟩_ = inv-φ ; cong = λ {f} {g} → cong-i {f} {g} }  ; right-inverse-of = is-inverse }

    gk01 : (x : Group.Carrier (G / K ) ) → (G / K) < φ ( inv-φ x ) ≈ x >
    gk01 x = begin
        ⟦ inv-φ x ⟧  ≈⟨ grefl ⟩ 
        ⟦ n x ⟧ ∎


record FundamentalHomomorphism (G H : Group c c )
    (f : Group.Carrier G → Group.Carrier H )
    (homo : IsGroupHomomorphism (GR G) (GR H) f )
    (K : NormalSubGroup G ) (kf : K⊆ker G H K f) :  Set c where
  open Group H
  open GK G K
  field
    h : Group.Carrier (G / K ) → Group.Carrier H
    h-homo :  IsGroupHomomorphism (GR (G / K) ) (GR H) h
    is-solution : (x : Group.Carrier G)  →  f x ≈ h ( φ x )
    unique : (h1 : Group.Carrier (G / K ) → Group.Carrier H)  → (homo : IsGroupHomomorphism (GR (G / K)) (GR H) h1 )
       → ( (x : Group.Carrier G)  →  f x ≈ h1 ( φ x ) ) → ( ( x : Group.Carrier (G / K)) → h x ≈ h1 x )

FundamentalHomomorphismTheorm : (G H : Group c c)
    (f : Group.Carrier G → Group.Carrier H )
    (homo : IsGroupHomomorphism (GR G) (GR H) f )
    (K : NormalSubGroup G ) → (kf : K⊆ker G H K f)   → FundamentalHomomorphism G H f homo K kf
FundamentalHomomorphismTheorm G H f homo K kf = record {
     h = h
   ; h-homo = h-homo
   ; is-solution = is-solution
   ; unique = unique
  } where
    open GK G K
    open Group H
    open Gutil H
    open NormalSubGroup K
    open IsGroupHomomorphism homo
    open aN
    h : Group.Carrier (G / K ) → Group.Carrier H
    h r = f ( inv-φ r )
    h03 : (x y : Group.Carrier (G / K ) ) →  h ( (G / K) < x ∙ y > ) ≈ h x ∙ h y
    h03 x y = {!!}
    h-homo :  IsGroupHomomorphism (GR (G / K ) ) (GR H) h
    h-homo = record {
     isMonoidHomomorphism = record {
          isMagmaHomomorphism = record {
             isRelHomomorphism = record { cong = λ {x} {y} eq → {!!} }
           ; homo = h03 }
        ; ε-homo = {!!} }
       ; ⁻¹-homo = {!!} }
    open EqReasoning (Algebra.Group.setoid H)
    is-solution : (x : Group.Carrier G)  →  f x ≈ h ( φ x )
    is-solution x = begin
         f x ≈⟨ grefl  ⟩
         h ( φ x ) ∎ 
    unique : (h1 : Group.Carrier (G / K ) → Group.Carrier H)  → (h1-homo : IsGroupHomomorphism (GR (G / K)) (GR H) h1 )
       → ( (x : Group.Carrier G)  →  f x ≈ h1 ( φ x ) ) → ( ( x : Group.Carrier (G / K)) → h x ≈ h1 x )
    unique h1 h1-homo h1-is-solution x = begin
         h x ≈⟨ grefl ⟩
         f ( inv-φ x ) ≈⟨ h1-is-solution _ ⟩
         h1 ( φ ( inv-φ x ) ) ≈⟨ IsGroupHomomorphism.⟦⟧-cong h1-homo (gk01 x)  ⟩
         h1 x ∎






