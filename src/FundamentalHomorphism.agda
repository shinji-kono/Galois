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

import Axiom.Extensionality.Propositional
postulate f-extensionality : { n m : Level}  → Axiom.Extensionality.Propositional.Extensionality n m
open import Tactic.MonoidSolver using (solve; solve-macro)


record NormalSubGroup (A : Group c c )  : Set c  where
   open Group A
   field
       ⟦_⟧ : Group.Carrier A → Group.Carrier A
       normal :  IsGroupHomomorphism (GR A) (GR A)  ⟦_⟧
       comm : {a b :  Carrier } → b ∙ ⟦ a ⟧  ≈ ⟦ a ⟧  ∙ b
       --
       factor : (a b : Carrier) → Carrier
       is-factor : (a b : Carrier) →  b ∙ ⟦ factor a b ⟧ ≈ a

-- Set of a ∙ ∃ n ∈ N
--
record an {A : Group c c }  (N : NormalSubGroup A ) (n x : Group.Carrier A  ) : Set c where
    open Group A
    open NormalSubGroup N
    field
        a : Group.Carrier A
        aN=x :  a ∙ ⟦ n ⟧ ≈ x

record aN {A : Group c c }  (N : NormalSubGroup A )  : Set c where
    field
        n : Group.Carrier A
        is-an : (x : Group.Carrier A) → an N n x

qid : {A : Group c c }  (N : NormalSubGroup A )  → aN N
qid {A} N = record { n = ε ; is-an = λ x → record { a = x ; aN=x = ? } } where
       open Group A
       open NormalSubGroup N

_/_ : (A : Group c c ) (N  : NormalSubGroup A ) → Group c c
_/_ A N  = record {
    Carrier  = aN N
    ; _≈_      = λ f g → ⟦ n f ⟧ ≈ ⟦ n g ⟧
    ; _∙_      = qadd
    ; ε        = qid N
    ; _⁻¹      = ?
    ; isGroup = record { isMonoid  = record { isSemigroup = record { isMagma = record {
       isEquivalence = record {refl = grefl ; trans = gtrans ; sym = gsym }
       ; ∙-cong = λ {x} {y} {u} {v} x=y u=v → ? }
       ; assoc = ? }
       ; identity =  ? , (λ q → ? )  }
       ; inverse   = ( (λ x → ? ) , (λ x → ? ))
       ; ⁻¹-cong   = λ i=j → ?
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
              x ⁻¹ ∙ (a (is-an f x) ∙ a (is-an g x)) ∙ ⟦ n f ∙ n g ⟧ ≈⟨ ? ⟩
              x ⁻¹ ∙  (a (is-an f x) ∙ a (is-an g x) ∙ ⟦ n f ∙ n g ⟧) ≈⟨ ? ⟩
              x ⁻¹ ∙  (a (is-an f x) ∙ a (is-an g x) ∙ ( ⟦ n f ⟧  ∙ ⟦ n g ⟧ )) ≈⟨ ? ⟩
              x ⁻¹ ∙  (a (is-an f x) ∙ ( a (is-an g x) ∙  ⟦ n f ⟧)  ∙ ⟦ n g ⟧)  ≈⟨ ? ⟩
              x ⁻¹ ∙  (a (is-an f x) ∙ ( ⟦ n f ⟧ ∙ a (is-an g x) )  ∙ ⟦ n g ⟧)  ≈⟨ ? ⟩
              x ⁻¹ ∙  ((a (is-an f x) ∙ ⟦ n f ⟧ ) ∙ ( a (is-an g x)   ∙ ⟦ n g ⟧))  ≈⟨ ? ⟩
              x ⁻¹ ∙  ((a (is-an f x) ∙ ⟦ n f ⟧ ) ∙ ( a (is-an g x)   ∙ ⟦ n g ⟧))  ≈⟨ ? ⟩
              x ⁻¹ ∙  (x ∙ x)  ≈⟨ ? ⟩
             x ∎

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
    φ g = record { n = factor ε g ; is-an = λ x → record { a = x ∙ ( ⟦ factor ε g ⟧ ⁻¹)   ; aN=x = ?  } }

    φ-homo : IsGroupHomomorphism (GR G) (GR (G / K)) φ
    φ-homo = record {⁻¹-homo = λ g → ?  ; isMonoidHomomorphism = record { ε-homo = ? ; isMagmaHomomorphism = record { homo = ? ; isRelHomomorphism =
       record { cong = ? } }}}

    φe : (Algebra.Group.setoid G)  Function.Equality.⟶ (Algebra.Group.setoid (G / K))
    φe = record { _⟨$⟩_ = φ ; cong = ?  }  where
           φ-cong : {f g : Carrier } → f ≈ g  → ⟦ n (φ f ) ⟧ ≈ ⟦ n (φ g ) ⟧
           φ-cong = ?

    -- inverse ofφ
    --  f = λ x → record { a = af ; n = fn ; aN=x = x ≈ af ∙ ⟦ fn ⟧  )   = (af)K  , fn ≡ factor x af , af ≡ a (f x)
    --        (inv-φ f)K ≡ (af)K
    --           φ (inv-φ f) x → f (h0 x)
    --           f x → φ (inv-φ f) (h1 x)

    inv-φ : Group.Carrier (G / K ) → Group.Carrier G
    inv-φ f = ⟦ n f ⟧ ⁻¹


    cong-i : {f g : Group.Carrier (G / K ) } → ⟦ n f ⟧ ≈ ⟦ n g ⟧ → inv-φ f ≈ inv-φ g
    cong-i = ?

    is-inverse : (f : aN K  ) →  ⟦ n (φ (inv-φ f) ) ⟧ ≈ ⟦ n f ⟧
    is-inverse f = begin
       ⟦ n (φ (inv-φ f) ) ⟧  ≈⟨ grefl  ⟩
       ⟦ n (φ (⟦ n f  ⟧ ⁻¹) ) ⟧  ≈⟨ grefl  ⟩
       ⟦ factor ε (⟦ n f  ⟧ ⁻¹) ⟧  ≈⟨ ? ⟩
       ( ⟦ n f ⟧ ∙ ⟦ n f  ⟧ ⁻¹) ∙  ⟦ factor ε (⟦ n f  ⟧ ⁻¹) ⟧  ≈⟨ ? ⟩
       ⟦ n f ⟧ ∙ ( ⟦ n f  ⟧ ⁻¹ ∙  ⟦ factor ε (⟦ n f  ⟧ ⁻¹) ⟧ ) ≈⟨ ∙-cong grefl (is-factor ε _ ) ⟩
       ⟦ n f ⟧ ∙ ε  ≈⟨ ? ⟩
       ⟦ n f ⟧ ∎

    φ-surjective : Surjective φe
    φ-surjective = record { from = record { _⟨$⟩_ = inv-φ ; cong = λ {f} {g} → cong-i {f} {g} }  ; right-inverse-of = is-inverse }

    gk00 : {x : Carrier } → ⟦ factor ε x ⟧ ⁻¹ ≈ x
    gk00 {x} = begin
        ⟦ factor ε x ⟧ ⁻¹ ≈⟨ ? ⟩ 
        ( x ⁻¹ ∙ ( x ∙ ⟦ factor ε x ⟧) ) ⁻¹ ≈⟨ ? ⟩ 
        ( x ⁻¹ ∙ ( x ∙ ⟦ factor ε x ⟧) ) ⁻¹ ≈⟨ ⁻¹-cong (∙-cong grefl (is-factor ε x))  ⟩ 
        ( x ⁻¹ ∙ ε ) ⁻¹ ≈⟨ ? ⟩ 
        ( x ⁻¹  ) ⁻¹ ≈⟨ ? ⟩ 
        x ∎

    gk01 : (x : Group.Carrier (G / K ) ) → (G / K) < φ ( inv-φ x ) ≈ x >
    gk01 x = begin
        ⟦ factor ε ( inv-φ x) ⟧  ≈⟨ ? ⟩ 
        ( inv-φ x ) ⁻¹ ∙ ( inv-φ x ∙ ⟦ factor ε ( inv-φ x) ⟧)  ≈⟨ ∙-cong grefl (is-factor ε _ ) ⟩ 
        ( inv-φ x ) ⁻¹ ∙ ε  ≈⟨ ? ⟩ 
        ( ⟦ n x ⟧  ⁻¹) ⁻¹   ≈⟨ ? ⟩ 
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
         f x ≈⟨ gsym ( ⟦⟧-cong (gk00 ))  ⟩
         f ( Group._⁻¹ G  ⟦ factor (Group.ε G) x  ⟧   ) ≈⟨ grefl  ⟩
         h ( φ x ) ∎ 
    unique : (h1 : Group.Carrier (G / K ) → Group.Carrier H)  → (h1-homo : IsGroupHomomorphism (GR (G / K)) (GR H) h1 )
       → ( (x : Group.Carrier G)  →  f x ≈ h1 ( φ x ) ) → ( ( x : Group.Carrier (G / K)) → h x ≈ h1 x )
    unique h1 h1-homo h1-is-solution x = begin
         h x ≈⟨ grefl ⟩
         f ( inv-φ x ) ≈⟨ h1-is-solution _ ⟩
         h1 ( φ ( inv-φ x ) ) ≈⟨ IsGroupHomomorphism.⟦⟧-cong h1-homo (gk01 x)  ⟩
         h1 x ∎






