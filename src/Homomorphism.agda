{-# OPTIONS --allow-unsolved-metas #-}

-- fundamental homomorphism theorem
--

module Homomorphism where

open import Level hiding ( suc ; zero )
open import Algebra
open import Algebra.Structures
open import Algebra.Definitions
open import Algebra.Core
open import Algebra.Bundles

open import Data.Product
open import Relation.Binary.PropositionalEquality
open import NormalSubgroup
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
-- In our case G and G / K has the same carrier set, so φ is the identity function and f = h.
-- What we need to prove is that G / K is a Group and h has congruence.
--    (x y : Carrier (G / K ) → x ≈ y → h x ≈ h y

import Relation.Binary.Reasoning.Setoid as EqReasoning

open GroupMorphisms

-- Set of a ∙ ∃ n ∈ N
--

data IsaN  {c d : Level} {A : Group c d }  (N : NormalSubGroup {d} A) (a : Group.Carrier A ) : (x : Group.Carrier A ) → Set (Level.suc c ⊔ d) where
    an : (n x : Group.Carrier A ) →  A < A < a ∙ n > ≈ x > → (pn : NormalSubGroup.P N n) → IsaN N a x

record aNeq {c d : Level} {A : Group c d }  (N : NormalSubGroup A )  (a b : Group.Carrier A)  : Set (Level.suc c ⊔ d) where
    field
        eq→  : {x : Group.Carrier A}  → IsaN N a x → IsaN N b x
        eq←  : {x : Group.Carrier A}  → IsaN N b x → IsaN N a x

module AN {c d : Level} (A : Group c d) (N : NormalSubGroup {d} A  ) where
    open Group A
    open NormalSubGroup N
    open EqReasoning (Algebra.Group.setoid A)
    open Gutil A
    open aNeq
    --
    -- (aN)(bN) = a(Nb)N = a(bN)N = (ab)NN = (ab)N.
    --
    -- a =n= b ↔ a . b ⁻¹ ∈ N
    a=b→ab⁻¹∈N : {a b : Carrier} → (a=b : aNeq N a b) → P (a ∙ b ⁻¹) 
    a=b→ab⁻¹∈N {a} {b} a=b with eq→ a=b (an ε a (proj₂ identity _) Pε)
    ... | an n .a bn=a pn = P≈ an06 (Pcomm {n} {b} pn ) where
        an06 : b ∙ (n ∙ b ⁻¹) ≈ a ∙ b ⁻¹
        an06 =  begin 
           b ∙ (n ∙ b ⁻¹) ≈⟨ solve monoid ⟩ 
           (b ∙ n ) ∙ b ⁻¹ ≈⟨ car bn=a ⟩ 
           a ∙ b ⁻¹ ∎
    ab⁻¹∈N→a=b : {a b : Carrier} → P (a ∙ b ⁻¹) → aNeq N a b
    ab⁻¹∈N→a=b {a} {b} parb = record { eq→ = an07 ; eq← = an09 } where
        an07 : {x : Carrier} → IsaN N a x → IsaN N b x
        an07 {x} (an n x eq pn) = an _ x an08 (P∙ (Pcomm parb) pn ) where
            an08 : b ∙ (( b ⁻¹ ∙ ((a ∙ b ⁻¹ ) ∙ b ⁻¹ ⁻¹ ))∙ n )  ≈ x
            an08 = begin
                b ∙ (( b ⁻¹ ∙ ((a ∙ b ⁻¹ ) ∙ b ⁻¹ ⁻¹ ))∙ n )  ≈⟨ solve monoid ⟩
                b ∙ (( b ⁻¹ ∙ (a ∙ (b ⁻¹  ∙ b ⁻¹ ⁻¹ ))) ∙ n )  ≈⟨ cdr (car (cdr (cdr (proj₂ inverse _)))) ⟩
                b ∙ (( b ⁻¹ ∙ (a ∙ ε)) ∙ n )  ≈⟨ solve monoid ⟩
                (b ∙ b ⁻¹ ) ∙ (a ∙ n) ≈⟨ car ( proj₂  inverse _) ⟩
                ε ∙ (a ∙ n) ≈⟨ proj₁ identity _ ⟩
                a ∙ n  ≈⟨ eq  ⟩
                x ∎
        an09 : {x : Carrier} → IsaN N b x → IsaN N a x
        an09 {x} (an n x eq pn) = an _ x an10 (P∙ (Pcomm (P⁻¹ _ parb)) pn ) where
            an10 : a ∙ (( a ⁻¹ ∙ ((a ∙ b ⁻¹ ) ⁻¹  ∙ a ⁻¹ ⁻¹ ))∙ n ) ≈ x
            an10 = begin
                a ∙ (( a ⁻¹ ∙ ((a ∙ b ⁻¹ ) ⁻¹  ∙ a ⁻¹ ⁻¹ ))∙ n )  ≈⟨ cdr (car (cdr (car (gsym (lemma5 _ _))))) ⟩
                a ∙ (( a ⁻¹ ∙ ((b ⁻¹ ⁻¹  ∙ a ⁻¹ )   ∙ a ⁻¹ ⁻¹ ))∙ n )  ≈⟨ cdr (car (cdr (car (car f⁻¹⁻¹≈f )))) ⟩
                a ∙ (( a ⁻¹ ∙ ((b ∙ a ⁻¹ ) ∙ a ⁻¹ ⁻¹ ))∙ n )  ≈⟨ solve monoid ⟩
                a ∙ (( a ⁻¹ ∙ (b ∙ (a ⁻¹  ∙ a ⁻¹ ⁻¹ ))) ∙ n )  ≈⟨ cdr (car (cdr (cdr (proj₂ inverse _)))) ⟩
                a ∙ (( a ⁻¹ ∙ (b ∙ ε)) ∙ n )  ≈⟨ solve monoid ⟩
                (a ∙ a ⁻¹ ) ∙ (b ∙ n) ≈⟨ car ( proj₂  inverse _) ⟩
                ε ∙ (b ∙ n) ≈⟨ proj₁ identity _ ⟩
                b ∙ n  ≈⟨ eq  ⟩
                x ∎

    an-cong : {a b x : Carrier } → a ≈ b → IsaN N a x → IsaN N b x
    an-cong {a} {b} {x} eq (an n _ eq1 pn) = an n _ an04 pn where
        an04 : b ∙ n  ≈ x
        an04 = begin
           b ∙ n ≈⟨ car (gsym eq) ⟩
           a ∙ n ≈⟨ eq1 ⟩
           x ∎
    aneq : {a b : Carrier } → a ≈ b → aNeq N a b
    aneq {a} {b} eq = record { eq→ = λ {x} lt → an-cong eq lt ; eq← = λ lt → an-cong (gsym eq) lt }   
    _=n=_ = aNeq N

    nrefl :  {x : Carrier} → x =n= x
    nrefl {x} = record { eq→ = λ {lt} ix → ix ; eq← =  λ {lt} ix → ix }
    nsym : {x y  : Carrier} → x =n= y → y =n= x
    nsym {x} {y} eq = record { eq→ = λ {lt} ix → eq← eq ix ; eq← =  λ {lt} ix → eq→ eq ix }
    ntrans : {x y  z : Carrier} → x =n= y → y =n= z → x =n= z
    ntrans {x} {y} {z} x=y y=z = record { eq→ = λ {lt} ix → eq→ y=z (eq→ x=y ix) 
         ; eq← =  λ {lt} ix → eq← x=y (eq← y=z ix) }

_/_ : {c d : Level} (A : Group c d ) (N  : NormalSubGroup A ) → Group c (Level.suc c ⊔ d) 
_/_ A N  = record {
    Carrier  = Group.Carrier A
    ; _≈_      = aNeq N
    ; _∙_      = _∙_
    ; ε        = ε
    ; _⁻¹      = λ x → x ⁻¹
    ; isGroup = record { isMonoid  = record { isSemigroup = record { isMagma = record {
       isEquivalence = record {refl = nrefl
           ; trans = ntrans ; sym = λ a=b → nsym a=b 
          }
       ; ∙-cong = λ {x} {y} {u} {v} x=y u=v → gk00 x=y u=v }
       ; assoc = gkassoc }
       ; identity =  (λ a → aneq (proj₁ identity _)) , (λ a → aneq (proj₂ identity _) )  }
       ; inverse   =  (λ a → aneq (proj₁ inverse _)) , (λ x → aneq (proj₂ inverse _) ) 
       ; ⁻¹-cong   = gkcong⁻¹
      }
   } where
       _=n=_ = aNeq N
       open Group A
       open NormalSubGroup N
       open EqReasoning (Algebra.Group.setoid A)
       open Gutil A
       open AN A N
       open aNeq 
       gk00 : {x y u v : Carrier } → aNeq N x y → aNeq N u v → aNeq N (x ∙ u) (y ∙ v)
       gk00 {x} {y} {u} {v} x=y u=v = gk08 where
           gk09 : (x ∙ y ⁻¹ ) ∙ (y  ∙ ((u ∙ v ⁻¹) ∙ y ⁻¹ ))  ≈ x ∙ u ∙ (y ∙ v) ⁻¹
           gk09 = begin
               (x ∙ y ⁻¹ ) ∙ (y  ∙ ((u ∙ v ⁻¹) ∙ y ⁻¹ )) ≈⟨ solve monoid ⟩
               x ∙ y ⁻¹ ∙ (y  ∙ (u ∙ (v ⁻¹ ∙  y ⁻¹ ))) ≈⟨ cdr (cdr (cdr ((lemma5 _ _)))) ⟩
               x ∙ y ⁻¹ ∙ (y  ∙ (u ∙ (y ∙ v) ⁻¹ )) ≈⟨ solve monoid ⟩
               x ∙ ((y ⁻¹ ∙ y ) ∙ (u ∙ (y ∙ v) ⁻¹)) ≈⟨ cdr (car (proj₁ inverse _) ) ⟩
               x ∙ (ε ∙ (u ∙ (y ∙ v) ⁻¹)) ≈⟨ solve monoid ⟩
               x ∙ u ∙ (y ∙ v) ⁻¹ ∎ 
           gk08 : aNeq N (x ∙ u) (y ∙ v)
           gk08 = ab⁻¹∈N→a=b (P≈ gk09 (P∙ (a=b→ab⁻¹∈N x=y) (Pcomm (a=b→ab⁻¹∈N u=v)) ))
       gkassoc : (x y z : Carrier ) → aNeq N ((x ∙ y ) ∙ z) (x ∙ (y ∙ z))
       gkassoc x y z = aneq (solve monoid) 
       gkcong⁻¹ : {x y : Carrier } → aNeq N x y → aNeq N (x ⁻¹) (y ⁻¹) 
       gkcong⁻¹ {x} {y} x=y  = ab⁻¹∈N→a=b (P≈ gk09 (Pcomm {_} {y ⁻¹ } (P⁻¹ _ ( a=b→ab⁻¹∈N x=y)))) where
          gk09 :  y ⁻¹ ∙ ((x ∙ y ⁻¹) ⁻¹ ∙ (y ⁻¹) ⁻¹) ≈ x ⁻¹ ∙ (y ⁻¹) ⁻¹
          gk09 = begin
              y ⁻¹ ∙ ((x ∙ y ⁻¹) ⁻¹ ∙ (y ⁻¹) ⁻¹) ≈⟨ cdr (car (gsym (lemma5 _ _)))  ⟩
              y ⁻¹ ∙ ((y ⁻¹ ⁻¹ ∙ x ⁻¹ ) ∙ (y ⁻¹) ⁻¹) ≈⟨ solve monoid ⟩
              (y ⁻¹ ∙ y ⁻¹ ⁻¹ ) ∙ ( x ⁻¹  ∙ (y ⁻¹) ⁻¹) ≈⟨ car (proj₂ inverse _) ⟩
              ε ∙ ( x ⁻¹  ∙ (y ⁻¹) ⁻¹) ≈⟨ solve monoid ⟩
              x ⁻¹ ∙ (y ⁻¹) ⁻¹ ∎

-- K ⊆ ker(f)
K⊆ker : {c d : Level} (G H : Group c d)  (K : NormalSubGroup {d} G ) (f : Group.Carrier G → Group.Carrier H ) 
   → Set (c ⊔ d)
K⊆ker G H K f = (x : Group.Carrier G ) → P x → f x ≈ ε   where
  open Group H
  open NormalSubGroup K

Ker : {c d : Level} (G H : Group c d)
    {f : Group.Carrier G → Group.Carrier H }
    (f-homo : IsGroupHomomorphism (GR G) (GR H) f ) →  NormalSubGroup {d} G 
Ker {c} {d} G H {f} f-homo = record {
          P = λ x → f x ≈ ε
        ; Pε = ε-homo 
        ; P⁻¹ = im01
        ; P≈ = im02
        ; P∙ = im03
        ; Pcomm = im04
       } where
    open Group H
    open Gutil H
    open IsGroupHomomorphism f-homo
    open EqReasoning (Algebra.Group.setoid H)

    GC = Group.Carrier G
    im01 : (a : Group.Carrier G) → f a ≈ ε → f ((G Group.⁻¹) a) ≈ ε
    im01 a fa=e = begin
        f ((G Group.⁻¹) a) ≈⟨ ⁻¹-homo _  ⟩
        f a ⁻¹  ≈⟨ ⁻¹-cong fa=e ⟩
        ε ⁻¹  ≈⟨ gsym ε≈ε⁻¹ ⟩
        ε ∎  
    im02 : {a b : GC} → G < a ≈ b > → f a ≈ ε → f b ≈ ε
    im02 {a} {b} a=b fa=e = begin
       f b ≈⟨ ⟦⟧-cong (GU.gsym a=b) ⟩
       f a ≈⟨ fa=e  ⟩
       ε ∎  where
        open import Gutil G as GU
    im04 :  {a b : Group.Carrier G} → f a ≈ ε → 
         f ((G Group.∙ b) ((G Group.∙ a) ((G Group.⁻¹) b))) ≈ ε
    im04 {a} {b} fa=e = begin
        f ( G < b ∙ G < a ∙ (G Group.⁻¹) b > > ) ≈⟨ homo _ _ ⟩
        f  b ∙ f ( G < a ∙ (G Group.⁻¹) b >  ) ≈⟨ cdr (homo _ _) ⟩
        f  b ∙ ( f a ∙ f ((G Group.⁻¹) b )) ≈⟨ cdr (cdr (⁻¹-homo _))  ⟩
        f  b ∙ ( f a ∙ f b ⁻¹ ) ≈⟨ cdr (car fa=e) ⟩
        f  b ∙ ( ε ∙ f b ⁻¹ ) ≈⟨ solve monoid ⟩
        f  b ∙ f b ⁻¹ ≈⟨ proj₂ inverse _ ⟩
        ε ∎  
    im03 : {a b : Group.Carrier G} → f a ≈ ε → f b ≈ ε →
         f ((G Group.∙ a) b) ≈ ε
    im03 {a} {b} fa=e fb=e = begin
       f (G < a ∙ b > ) ≈⟨ homo _ _ ⟩
       f a ∙ f b  ≈⟨ ∙-cong fa=e fb=e ⟩
       ε ∙ ε  ≈⟨ proj₁ identity _ ⟩
       ε ∎ 

Im : {c d : Level} (G  : Group c d) {H : Group c d}
    {f : Group.Carrier G → Group.Carrier H }
    (f-homo : IsGroupHomomorphism (GR G) (GR H) f ) →  Group _ _
Im G {H} {f} f-homo = G / Ker G H f-homo

module GK {c d : Level} (G : Group c d) (K : NormalSubGroup G  ) where
    φ : Group.Carrier G → Group.Carrier (G / K )  -- a → aN
    φ g = g

record FundamentalHomomorphism {c d : Level} (G H : Group c d )
    (f : Group.Carrier G → Group.Carrier H )
    (homo : IsGroupHomomorphism (GR G) (GR H) f )
    (K : NormalSubGroup G  ) (kf : K⊆ker G H K f)  :  Set (Level.suc c ⊔ d) where
  open Group H
  open GK G K 
  field
    h : Group.Carrier (G / K ) → Group.Carrier H
    h-homo :  IsGroupHomomorphism (GR (G / K) ) (GR H) h
    is-solution : (x : Group.Carrier G)  →  f x ≈ h ( φ x )
    unique : (h1 : Group.Carrier (G / K ) → Group.Carrier H)  → (homo : IsGroupHomomorphism (GR (G / K)) (GR H) h1 )
       → ( (x : Group.Carrier G)  →  f x ≈ h1 ( φ x )) → (( x : Group.Carrier (G / K)) → h x ≈ h1 x )

FundamentalHomomorphismTheorm : {c d : Level} (G H : Group c d)
    (f : Group.Carrier G → Group.Carrier H )
    (f-homo : IsGroupHomomorphism (GR G) (GR H) f )
    (K : NormalSubGroup G  ) → (kf : K⊆ker G H K f) → FundamentalHomomorphism G H f f-homo K kf 
FundamentalHomomorphismTheorm {c} {d} G H f f-homo K kf = record {
     h = h
   ; h-homo = h-homo
   ; is-solution = is-solution
   ; unique = unique
  } where
    open GK G K 
    open Group H
    open Gutil H
    open IsGroupHomomorphism f-homo
    open EqReasoning (Algebra.Group.setoid H)


    h : Group.Carrier (G / K ) → Group.Carrier H
    h r = f r
    h03 : (x y : Group.Carrier (G / K ) ) →  h ( (G / K) < x ∙ y > ) ≈ h x ∙ h y
    h03 x y = homo _ _
    h04 : {x y : Group.Carrier G} → aNeq K x y → h x ≈ h y 
    h04 {x} {y} x=y = h20  where
        h20 : h x ≈ h y
        h20 = begin 
           h x ≈⟨ gsym (proj₂ identity _) ⟩
           h x ∙ ε ≈⟨ cdr (gsym (proj₁ inverse _)) ⟩
           h x ∙ ((h y) ⁻¹ ∙ h y) ≈⟨ solve monoid ⟩
           (h x ∙ (h y) ⁻¹ ) ∙ h y ≈⟨ gsym (car (cdr (⁻¹-homo _ ))) ⟩
           (h x ∙ h (Group._⁻¹ G y ))  ∙ h y ≈⟨ gsym (car (homo _ _)) ⟩
           h (G < x ∙ (Group._⁻¹ G y ) > ) ∙ h y  ≈⟨ car ( kf _ (AN.a=b→ab⁻¹∈N G K x=y )) ⟩ 
           ε ∙ h y  ≈⟨ proj₁ identity _ ⟩ 
           h y   ∎ 
    h-homo :  IsGroupHomomorphism (GR (G / K ) ) (GR H) h
    h-homo = record {    -- this is essentially f-homo except cong
     isMonoidHomomorphism = record {
          isMagmaHomomorphism = record {
             isRelHomomorphism = record { cong = λ {x} {y} eq → h04 eq  }
           ; homo = h03 }
        ; ε-homo = ε-homo }
       ; ⁻¹-homo = ⁻¹-homo }
    is-solution : (x : Group.Carrier G)  →  f x ≈ h ( φ x )
    is-solution x = begin
         f x ≈⟨ grefl ⟩
         h ( φ x ) ∎ 
    unique : (h1 : Group.Carrier (G / K ) → Group.Carrier H)  → (h1-homo : IsGroupHomomorphism (GR (G / K)) (GR H) h1 )
       → ( (x : Group.Carrier G)  →  f x ≈ h1 ( φ x ) ) → ( ( x : Group.Carrier (G / K)) → h x ≈ h1 x )
    unique h1 h1-homo h1-is-solution x = begin
         h x ≈⟨ grefl ⟩
         f x ≈⟨ h1-is-solution _ ⟩
         h1 x ∎ 
-- 
-- Fundamental Homomorphism Theorm on G / Imf f gives another form of Fundamental Homomorphism Theorm
--    i.e.  G / Ker f ≈ Im f





