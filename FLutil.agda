module FLutil where

open import Level hiding ( suc ; zero )
open import Data.Fin hiding ( _<_  ; _≤_ ; _-_ ; _+_ ; _≟_)
open import Data.Fin.Properties hiding ( <-trans ; ≤-trans ; ≤-irrelevant ; _≟_ ) renaming ( <-cmp to <-fcmp )
open import Data.Fin.Permutation
open import Data.Nat -- using (ℕ; suc; zero; s≤s ; z≤n )
open import Relation.Binary.PropositionalEquality 
open import Data.List using (List; []; _∷_ ; length ; _++_ ; head ; tail ) renaming (reverse to rev )
open import Data.Product
open import Relation.Nullary
open import Data.Empty
open import  Relation.Binary.Core
open import  Relation.Binary.Definitions
open import logic
open import nat

infixr  100 _::_

data  FL : (n : ℕ )→ Set where
   f0 :  FL 0 
   _::_ :  { n : ℕ } → Fin (suc n ) → FL n → FL (suc n)

data _f<_  : {n : ℕ } (x : FL n ) (y : FL n)  → Set  where
   f<n : {m : ℕ } {xn yn : Fin (suc m) } {xt yt : FL m} → xn Data.Fin.< yn →   (xn :: xt) f< ( yn :: yt )
   f<t : {m : ℕ } {xn : Fin (suc m) } {xt yt : FL m} → xt f< yt →   (xn :: xt) f< ( xn :: yt )

FLeq : {n : ℕ } {xn yn : Fin (suc n)} {x : FL n } {y : FL n}  → xn :: x ≡ yn :: y → ( xn ≡ yn )  × (x ≡ y )
FLeq refl = refl , refl 

f-<> :  {n : ℕ } {x : FL n } {y : FL n}  → x f< y → y f< x → ⊥
f-<> (f<n x) (f<n x₁) = nat-<> x x₁
f-<> (f<n x) (f<t lt2) = nat-≡< refl x
f-<> (f<t lt) (f<n x) = nat-≡< refl x
f-<> (f<t lt) (f<t lt2) = f-<> lt lt2

f-≡< :  {n : ℕ } {x : FL n } {y : FL n}  → x ≡ y → y f< x → ⊥
f-≡< refl (f<n x) = nat-≡< refl x
f-≡< refl (f<t lt) = f-≡< refl lt 

FLcmp : {n : ℕ } → Trichotomous {Level.zero} {FL n}  _≡_  _f<_
FLcmp f0 f0 = tri≈ (λ ()) refl (λ ())
FLcmp (xn :: xt) (yn :: yt) with <-fcmp xn yn
... | tri< a ¬b ¬c = tri< (f<n a) (λ eq → nat-≡< (cong toℕ (proj₁ (FLeq eq)) ) a) (λ lt  → f-<> lt (f<n a) )
... | tri> ¬a ¬b c = tri> (λ lt  → f-<> lt (f<n c) ) (λ eq → nat-≡< (cong toℕ (sym (proj₁ (FLeq eq)) )) c) (f<n c)
... | tri≈ ¬a refl ¬c with FLcmp xt yt
... | tri< a ¬b ¬c₁ = tri< (f<t a) (λ eq → ¬b (proj₂ (FLeq eq) )) (λ lt  → f-<> lt (f<t a) )
... | tri≈ ¬a₁ refl ¬c₁ = tri≈ (λ lt → f-≡< refl lt )  refl (λ lt → f-≡< refl lt )
... | tri> ¬a₁ ¬b c = tri> (λ lt  → f-<> lt (f<t c) ) (λ eq → ¬b (proj₂ (FLeq eq) )) (f<t c)

f<-trans : {n : ℕ } { x y z : FL n } → x f< y → y f< z → x f< z
f<-trans {suc n} (f<n x) (f<n x₁) = f<n ( Data.Fin.Properties.<-trans x x₁ )
f<-trans {suc n} (f<n x) (f<t y<z) = f<n x
f<-trans {suc n} (f<t x<y) (f<n x) = f<n x
f<-trans {suc n} (f<t x<y) (f<t y<z) = f<t (f<-trans x<y y<z)

infixr 250 _f<?_

_f<?_ : {n  : ℕ} → (x y : FL n ) → Dec (x f< y )
x f<? y with FLcmp x y
... | tri< a ¬b ¬c = yes a
... | tri≈ ¬a refl ¬c = no ( ¬a )
... | tri> ¬a ¬b c = no ( ¬a )

_f≤_ : {n : ℕ } (x : FL n ) (y : FL n)  → Set
_f≤_ x y = (x ≡ y ) ∨  (x f< y )

FL0 : {n : ℕ } → FL n
FL0 {zero} = f0
FL0 {suc n} = zero :: FL0


fmax : { n : ℕ } →  FL n
fmax {zero} = f0
fmax {suc n} = fromℕ< a<sa :: fmax {n}

fmax< : { n : ℕ } → {x : FL n } → ¬ (fmax f< x )
fmax< {suc n} {x :: y} (f<n lt) = nat-≤> (fmax1 x) lt where
    fmax1 : {n : ℕ } → (x : Fin (suc n)) → toℕ x ≤ toℕ (fromℕ< {n} a<sa)
    fmax1 {zero} zero = z≤n
    fmax1 {suc n} zero = z≤n
    fmax1 {suc n} (suc x) = s≤s (fmax1 x) 
fmax< {suc n} {x :: y} (f<t lt) = fmax< {n} {y} lt

fmax¬ : { n : ℕ } → {x : FL n } → ¬ ( x ≡ fmax ) → x f< fmax
fmax¬ {zero} {f0} ne = ⊥-elim ( ne refl ) 
fmax¬ {suc n} {x} ne with FLcmp x fmax
... | tri< a ¬b ¬c = a
... | tri≈ ¬a b ¬c = ⊥-elim ( ne b)
... | tri> ¬a ¬b c = ⊥-elim (fmax< c)

FL0≤ : {n : ℕ } → FL0 {n} f≤ fmax
FL0≤ {zero} = case1 refl
FL0≤ {suc zero} = case1 refl
FL0≤ {suc n} with <-fcmp zero (fromℕ< {n} a<sa)
... | tri< a ¬b ¬c = case2 (f<n a)
... | tri≈ ¬a b ¬c with FL0≤ {n}
... | case1 x = case1 (subst₂ (λ j k → (zero :: FL0) ≡ (j :: k ) ) b x refl )
... | case2 x = case2 (subst (λ k →  (zero :: FL0) f< (k :: fmax)) b (f<t x)  )

open import Data.Nat.Properties using ( ≤-trans ; <-trans )
fsuc : { n : ℕ } → (x : FL n ) → x f< fmax → FL n 
fsuc {n} (x :: y) (f<n lt) = fromℕ< fsuc1 :: y where
    fsuc2 : toℕ x < toℕ (fromℕ< a<sa) 
    fsuc2 = lt
    fsuc1 : suc (toℕ x) < n
    fsuc1 =  Data.Nat.Properties.≤-trans (s≤s lt) ( s≤s ( toℕ≤pred[n] (fromℕ< a<sa)) )
fsuc (x :: y) (f<t lt) = x :: fsuc y lt

flist1 :  {n : ℕ } (i : ℕ) → i < suc n → List (FL n) → List (FL n) → List (FL (suc n)) 
flist1 zero i<n [] _ = []
flist1 zero i<n (a ∷ x ) z  = ( zero :: a ) ∷ flist1 zero i<n x z 
flist1 (suc i) (s≤s i<n) [] z  = flist1 i (Data.Nat.Properties.<-trans i<n a<sa) z z 
flist1 (suc i) i<n (a ∷ x ) z  = ((fromℕ< i<n ) :: a ) ∷ flist1 (suc i) i<n x z 

flist : {n : ℕ } → FL n → List (FL n) 
flist {zero} f0 = f0 ∷ [] 
flist {suc n} (x :: y)  = flist1 n a<sa (flist y) (flist y)   

fr22 : fsuc (zero :: zero :: f0) (fmax¬ (λ ())) ≡ (suc zero :: zero :: f0)
fr22 = refl

fr4 : List (FL 4)
fr4 = Data.List.reverse (flist (fmax {4}) )

-- fr5 : List (List ℕ)
-- fr5 = map plist (map FL→perm  (Data.List.reverse (flist (fmax {4}) )))


open import Relation.Binary as B hiding (Decidable; _⇔_)
open import Data.Sum.Base as Sum --  inj₁
open import Relation.Nary using (⌊_⌋)
open import Data.List.Fresh

FList : {n : ℕ } → Set
FList {n} = List# (FL n) ⌊ _f<?_ ⌋

fr1 : FList
fr1 =
   ((# 0) :: ((# 0) :: ((# 0 ) :: f0))) ∷# 
   ((# 0) :: ((# 1) :: ((# 0 ) :: f0))) ∷# 
   ((# 1) :: ((# 0) :: ((# 0 ) :: f0))) ∷# 
   ((# 2) :: ((# 0) :: ((# 0 ) :: f0))) ∷# 
   ((# 2) :: ((# 1) :: ((# 0 ) :: f0))) ∷# 
   []

open import Data.Product
open import Relation.Nullary.Decidable hiding (⌊_⌋)
open import Data.Bool hiding (_<_)
open import Data.Unit.Base using (⊤ ; tt)

--  fresh a []        = ⊤
--  fresh a (x ∷# xs) = R a x × fresh a xs

-- toWitness
-- ttf< :  {n : ℕ } → {x a : FL n } → x f< a  → T (isYes (x f<? a))
-- ttf< {n} {x} {a} x<a with x f<? a
-- ... | yes y = subst (λ k → Data.Bool.T k ) refl tt
-- ... | no nn = ⊥-elim ( nn x<a )

ttf : {n : ℕ } {x a : FL (suc n)} → x f< a → (y : FList {suc n}) →  fresh (FL (suc n)) ⌊ _f<?_ ⌋  a y  → fresh (FL (suc n)) ⌊ _f<?_ ⌋  x y
ttf _ [] fr = Level.lift tt
ttf {_} {x} {a} lt (cons a₁ y x1) (lift lt1 , x2 ) = (Level.lift (fromWitness (ttf1 lt1 lt ))) , ttf (ttf1 lt1 lt) y x1 where 
       ttf1 : True (a f<? a₁) → x f< a  → x f< a₁
       ttf1 t x<a = f<-trans x<a (toWitness t)

-- by https://gist.github.com/aristidb/1684202

FLinsert : {n : ℕ } → FL n → FList {n}  → FList {n} 
FLfresh : {n : ℕ } → (a x : FL (suc n) ) → (y : FList {suc n} ) → a f< x
     → fresh (FL (suc n)) ⌊ _f<?_ ⌋ a y → fresh (FL (suc n)) ⌊ _f<?_ ⌋ a (FLinsert x y)
FLinsert {zero} f0 y = f0 ∷# []
FLinsert {suc n} x [] = x ∷# []
FLinsert {suc n} x (cons a y x₁) with FLcmp x a
... | tri≈ ¬a b ¬c  = cons a y x₁
... | tri< lt ¬b ¬c  = cons x ( cons a y x₁) ( Level.lift (fromWitness lt ) , ttf lt y  x₁) 
FLinsert {suc n} x (cons a [] x₁) | tri> ¬a ¬b lt with FLinsert x [] | inspect ( FLinsert x ) []
... | [] | ()
... | cons a₁ t x₂ | e = cons a ( x  ∷# []  ) ( Level.lift (fromWitness lt) , Level.lift tt )
FLinsert {suc n} x (cons a y yr) |  tri> ¬a ¬b a<x =
        cons a (FLinsert x y) (FLfresh a x y a<x yr )

FLfresh a x [] a<x (Level.lift tt) = Level.lift (fromWitness a<x) , Level.lift tt
FLfresh a x (cons b [] (Level.lift tt)) a<x (Level.lift a<b , a<y) with FLcmp x b
... | tri< x<b ¬b ¬c  = Level.lift (fromWitness a<x) , Level.lift a<b , Level.lift tt
... | tri≈ ¬a refl ¬c = Level.lift (fromWitness a<x) , Level.lift tt
... | tri> ¬a ¬b b<x =  Level.lift a<b  ,  Level.lift (fromWitness  (f<-trans (toWitness a<b) b<x))  , Level.lift tt
FLfresh a x (cons b y br) a<x (Level.lift a<b , a<y) with FLcmp x b
... | tri< x<b ¬b ¬c =  Level.lift (fromWitness a<x) , Level.lift a<b , ttf (toWitness a<b) y br
... | tri≈ ¬a refl ¬c = Level.lift (fromWitness a<x) , ttf a<x y br
FLfresh a x (cons b [] br) a<x (Level.lift a<b , a<y) | tri> ¬a ¬b b<x =
    Level.lift a<b , Level.lift (fromWitness (f<-trans (toWitness a<b) b<x)) , Level.lift tt
FLfresh a x (cons b (cons a₁ y x₁) br) a<x (Level.lift a<b , a<y) | tri> ¬a ¬b b<x =
    Level.lift a<b , FLfresh a x (cons a₁ y x₁) a<x a<y

fr6 = FLinsert ((# 1) :: ((# 1) :: ((# 0 ) :: f0))) fr1 

-- open import Data.List.Fresh.Relation.Unary.All
-- fr7 = append ( ((# 1) :: ((# 1) :: ((# 0 ) :: f0))) ∷# [] ) fr1 ( ({!!} , {!!} ) ∷ [] )

Flist1 :  {n : ℕ } (i : ℕ) → i < suc n → FList {n} → FList {n} → FList {suc n} 
Flist1 zero i<n [] _ = []
Flist1 zero i<n (a ∷# x ) z  = FLinsert ( zero :: a ) (Flist1 zero i<n x z )
Flist1 (suc i) (s≤s i<n) [] z  = Flist1 i (Data.Nat.Properties.<-trans i<n a<sa) z z 
Flist1 (suc i) i<n (a ∷# x ) z  = FLinsert ((fromℕ< i<n ) :: a ) (Flist1 (suc i) i<n x z )

Flist : {n : ℕ } → FL n → FList {n}
Flist {zero} f0 = f0 ∷# [] 
Flist {suc n} (x :: y)  = Flist1 n a<sa (Flist y) (Flist y)   

fr8 : FList {4}
fr8 = Flist (fmax {4}) 

-- FLinsert membership

module FLMB { n : ℕ } where

  FL-Setoid : Setoid Level.zero Level.zero
  FL-Setoid  = record { Carrier = FL n ; _≈_ = _≡_ ; isEquivalence = record { sym = sym ; refl = refl ; trans = trans }}

  open import Data.List.Fresh.Membership.Setoid FL-Setoid
  open import Data.List.Fresh.Relation.Unary.Any 

  FLinsert-mb :  (x : FL n ) → (xs : FList {n})  → x ∈ FLinsert x xs
  FLinsert-mb x xs = {!!}
