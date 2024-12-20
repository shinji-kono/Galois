{-# OPTIONS --cubical-compatible --safe #-}
module FLutil where

open import Level hiding ( suc ; zero )
open import Data.Fin hiding (_<_  ; _>_ ; _≤_ ; _-_ ; _+_ ; _≟_)
open import Data.Fin.Properties hiding ( <-trans ; ≤-refl ; ≤-trans ; ≤-irrelevant ; _≟_ ) renaming ( <-cmp to <-fcmp )
open import Data.Fin.Permutation  -- hiding ([_,_])
open import Data.Nat -- using (ℕ; suc; zero; s≤s ; z≤n )
open import Data.Nat.Properties as DNP
open import Relation.Binary.PropositionalEquality hiding ( [_] )
open import Data.List using (List; []; _∷_ ; length ; _++_ ; tail ) renaming (reverse to rev )
open import Data.Product
open import Relation.Nullary as RNu hiding ( ⌊_⌋ ; toWitness ; fromWitness ) 
open import Data.Empty
open import Data.Maybe
open import Data.Maybe.Properties
open import  Relation.Binary.Core
open import  Relation.Binary.Definitions 
open import logic
open import nat

infixr  100 _::_

data  FL : (n : ℕ ) → Set where
   f0 :  FL 0 
   _::_ :  { n : ℕ } → Fin (suc n ) → FL n → FL (suc n)

data _f<_  : {n : ℕ } (x : FL n ) (y : FL n)  → Set  where
   f<n : {m : ℕ } {xn yn : Fin (suc m) } {xt yt : FL m} → xn Data.Fin.< yn →   (xn :: xt) f< ( yn :: yt )
   f<t : {m : ℕ } {xn : Fin (suc m) } {xt yt : FL m} → xt f< yt →   (xn :: xt) f< ( xn :: yt )

proj1-FL : {n : ℕ } → FL n → Maybe (Fin n) 
proj1-FL f0 = nothing
proj1-FL (x :: fl) = just x

proj2-FL : {n : ℕ } → FL n → Maybe (FL (Data.Nat.pred n))
proj2-FL f0 = nothing
proj2-FL (x :: fl) = just fl

FLeq : {n : ℕ } {xn yn : Fin (suc n)} {x : FL n } {y : FL n}  → xn :: x ≡ yn :: y → ( xn ≡ yn )  × (x ≡ y )
FLeq {n} {xn} {yn} {x} {y} eq = (just-injective (cong proj1-FL eq)) , (just-injective (cong proj2-FL eq)) 

proj1-FL-0 : (n : ℕ ) → (fl : FL n ) → proj1-FL fl ≡ nothing → n ≡ 0
proj1-FL-0 n f0 eq = refl       -- we cannot put n ≡ 0
proj1-FL-0 (suc n) (x :: fl) ()

FLpos : {n : ℕ} → FL (suc n) → Fin (suc n)
FLpos {n} fl = lemma (suc n) (s≤s z≤n) fl  where
    lemma : (m : ℕ ) → 0 < m → FL m → Fin m
    lemma n () f0 
    lemma (suc _) 0<m (x :: fl) = x

fin-≡< :  {n : ℕ } {x : Fin n } {y : Fin n}  → x ≡ y → y Data.Fin.< x → ⊥
fin-≡< {n} {x} {y} eq y<x with <-fcmp x y
... | tri< a ¬b ¬c = ¬b eq
... | tri≈ ¬a refl ¬c = nat-≡< refl y<x
... | tri> ¬a ¬b c = ¬b eq
                                                                
f-≡< :  {n : ℕ } {x : FL n } {y : FL n}  → x ≡ y → y f< x → ⊥
f-≡< eq (f<t lt2) = f-≡< (proj₂ (FLeq eq)) lt2
f-≡< eq (f<n {_} {xn} {yn} xn<yn) = fin-≡< (proj₁ (FLeq eq)) xn<yn

f-<> :  {n : ℕ } {x : FL n } {y : FL n}  → x f< y → y f< x → ⊥
f-<> {zero} {x} {y} ()
f-<> {suc n} {x} {y} x<y y<x = lemma x x<y y<x refl where
   lemma : {n : ℕ } {x y : FL (suc n)} (x1 : FL (suc n)) → (x<y : x f< y) (y<x : y f< x1) → x ≡ x1 → ⊥
   lemma _ (f<n x) (f<n x₁) refl = nat-<> x x₁
   lemma _ (f<n x) (f<t lt2) refl = nat-≡< refl x
   lemma _ (f<t ltx) (f<n x) refl = nat-≡< refl x
   lemma _ (f<t ltx) (f<t lty) eq = f-<> ltx (subst (λ k → _ f< k ) (proj₂ (FLeq (sym eq))) lty)

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

x≤fmax : {n : ℕ } → {x : FL n} → x f≤ fmax
x≤fmax {n} {x} with FLcmp x fmax
... | tri< a ¬b ¬c = case2 a
... | tri≈ ¬a b ¬c = case1 b
... | tri> ¬a ¬b c = ⊥-elim ( fmax< c )

open import Data.Nat.Properties using ( ≤-trans ; <-trans )
fsuc : { n : ℕ } → (x : FL n ) → x f< fmax → FL n 
fsuc {n} (x :: y) (f<n lt) = fromℕ< fsuc1 :: y where
    fsuc1 : suc (toℕ x) < n
    fsuc1 =  Data.Nat.Properties.≤-trans (s≤s lt) ( s≤s ( toℕ≤pred[n] (fromℕ< a<sa)) )
fsuc (x :: y) (f<t lt) = x :: fsuc y lt

open import fin

flist1 :  {n : ℕ } (i : ℕ) → i < suc n → List (FL n) → List (FL n) → List (FL (suc n)) 
flist1 zero i<n [] _ = []
flist1 zero i<n (a ∷ x ) z  = ( zero :: a ) ∷ flist1 zero i<n x z 
flist1 (suc i) (s≤s i<n) [] z  = flist1 i (Data.Nat.Properties.<-trans i<n a<sa) z z 
flist1 (suc i) i<n (a ∷ x ) z  = ((fromℕ< i<n ) :: a ) ∷ flist1 (suc i) i<n x z 

flist : {n : ℕ } → FL n → List (FL n) 
flist {zero} f0 = f0 ∷ [] 
flist {suc n} (x :: y)  = flist1 n a<sa (flist y) (flist y)   

FL1 : List ℕ → List ℕ
FL1 [] = []
FL1 (x ∷ y) = suc x ∷ FL1 y

FL→plist : {n : ℕ} → FL n → List ℕ
FL→plist {0} f0 = []
FL→plist {suc n} (zero :: y) = zero ∷ FL1 (FL→plist y) 
FL→plist {suc n} (suc x :: y) with FL→plist y
... | [] = zero ∷ []
... | x1 ∷ t = suc x1 ∷ FL2 x t where
  FL2 : {n : ℕ} → Fin n → List ℕ → List ℕ
  FL2 zero y = zero ∷ FL1 y
  FL2 (suc i) [] = zero ∷ []
  FL2 (suc i) (x ∷ y) = suc x ∷ FL2 i y

tt0 = (# 2) :: (# 1) :: (# 0) :: zero :: f0
tt1 = FL→plist tt0

open _∧_

find-zero : {n i : ℕ} → List ℕ → i < n  → Fin n ∧ List ℕ
find-zero  [] i<n = record { proj1 = fromℕ< i<n  ; proj2 = [] }
find-zero x (s≤s z≤n) = record { proj1 = fromℕ< (s≤s z≤n)  ; proj2 = x }
find-zero (zero ∷ y) (s≤s (s≤s i<n)) = record { proj1 = fromℕ< (s≤s (s≤s i<n)) ; proj2 = y }
find-zero (suc x ∷ y) (s≤s (s≤s i<n)) with find-zero y (s≤s i<n) 
... | record { proj1 = i ; proj2 = y1 } = record { proj1 = suc i ; proj2 = suc x ∷ y1 }

plist→FL : {n : ℕ} → List ℕ → FL n -- wrong implementation
plist→FL {zero} [] = f0
plist→FL {suc n} [] = zero :: plist→FL {n} []
plist→FL {zero} x = f0
plist→FL {suc n} x with find-zero x a<sa
... | record { proj1 = i ; proj2 = y } = i :: plist→FL y

tt2 = 2 ∷ 1 ∷ 0 ∷ 3 ∷ []
tt3 : FL 4
tt3 = plist→FL tt2
tt4 = FL→plist tt3
tt5 = plist→FL {4} (FL→plist tt0)

-- maybe FL→iso can be easier using this ...
-- FL→plist-iso : {n : ℕ} → (f : FL n ) → plist→FL (FL→plist f ) ≡ f
-- FL→plist-iso = {!!}
-- FL→plist-inject : {n : ℕ} → (f g : FL n ) → FL→plist f ≡ FL→plist g → f ≡ g
-- FL→plist-inject = {!!}

open import Relation.Binary as B hiding (Decidable; _⇔_)
open import Data.Sum.Base as Sum --  inj₁
open import Relation.Nary -- hiding (⌊_⌋)
open import Data.List.Fresh hiding ([_])

FList : (n : ℕ ) → Set
FList n = List# (FL n) ⌊ _f<?_ ⌋

fr1 : FList 3
fr1 =
   ((# 0) :: ((# 0) :: ((# 0 ) :: f0))) ∷# 
   ((# 0) :: ((# 1) :: ((# 0 ) :: f0))) ∷# 
   ((# 1) :: ((# 0) :: ((# 0 ) :: f0))) ∷# 
   ((# 2) :: ((# 0) :: ((# 0 ) :: f0))) ∷# 
   ((# 2) :: ((# 1) :: ((# 0 ) :: f0))) ∷# 
   []

open import Data.Product
-- open import Relation.Nullary.Decidable hiding (⌊_⌋)
-- open import Data.Bool hiding (_<_ ; _≤_ )
open import Data.Unit.Base using (⊤ ; tt)

--  fresh a []        = ⊤
--  fresh a (x ∷# xs) = R a x × fresh a xs

-- toWitness
-- ttf< :  {n : ℕ } → {x a : FL n } → x f< a  → T (isYes (x f<? a))
-- ttf< {n} {x} {a} x<a with x f<? a
-- ... | yes y = subst (λ k → Data.Bool.T k ) refl tt
-- ... | no nn = ⊥-elim ( nn x<a )

ttf : {n : ℕ } {x a : FL (n)} → x f< a → (y : FList (n)) →  fresh (FL (n)) ⌊ _f<?_ ⌋  a y  → fresh (FL (n)) ⌊ _f<?_ ⌋  x y
ttf _ [] fr = Level.lift tt
ttf {_} {x} {a} lt (cons a₁ y x1) (lift lt1 , x2 ) = (Level.lift (RNu.fromWitness (ttf1 lt1 lt ))) , ttf (ttf1 lt1 lt) y x1 where 
       ttf1 : True (a f<? a₁) → x f< a  → x f< a₁
       ttf1 t x<a = f<-trans x<a (RNu.toWitness t)

-- by https://gist.github.com/aristidb/1684202

FLinsert : {n : ℕ } → FL n → FList n  → FList n 
FLfresh : {n : ℕ } → (a x : FL (suc n) ) → (y : FList (suc n) ) → a f< x
     → fresh (FL (suc n)) ⌊ _f<?_ ⌋ a y → fresh (FL (suc n)) ⌊ _f<?_ ⌋ a (FLinsert x y)
FLinsert {zero} f0 y = f0 ∷# []
FLinsert {suc n} x [] = x ∷# []
FLinsert {suc n} x (cons a y x₁) with FLcmp x a
... | tri≈ ¬a b ¬c  = cons a y x₁
... | tri< lt ¬b ¬c  = cons x ( cons a y x₁) ( Level.lift (RNu.fromWitness lt ) , ttf lt y  x₁) 
FLinsert {suc n} x (cons a [] x₁) | tri> ¬a ¬b lt  = cons a ( x  ∷# []  ) ( Level.lift (RNu.fromWitness lt) , Level.lift tt )
FLinsert {suc n} x (cons a y yr)  | tri> ¬a ¬b a<x = cons a (FLinsert x y) (FLfresh a x y a<x yr )

FLfresh a x [] a<x (Level.lift tt) = Level.lift (RNu.fromWitness a<x) , Level.lift tt
FLfresh a x (cons b [] (Level.lift tt)) a<x (Level.lift a<b , a<y) with FLcmp x b
... | tri< x<b ¬b ¬c  = Level.lift (RNu.fromWitness a<x) , Level.lift a<b , Level.lift tt
... | tri≈ ¬a refl ¬c = Level.lift (RNu.fromWitness a<x) , Level.lift tt
... | tri> ¬a ¬b b<x =  Level.lift a<b  ,  Level.lift (RNu.fromWitness  (f<-trans (RNu.toWitness a<b) b<x))  , Level.lift tt
FLfresh a x (cons b y br) a<x (Level.lift a<b , a<y) with FLcmp x b
... | tri< x<b ¬b ¬c =  Level.lift (RNu.fromWitness a<x) , Level.lift a<b , ttf (RNu.toWitness a<b) y br
... | tri≈ ¬a refl ¬c = Level.lift (RNu.fromWitness a<x) , ttf a<x y br
FLfresh a x (cons b [] br) a<x (Level.lift a<b , a<y) | tri> ¬a ¬b b<x =
    Level.lift a<b , Level.lift (RNu.fromWitness (f<-trans (RNu.toWitness a<b) b<x)) , Level.lift tt
FLfresh a x (cons b (cons a₁ y x₁) br) a<x (Level.lift a<b , a<y) | tri> ¬a ¬b b<x =
    Level.lift a<b , FLfresh a x (cons a₁ y x₁) a<x a<y

fr6 = FLinsert ((# 1) :: ((# 1) :: ((# 0 ) :: f0))) fr1 

open import Data.List.Fresh.Relation.Unary.Any 
open import Data.List.Fresh.Relation.Unary.All 

x∈FLins : {n : ℕ} → (x : FL n ) → (xs : FList n)  → Any (x ≡_) (FLinsert x xs)
x∈FLins {zero} f0 [] = here refl
x∈FLins {zero} f0 (cons f0 xs x) = here refl
x∈FLins {suc n} x [] = here refl
x∈FLins {suc n} x (cons a xs x₁) with FLcmp x a
... | tri< x<a ¬b ¬c = here refl
... | tri≈ ¬a b ¬c   = here b
x∈FLins {suc n} x (cons a [] x₁)              | tri> ¬a ¬b a<x = there ( here refl )
x∈FLins {suc n} x (cons a (cons a₁ xs x₂) x₁) | tri> ¬a ¬b a<x = there ( x∈FLins x (cons a₁ xs x₂) )

nextAny : {n : ℕ} → {x h : FL n } → {L : FList n}  → {hr : fresh (FL n) ⌊ _f<?_ ⌋ h L } → Any (x ≡_) L → Any (x ≡_) (cons h L hr )
nextAny (here x₁) = there (here x₁)
nextAny (there any) = there (there any)

insAny : {n : ℕ} → {x h : FL n } → (xs : FList n)  → Any (x ≡_) xs → Any (x ≡_) (FLinsert h xs)
insAny {zero} {f0} {f0} (cons a L xr) (here refl) = here refl
insAny {zero} {f0} {f0} (cons a L xr) (there any) = insAny {zero} {f0} {f0} L any 
insAny {suc n} {x} {h} (cons a L xr) any with FLcmp h a 
... | tri< x<a ¬b ¬c = there any
... | tri≈ ¬a b ¬c = any
insAny {suc n} {a} {h} (cons a [] (Level.lift tt)) (here refl) | tri> ¬a ¬b c = here refl
insAny {suc n} {x} {h} (cons a (cons a₁ L x₁) xr) (here refl) | tri> ¬a ¬b c = here refl
insAny {suc n} {x} {h} (cons a (cons a₁ L x₁) xr) (there any) | tri> ¬a ¬b c = there (insAny (cons a₁ L x₁) any)

-- FLinsert membership

module FLMB { n : ℕ } where

  FL-Setoid : Setoid Level.zero Level.zero
  FL-Setoid  = record { Carrier = FL n ; _≈_ = _≡_ ; isEquivalence = record { sym = sym ; refl = refl ; trans = trans }}

  open import Data.List.Fresh.Membership.Setoid FL-Setoid

  FLinsert-mb :  (x : FL n ) → (xs : FList n)  → x ∈ FLinsert x xs
  FLinsert-mb x xs = x∈FLins {n} x xs 

  
