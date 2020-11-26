open import Level hiding ( suc ; zero )
open import Algebra
module sym3 where

open import Symmetric 
open import Data.Unit
open import Function.Inverse as Inverse using (_↔_; Inverse; _InverseOf_)
open import Function
open import Data.Nat hiding (_⊔_) -- using (ℕ; suc; zero)
open import Relation.Nullary
open import Data.Empty
open import Data.Product

open import Gutil 
open import Putil 
open import FLutil 
open import Solvable using (solvable)
open import  Relation.Binary.PropositionalEquality hiding ( [_] )

open import Data.Fin
open import Data.Fin.Permutation hiding (_∘ₚ_)

infixr  200 _∘ₚ_
_∘ₚ_ = Data.Fin.Permutation._∘ₚ_


sym3solvable : solvable (Symmetric 3)
solvable.dervied-length sym3solvable = 2
solvable.end sym3solvable x d = solved1 x d where

   open import Data.List using ( List ; [] ; _∷_ )

   open Solvable (Symmetric 3)

   p0id :  FL→perm ((# 0) :: ((# 0) :: ((# 0 ) :: f0))) =p= pid
   p0id = pleq _ _ refl 

   p0 =  FL→perm ((# 0) :: ((# 0) :: ((# 0 ) :: f0))) 
   p1 =  FL→perm ((# 0) :: ((# 1) :: ((# 0 ) :: f0))) 
   p2 =  FL→perm ((# 1) :: ((# 0) :: ((# 0 ) :: f0))) 
   p3 =  FL→perm ((# 1) :: ((# 1) :: ((# 0 ) :: f0))) 
   p4 =  FL→perm ((# 2) :: ((# 0) :: ((# 0 ) :: f0))) 
   p5 =  FL→perm ((# 2) :: ((# 1) :: ((# 0 ) :: f0))) 
   t0  =  plist p0 ∷ plist p1 ∷  plist p2 ∷ plist p3 ∷ plist p4 ∷  plist p5 ∷ [] 

   t1  =  plist [ p0 , p0 ] ∷ plist [ p1 , p0 ] ∷  plist [ p2 , p0 ] ∷ plist [ p3 , p0 ] ∷ plist [ p4 , p0 ] ∷  plist [ p5 , p1 ] ∷ 
          plist [ p0 , p1 ] ∷ plist [ p1 , p1 ] ∷  plist [ p2 , p1 ] ∷ plist [ p3 , p1 ] ∷ plist [ p4 , p1 ] ∷  plist [ p5 , p1 ] ∷ 
          plist [ p0 , p2 ] ∷ plist [ p1 , p2 ] ∷  plist [ p2 , p2 ] ∷ plist [ p3 , p2 ] ∷ plist [ p4 , p2 ] ∷  plist [ p5 , p2 ] ∷ 
          plist [ p0 , p3 ] ∷ plist [ p1 , p3 ] ∷  plist [ p3 , p3 ] ∷ plist [ p3 , p3 ] ∷ plist [ p4 , p3 ] ∷  plist [ p5 , p3 ] ∷ 
          plist [ p0 , p4 ] ∷ plist [ p1 , p4 ] ∷  plist [ p3 , p4 ] ∷ plist [ p3 , p4 ] ∷ plist [ p4 , p4 ] ∷  plist [ p5 , p4 ] ∷ 
          plist [ p0 , p5 ] ∷ plist [ p1 , p5 ] ∷  plist [ p3 , p5 ] ∷ plist [ p3 , p5 ] ∷ plist [ p4 , p4 ] ∷  plist [ p5 , p5 ] ∷ 
          []

   open _=p=_
   
   stage1 :  (x : Permutation 3 3) →  Set (Level.suc Level.zero)
   stage1 x = Commutator (λ x₂ → Lift (Level.suc Level.zero) ⊤)  x 

   open import logic

   p33=4 : ( p3  ∘ₚ p3 ) =p= p4
   p33=4 = pleq _ _ refl

   p44=3 : ( p4  ∘ₚ p4 ) =p= p3
   p44=3 = pleq _ _ refl

   p34=0 : ( p3  ∘ₚ p4 ) =p= pid
   p34=0 = pleq _ _ refl

   p43=0 : ( p4  ∘ₚ p3 ) =p= pid
   p43=0 = pleq _ _ refl

   com33 : [ p3 , p3 ] =p= pid
   com33 = pleq _ _ refl

   com44 : [ p4 , p4 ] =p= pid
   com44 = pleq _ _ refl

   com34 : [ p3 , p4 ] =p= pid
   com34 = pleq _ _ refl

   com43 : [ p4 , p3 ] =p= pid
   com43 = pleq _ _ refl


   pFL : ( g : Permutation 3 3) → { x : FL 3 } →  perm→FL g ≡ x → g =p=  FL→perm x
   pFL g {x} refl = ptrans (psym (FL←iso g)) ( FL-inject refl ) 

   open ≡-Reasoning

--   st01 : ( x y : Permutation 3 3) →   x =p= p3 →  y =p= p3 → x ∘ₚ  y =p= p4 
--   st01 x y s t = record { peq = λ q → ( begin
--         (x ∘ₚ y) ⟨$⟩ʳ q
--       ≡⟨ peq ( presp s t ) q ⟩
--          ( p3  ∘ₚ p3 ) ⟨$⟩ʳ q
--       ≡⟨ peq  p33=4 q  ⟩
--         p4 ⟨$⟩ʳ q
--       ∎ ) }

   st00 = perm→FL [ FL→perm ((suc zero) :: (suc zero :: (zero :: f0 ))) , FL→perm  ((suc (suc zero)) :: (suc zero) :: (zero :: f0))  ]

   st02 :  ( g h : Permutation 3 3) →  ([ g , h ] =p= pid) ∨ ([ g , h ] =p= p3) ∨ ([ g , h ] =p= p4)
   st02 g h with perm→FL g | perm→FL h | inspect perm→FL g | inspect perm→FL h
   ... | (zero :: (zero :: (zero :: f0))) | t | record { eq = ge } | te = case1 (ptrans (comm-resp {g} {h} {pid} (FL-inject ge ) prefl ) (idcomtl h) )
   ... | s | (zero :: (zero :: (zero :: f0))) | se |  record { eq = he } = case1 (ptrans (comm-resp {g} {h} {_} {pid} prefl (FL-inject he ))(idcomtr g) )
   ... | (zero :: (suc zero) :: (zero :: f0 )) |  (zero :: (suc zero) :: (zero :: f0 )) |  record { eq = ge } |  record { eq = he } =
        case1 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) )
   ... | (suc zero) :: (zero :: (zero :: f0 )) | (suc zero) :: (zero :: (zero :: f0 )) |  record { eq = ge } |  record { eq = he } = 
        case1 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) )
   ... | (suc zero) :: (suc zero :: (zero :: f0 )) |  (suc zero) :: (suc zero :: (zero :: f0 )) |  record { eq = ge } |  record { eq = he } = 
        case1 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) )
   ... | (suc (suc zero)) :: (zero :: (zero :: f0 )) | (suc (suc zero)) :: (zero :: (zero :: f0 )) | record { eq = ge } |  record { eq = he } =
        case1 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) )
   ... | (suc (suc zero)) :: (suc zero) :: (zero :: f0) | (suc (suc zero)) :: (suc zero) :: (zero :: f0) | record { eq = ge } |  record { eq = he } =
        case1 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) )

   ... | (zero :: (suc zero) :: (zero :: f0 )) | ((suc zero) :: (zero :: (zero :: f0 ))) | record { eq = ge } |  record { eq = he } =
           case2 (case2 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... | (zero :: (suc zero) :: (zero :: f0 )) | (suc zero) :: (suc zero :: (zero :: f0 )) | record { eq = ge } |  record { eq = he } = 
           case2 (case2 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... | (zero :: (suc zero) :: (zero :: f0 )) |  (suc (suc zero)) :: (zero :: (zero :: f0 ))| record { eq = ge } |  record { eq = he } =  
           case2 (case1 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... | (zero :: (suc zero) :: (zero :: f0 )) | ((suc (suc zero)) :: (suc zero) :: (zero :: f0))| record { eq = ge } |  record { eq = he } =   
           case2 (case1 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... | ((suc zero) :: (zero :: (zero :: f0 ))) | (zero :: (suc zero) :: (zero :: f0 )) | record { eq = ge } |  record { eq = he } = 
          case2 (case1 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... | ((suc zero) :: (zero :: (zero :: f0 ))) | (suc zero) :: (suc zero :: (zero :: f0 )) | record { eq = ge } |  record { eq = he } = 
            case2 (case2 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... | ((suc zero) :: (zero :: (zero :: f0 ))) | ((suc (suc zero)) :: (zero :: (zero :: f0 )))| record { eq = ge } |  record { eq = he } =  
            case2 (case1 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... | ((suc zero) :: (zero :: (zero :: f0 ))) |  (suc (suc zero)) :: (suc zero) :: (zero :: f0) | record { eq = ge } |  record { eq = he } =  
            case2 (case2 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... | (suc zero) :: (suc zero :: (zero :: f0 )) |  (zero :: (suc zero) :: (zero :: f0 )) | record { eq = ge } |  record { eq = he } =  
            case2 (case1 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... | (suc zero) :: (suc zero :: (zero :: f0 )) |  ((suc zero) :: (zero :: (zero :: f0 ))) | record { eq = ge } |  record { eq = he } =  
            case2 (case1 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... | (suc zero) :: (suc zero :: (zero :: f0 )) |  ((suc (suc zero)) :: (zero :: (zero :: f0 ))) | record { eq = ge } |  record { eq = he } =  
         case1 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) )
   ... | (suc zero) :: (suc zero :: (zero :: f0 )) |  ((suc (suc zero)) :: (suc zero) :: (zero :: f0)) | record { eq = ge } |  record { eq = he } =   
            case2 (case1 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... | (suc (suc zero)) :: (zero :: (zero :: f0 )) | ((zero :: (suc zero) :: (zero :: f0 )) ) | record { eq = ge } |  record { eq = he } =
          case2 (case2 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... | (suc (suc zero)) :: (zero :: (zero :: f0 )) | ((suc zero) :: (zero :: (zero :: f0 ))) | record { eq = ge } |  record { eq = he } =
          case2 (case2 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... | (suc (suc zero)) :: (zero :: (zero :: f0 )) | ((suc zero) :: (suc zero :: (zero :: f0 ))) | record { eq = ge } |  record { eq = he } =
          case1 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) )
   ... | (suc (suc zero)) :: (zero :: (zero :: f0 )) | ((suc (suc zero)) :: (suc zero) :: (zero :: f0)) | record { eq = ge } |  record { eq = he } = 
          case2 (case2 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... |  ((suc (suc zero)) :: (suc zero) :: (zero :: f0)) | ((zero :: (suc zero) :: (zero :: f0 )) ) | record { eq = ge } |  record { eq = he } =
          case2 (case2 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... |  ((suc (suc zero)) :: (suc zero) :: (zero :: f0)) | ((suc zero) :: (zero :: (zero :: f0 ))) | record { eq = ge } |  record { eq = he } =
          case2 (case1 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... |  ((suc (suc zero)) :: (suc zero) :: (zero :: f0)) | ((suc zero) :: (suc zero :: (zero :: f0 )))  | record { eq = ge } |  record { eq = he } =
          case2 (case2 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   ... |  ((suc (suc zero)) :: (suc zero) :: (zero :: f0)) | (suc (suc zero)) :: (zero :: (zero :: f0 ))  | record { eq = ge } |  record { eq = he } =
          case2 (case1 (ptrans (comm-resp (pFL g ge) (pFL h he)) (FL-inject refl) ))
   
   stage12  :  (x : Permutation 3 3) → stage1 x →  ( x =p= pid ) ∨ ( x =p= p3 ) ∨ ( x =p= p4 )
   stage12 x uni = case1 prefl
   stage12 x (comm {g} {h} x1 y1 ) = st02 g h
   stage12 _ (gen {x} {y} sx sy) with stage12 x sx | stage12 y sy 
   ... | case1 t | case1 s = case1 ( record { peq = λ q → peq (presp t s) q} )
   ... | case1 t | case2 (case1 s) = case2 (case1 ( record { peq = λ q → peq (presp t s ) q } )) 
   ... | case1 t | case2 (case2 s) = case2 (case2 ( record { peq = λ q → peq (presp t s ) q } )) 
   ... | case2 (case1 t) | case1 s = case2 (case1 ( record { peq = λ q → peq (presp t s ) q } )) 
   ... | case2 (case2 t) | case1 s = case2 (case2 ( record { peq = λ q → peq (presp t s ) q } )) 
   ... | case2 (case1 s) | case2 (case1 t) = case2 (case2 record { peq = λ q → trans (peq ( presp s t ) q) ( peq  p33=4 q) } ) 
   ... | case2 (case1 s) | case2 (case2 t) = case1 record { peq = λ q → trans (peq ( presp s t ) q) ( peq  p34=0 q) }  
   ... | case2 (case2 s) | case2 (case1 t) = case1 record { peq = λ q → trans (peq ( presp s t ) q) ( peq  p43=0 q) } 
   ... | case2 (case2 s) | case2 (case2 t) = case2 (case1 record { peq = λ q → trans (peq ( presp s t ) q) ( peq  p44=3 q) } ) 
   stage12 _ (ccong {y} x=y sx) with stage12 y sx
   ... | case1 id = case1 ( ptrans (psym x=y ) id )
   ... | case2 (case1 x₁) = case2 (case1 ( ptrans (psym x=y ) x₁ ))
   ... | case2 (case2 x₁) = case2 (case2 ( ptrans (psym x=y ) x₁ ))


   solved1 :  (x : Permutation 3 3) →  Commutator (λ x₁ → Commutator (λ x₂ → Lift (Level.suc Level.zero) ⊤) x₁) x → x =p= pid
   solved1 _ uni = prefl
   solved1 x (gen {f} {g} d d₁) with solved1 f d | solved1 g d₁
   ... | record { peq = f=e } | record { peq = g=e } = record { peq = λ q → genlem q } where
      genlem : ( q : Fin 3 ) → g ⟨$⟩ʳ ( f ⟨$⟩ʳ q ) ≡ q
      genlem q = begin
             g ⟨$⟩ʳ ( f ⟨$⟩ʳ q )
          ≡⟨ g=e ( f ⟨$⟩ʳ q ) ⟩
             f ⟨$⟩ʳ q 
          ≡⟨ f=e q ⟩
             q
          ∎ 
   solved1 x (ccong {f} {g} (record {peq = f=g}) d) with solved1 f d
   ... | record { peq = f=e }  =  record  { peq = λ q → cc q } where
      cc : ( q : Fin 3 ) → x ⟨$⟩ʳ q ≡ q
      cc q = begin
             x ⟨$⟩ʳ q
          ≡⟨ sym (f=g q) ⟩
             f ⟨$⟩ʳ q
          ≡⟨ f=e q ⟩
             q
          ∎ 
   solved1 _ (comm {g} {h} x y) with stage12 g x | stage12 h y
   ... | case1 t | case1 s = ptrans (comm-resp t s) (comm-refl {pid} prefl)
   ... | case1 t | case2 s = ptrans (comm-resp {g} {h} {pid} t prefl) (idcomtl h)
   ... | case2 t | case1 s = ptrans (comm-resp {g} {h} {_} {pid} prefl s) (idcomtr g)
   ... | case2 (case1 t) | case2 (case1 s) = record { peq = λ q → trans ( peq ( comm-resp {g} {h}  t s ) q ) (peq com33 q) }
   ... | case2 (case2 t) | case2 (case2 s) = record { peq = λ q → trans ( peq ( comm-resp {g} {h}  t s ) q ) (peq com44 q) }
   ... | case2 (case1 t) | case2 (case2 s) = record { peq = λ q → trans ( peq ( comm-resp {g} {h}  t s ) q ) (peq com34 q) }
   ... | case2 (case2 t) | case2 (case1 s) = record { peq = λ q → trans ( peq ( comm-resp {g} {h}  t s ) q ) (peq com43 q) }

