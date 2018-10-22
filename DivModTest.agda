module DivModTest where

open import Foreign.Haskell
open import IO.Primitive
open import Data.String using (String; toCostring)

open import Function  using (_$_; _∘_) 
open import Relation.Binary.PropositionalEquality using (_≢_; sym)
open import Data.List using (List; []; _∷_) 
open import Data.Nat  using (ℕ) renaming (suc to 1+_) 
import Data.Nat.Show as NatShow 
open import Data.Nat.DivMod using () 
                        renaming (DivMod to DivModN; _divMod_ to _divModN_)
import Data.Fin as Fin 

-- of application ---
open import List0  using (concatStr) 
open import Bin0   using (Bin; 0b; 1b; 0#; 1bin; _+_; _*_; suc; toℕ)
open import Bin1   using (≢sym) 
open import Bin4   using (0≢1+x) 
open import DivMod using (DivMod; divMod) 


------------------------------------------------------------------------------
testN : ℕ → (dr : ℕ) → List String 
testN dd dr = 
            let (DivModN.result q rF _) =  dd divModN (1+ dr) 
                r = Fin.toℕ rF
            in
            "dd = " ∷ NatShow.show dd  ∷ "   dr = " ∷ NatShow.show (1+ dr) ∷ 
            "\nq = " ∷ NatShow.show q  ∷ "   r = " ∷ NatShow.show r  ∷ [] 

testB :  Bin → (dr : Bin) → List String 
testB dd dr = 
            let 1+dr≢0                  = ≢sym (0≢1+x dr)
                (DivMod.result q r _ _) = divMod dd (suc dr) 1+dr≢0
            in
            "dd = "  ∷ Bin0.show dd  ∷  "   dr = " ∷  Bin0.show dr  ∷ 
            "\nq = " ∷ Bin0.show q   ∷  "   r = "  ∷  Bin0.show r   ∷  [] 


main = (readFiniteFile "data.txt") >>= putStrLn ∘ toCostring ∘ g
       where
       g : String -> String
       g str = concatStr $ testB dd dr 
               where       -- test ddN drN
               a : Bin
               a = Bin0.fromString str

               b = Bin0.fromString "10101"
               c = Bin0.fromString "10101010"

               dd = a 
               dr = a 

               ddN = toℕ dd;   drN = toℕ dr



 
