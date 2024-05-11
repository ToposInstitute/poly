{-# OPTIONS --type-in-type #-}
{-# OPTIONS --guardedness #-}
module prelude.io where
open import prelude
open import functors
open import Agda.Builtin.IO public using (IO)
open import Data.String
open import prelude.Stream as Stream using (Stream)
open import Data.List as L using (List)

IO[_,_] : Set → Set → Set
IO[ A , B ] = A → IO B

infixl 1 _>>=_

postulate
  return : ∀ {a} {A : Set a} → A → IO A
  _>>=_  : ∀ {a b} {A : Set a} {B : Set b} → IO A → (A → IO B) → IO B
  return>>= : ∀ {a b} (f : a → IO b) → (λ x → return x >>= f) ≡ f
  >>=return : ∀ {a b} (f : a → IO b) → (λ x → f x >>= return) ≡ f


{-# COMPILE GHC return = \_ _ -> return    #-}
{-# COMPILE GHC _>>=_  = \_ _ _ _ -> (>>=) #-}

-- record Category {O : Set} (𝒞[_,_] : O → O → Set) : Set where
--   constructor 𝒾:_▸:_𝒾▸:_▸𝒾:
--   infixl 8 _▸_
--   field
--     𝒾 : ∀ {x} → 𝒞[ x , x ]
--     _▸_ : ∀ {x y z} → 𝒞[ x , y ] → 𝒞[ y , z ] → 𝒞[ x , z ]
--     𝒾▸ : ∀ {x y} (f : 𝒞[ x , y ]) → (𝒾 ▸ f) ≡ f
--     ▸𝒾 : ∀ {x y} (f : 𝒞[ x , y ]) → (f ▸ 𝒾) ≡ f
-- open Category ⦃...⦄ public


instance
  io-cat : Category IO[_,_]
  io-cat = 𝒾: return ▸: (λ f g x → f x >>= g) 𝒾▸: return>>= ▸𝒾: >>=return


{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# FOREIGN GHC import qualified Data.Text.IO as T #-}

postulate
  getContents : IO String
  putStrLn    : String → IO ⊤

{-# COMPILE GHC getContents = T.getContents #-}
{-# COMPILE GHC putStrLn = T.putStrLn #-}

postulate
  showℕ : ℕ → String
{-# COMPILE GHC showℕ = T.pack . show #-}

{-# NON_TERMINATING #-}
printStream : Stream ℕ → IO ⊤
printStream s = putStrLn (showℕ (Stream.hd s)) >>= λ _ → printStream (Stream.tl s)

printList : List ℕ → IO ⊤
printList L.[] = return tt
printList (x L.∷ xs) = putStrLn (showℕ x) >>= λ _ → printList xs
