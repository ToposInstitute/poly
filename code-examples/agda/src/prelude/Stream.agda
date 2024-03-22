{-# OPTIONS --guardedness #-}
module prelude.Stream where
open import prelude
open import Data.List as L using (List)

record Stream (a : Set) : Set where
    constructor _∷_
    coinductive
    field
        hd : a
        tl : Stream a
open Stream


take : ∀ {a} → ℕ → Stream a → List a
take ℕz xs = L.[]
take (ℕs n) xs = hd xs L.∷ take n (tl xs)
