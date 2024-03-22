{-# OPTIONS --type-in-type #-}
{-# OPTIONS --guardedness #-} 
module dyn where
open import prelude
open import functors
open import poly0 public
open import prelude.Stream
open Stream
open import Data.List as L using (List)


record Dyn : Set where
  constructor dyn
  field
    {state} : Set
    {body}  : ∫
    pheno   : ∫[ (state , λ _ → state) , body ]
open Dyn public

run : (d : Dyn) → ∫[ body d , 𝒴 ] → state d → Stream (π₁ (body d))
hd (run d@(dyn l) e s₀) = s₀ ★ l
tl (run d@(dyn l) e s₀) = run d e (s₀ # l ← hd (run d e s₀) # e ← tt)

module _ (d₁ d₂ : Dyn) where
    _⊠⊠⊠_ : Dyn
    _⊠⊠⊠_ = dyn (pheno d₁ ⟦⊠⟧ pheno d₂)

_⟫_ : (d : Dyn) → ∫[ body d , A ] → Dyn
d ⟫ l = dyn (pheno d ▸ l)

fun→dyn : ∀ {a b} → (a → b) → Dyn
fun→dyn f = dyn (λ a⁺ → a⁺ , f)

delay : Set → Dyn
delay s = fun→dyn (id {A = s})
