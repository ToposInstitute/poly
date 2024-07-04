{-# OPTIONS --type-in-type #-}
module poly.core where
open import functors
open import prelude

_^ : Set → Set -- Presheaf
I ^ = I → Set

∫ : Set -- Arena
∫ = ∃ _^

_⦅_⦆ : ∫ → Set → Set -- Interpret as a polynomial functor
(A⁺ , A⁻) ⦅ y ⦆ = Σ[ a⁺ ∈ A⁺ ] (A⁻ a⁺ → y)

module _ (A@(A⁺ , A⁻) B@(B⁺ , B⁻) : ∫) where
  ∫[_,_] : Set
  ∫[_,_] = (a⁺ : A⁺) → Σ[ b⁺ ∈ B⁺ ] (B⁻ b⁺ → A⁻ a⁺)
module _ {A@(A⁺ , A⁻) B@(B⁺ , B⁻) : ∫} where
  lens : (get : A⁺ → B⁺)
         (set : (a⁺ : A⁺) → B⁻ (get a⁺) → A⁻ a⁺)
       → ∫[ A , B ]
  lens g s = λ a⁺ → g a⁺ , s a⁺
  get : (l : ∫[ A , B ]) → A⁺ → B⁺
  get l = π₁ ∘ l
  set : (A↝B : ∫[ A , B ]) → (a⁺ : A⁺) → B⁻ (get A↝B a⁺) → A⁻ a⁺
  set l = π₂ ∘ l

instance
    lens-cat : Category ∫[_,_]
    lens-cat = 𝒾: (λ a⁺ → a⁺ , id)
               ▸: (λ l1 l2 a⁺ → let b⁺ , setb = l1 a⁺
                                    c⁺ , setc = l2 b⁺
                                in  c⁺ , setb ∘ setc)
               𝒾▸: (λ _ → refl)
               ▸𝒾: (λ _ → refl)
