{-# OPTIONS --type-in-type #-}
module chu.lens where
open import prelude
open import functors
open import chu
open import poly.core

→∫ : Chu → ∫
→∫ (A⁺ , A⁻ ! Ω) = A⁺ , λ a⁺ → ∃ (Ω a⁺)
      
→Lens : {A B : Chu} → Chu[ A , B ] → ∫[ →∫ A , →∫ B ]
→Lens (f ↔ fᵗ ! †)  a⁺ = f a⁺ , λ (b⁻ , fa⁺Ωb⁻) → fᵗ b⁻ , subst id († a⁺ b⁻) fa⁺Ωb⁻

module _ {A B C : Chu}
         (F@(f ↔ fᵗ ! _†₁_) : Chu[ A , B ])
         (G@(g ↔ gᵗ ! _†₂_) : Chu[ B , C ]) where

    comp₂ : ∀ a⁺ → π₂  (→Lens (F ▸       G) a⁺)
                 ≡ π₂ ((→Lens  F ▸ →Lens G) a⁺)
    comp₂ a⁺ = extensionality λ ( c⁻ , gfaΩc ) → (λ x → (fᵗ ∘ gᵗ) c⁻ , x) ⟨$⟩
               subst⋯ id (f a⁺ †₂ c⁻) (a⁺ †₁ gᵗ c⁻) gfaΩc

    comp∀ : ∀ a⁺ → →Lens (F ▸ G) a⁺ ≡ (→Lens F ▸ →Lens G) a⁺
    comp∀ a⁺ rewrite comp₂ a⁺ = refl

instance
    open Chu[_,_]
    chu-lens-functor : Functor →∫
    chu-lens-functor = φ: →Lens
                       𝒾: refl
                       ▸: λ F G → extensionality (comp∀ F G)
