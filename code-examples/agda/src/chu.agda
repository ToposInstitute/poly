{-# OPTIONS --type-in-type #-}
module chu where
open import functors
open import prelude
                 
record Chu : Set where
  constructor _,_!_
  field
    _⁺ _⁻ : Set
    _Ω_ : _⁺ → _⁻ → Set

module _ (A@(A⁺ , A⁻ ! _Ω₁_) B@(B⁺ , B⁻ ! _Ω₂_) : Chu) where
    record Chu[_,_] :  Set where -- Morphisms of chu spaces
      constructor _↔_!_
      field
        to : A⁺ → B⁺
        from : B⁻ → A⁻
        adj : ∀ a⁺ b⁻ → to a⁺ Ω₂ b⁻ ≡ a⁺ Ω₁ from b⁻
module _ {A@(A⁺ , A⁻ ! _Ω₁_)
          B@(B⁺ , B⁻ ! _Ω₂_)
          C@(C⁺ , C⁻ ! _Ω₃_) : Chu}
         (F@(f  ↔ fᵗ ! _†₁_) : Chu[ A , B ])
         (G@(g  ↔ gᵗ ! _†₂_) : Chu[ B , C ]) where
    adj-comp : ∀ a⁺ c⁻ → (g ∘ f) a⁺ Ω₃ c⁻ ≡ a⁺ Ω₁ (fᵗ ∘ gᵗ) c⁻
    adj-comp a⁺ c⁻ = trans (f a⁺ †₂    c⁻)  -- g (f a⁺) Ω₃        c⁻
                           (  a⁺ †₁ gᵗ c⁻)  --    f a⁺  Ω₂     gᵗ c⁻
                                            --      a⁺  Ω₁ fᵗ (gᵗ c⁻)
    chu-comp : Chu[ A , C ]
    chu-comp = (g ∘ f) ↔ (fᵗ ∘ gᵗ) ! adj-comp

instance
    chu-cat : Category Chu[_,_]
    chu-cat = 𝒾: (id ↔ id ! λ _ _ → refl)
              ▸: chu-comp
              𝒾▸: (λ (_ ↔ _ ! _†_) → (λ x → _ ↔ _ ! x) ⟨$⟩
                    extensionality2 λ a⁺ b⁻ → trans-refl (a⁺ † b⁻))
              ▸𝒾: (λ _ → refl)
