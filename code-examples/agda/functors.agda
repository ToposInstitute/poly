{-# OPTIONS --type-in-type #-}
module functors where
open import prelude

record Category {O : Set} (𝒞[_,_] : O → O → Set) : Set where
  constructor 𝒾:_▸:_𝒾▸:_▸𝒾:
  infixl 8 _▸_
  field
    𝒾 : ∀ {x} → 𝒞[ x , x ]
    _▸_ : ∀ {x y z} → 𝒞[ x , y ] → 𝒞[ y , z ] → 𝒞[ x , z ]
    𝒾▸ : ∀ {x y} (f : 𝒞[ x , y ]) → (𝒾 ▸ f) ≡ f
    ▸𝒾 : ∀ {x y} (f : 𝒞[ x , y ]) → (f ▸ 𝒾) ≡ f
open Category ⦃...⦄ public

record Functor {A : Set} {𝒜[_,_] : A → A → Set}
               {B : Set} {ℬ[_,_] : B → B → Set}
               (f : A → B) : Set where
  constructor φ:_𝒾:_▸:
  field
    ⦃ cat₁ ⦄ : Category {A} 𝒜[_,_]
    ⦃ cat₂ ⦄ : Category {B} ℬ[_,_]
    φ : ∀ {a b} → 𝒜[ a , b ] → ℬ[ f a , f b ]
    functor-id : ∀ {a} → φ {a} 𝒾 ≡ 𝒾
    functor-comp : ∀ {A B C} → (f : 𝒜[ A , B ]) (g : 𝒜[ B , C ])
                 → φ (f ▸ g) ≡ φ f ▸ φ g
open Functor ⦃...⦄ public

record Nat {A : Set} {𝒜[_,_] : A → A → Set}
           {B : Set} {ℬ[_,_] : B → B → Set}
           {F : A → B} {G : A → B}
           (α : (x : A) → ℬ[ F x , G x ]) : Set where
  field
    overlap ⦃ fun₁ ⦄ : Functor {A} {𝒜[_,_]} {B} {ℬ[_,_]} F
    overlap ⦃ fun₂ ⦄ : Functor {A} {𝒜[_,_]} {B} {ℬ[_,_]} G
    nat : ∀ {x y : A} (f : 𝒜[ x , y ]) → let _▹_ = _▸_ ⦃ cat₂ ⦄
                                          in φ f ▹ α y ≡ α x ▹ φ f

module _ {A : Set} {𝒜[_,_] : A → A → Set}  where
    instance
        id-functor : ⦃ Category 𝒜[_,_] ⦄ → Functor id
        id-functor = φ: id
                     𝒾: refl
                     ▸: λ f g → refl
    record Monad (f : A → A) : Set where
      field
        ⦃ functor ⦄ : Functor {_} {𝒜[_,_]} {_} {𝒜[_,_]} f
        η : ∀ {a} → 𝒜[ a , f a ]
        μ : ∀ {a} → 𝒜[ f (f a) , f a ]
    open Monad ⦃...⦄ public

{-
    record Lift[_⇒_] (pre post : (Set → Set) → Set) (t : (Set → Set) → Set → Set) : Set where
      field
        ⦃ lifted ⦄ : ∀ {f} → post (t f)
        lift : {f : Set → Set} {a : Set} → ⦃ pre f ⦄ → f a → t f a 
    open Lift[_⇒_] ⦃...⦄ public
-}

Cat[_,_] : Set → Set → Set
Cat[ a , b ] = a → b

instance
  Cat-cat : Category Cat[_,_]
  Cat-cat = record { 𝒾 = id ; _▸_ = λ f g → g ∘ f ; 𝒾▸ = λ _ → refl; ▸𝒾 = λ _ → refl}
instance
  ≡-cat : ∀ {A} → Category {A} (λ a b → a ≡ b)
  𝒾 {{≡-cat}} = refl
  _▸_ {{≡-cat}} = trans
  𝒾▸ {{≡-cat}} _ = refl
  ▸𝒾 {{≡-cat}} x≡y rewrite x≡y = refl
instance
    ×-cat : ∀ {A 𝒜[_,_]} ⦃ 𝒜 : Category {A} 𝒜[_,_] ⦄
              {B ℬ[_,_]} ⦃ ℬ : Category {B} ℬ[_,_] ⦄
          → Category {A × B} (λ (a , b) (a′ , b′) → 𝒜[ a , a′ ] × ℬ[ b , b′ ])
    𝒾 {{×-cat}} = 𝒾 , 𝒾
    _▸_ {{×-cat}} (f , f′ ) ( g , g′ ) = f ▸ g , f′ ▸ g′
    𝒾▸ {{×-cat}} (f , g) = 𝒾▸ f ×⁼ 𝒾▸ g
    ▸𝒾 {{×-cat}} (f , g) = ▸𝒾 f ×⁼ ▸𝒾 g

data _ᵒᵖ {A : Set} (𝒜 : A → A → Set) : A → A → Set where
  _ᵗ : ∀ {y x} → 𝒜(y )( x) → (𝒜 ᵒᵖ)(x )( y)

instance
    op-cat  : {A : Set} {𝒜[_,_] : A → A → Set} ⦃ 𝒜 : Category {A} 𝒜[_,_] ⦄
            → Category (𝒜[_,_] ᵒᵖ) 
    𝒾 {{op-cat}}  = 𝒾 ᵗ
    _▸_ {{op-cat}} (f ᵗ) (g ᵗ) = (g ▸ f) ᵗ
    𝒾▸ {{op-cat}} (f ᵗ) = _ᵗ ⟨$⟩ ▸𝒾 f 
    ▸𝒾 {{op-cat}} (f ᵗ) = _ᵗ ⟨$⟩ 𝒾▸ f
