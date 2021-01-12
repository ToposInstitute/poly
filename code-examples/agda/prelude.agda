module prelude where
open import Function using (id; _∘_) public
open import Data.Sum renaming (inj₁ to Σ₁; inj₂ to Σ₂) using (_⊎_) public
open import Data.Product renaming (proj₁ to π₁; proj₂ to π₂) using (Σ; _×_; _,_; ∃; Σ-syntax) public
open import Agda.Builtin.Unit using (⊤; tt) public
open import Data.Empty using (⊥) public
open import Data.Nat as Nat renaming (suc to ℕs; zero to ℕz; _+_ to _ℕ+_) using (ℕ) public
open import Relation.Binary.PropositionalEquality.Core as Eq using (_≡_; _≢_; refl; sym; trans; subst) renaming (cong to _⟨$⟩_) public
open Eq.≡-Reasoning using (_≡⟨⟩_; step-≡; _∎) public

postulate
  extensionality : {A : Set} {B : A → Set} {f g : (x : A) → B x}
                 → (∀ x → f x ≡ g x) → f ≡ g
extensionality2 : {A : Set} {B : A → Set} {C : (x : A) → B x → Set} {f g : (x : A) (y : B x) → C x y }
                 → (∀ x y → f x y ≡ g x y) → f ≡ g
extensionality2 λλf≡g = extensionality λ x → extensionality λ y → λλf≡g x y

trans-refl : {A : Set} {x y : A} (p : x ≡ y) → trans p refl ≡ p
trans-refl p rewrite p = refl 

subst⋯ : {A : Set} {x y z : A} (P : A → Set) (p : x ≡ y) (q : y ≡ z) (Px : P x)
      → subst P (trans p q) Px ≡ subst P q (subst P p Px)
subst⋯ _ p _ _ rewrite p = refl

_×⁼_ : {A X : Set} {a b : A} {x y : X} → a ≡ b → x ≡ y → (a , x) ≡ (b , y)
_×⁼_ refl refl = refl

_⨄_ : {A B : Set} → (A → Set) → (B → Set) → A ⊎ B → Set
(F ⨄ G) (Σ₁ x) = F x
(F ⨄ G) (Σ₂ y) = G y
_⨃_ _⨉_ : {A B : Set} → (A → Set) → (B → Set) → A × B → Set
F ⨃ G = λ (a , b) → F a ⊎ G b
F ⨉ G = λ (a , b) → F a × G b

_$₁_ : ∀ {A B X : Set} (f : A → B) → A × X → B × X
f $₁ (a , x) = f a , x

_⁻¹ : {A B : Set} → (A → B) → B → Set
_⁻¹ {A} {B} f b = Σ[ a ∈ A ] (f a ≡ b)

uncurry : {a b c : Set} → (a → b → c) → (a × b) → c
uncurry f (a , b) = f a b
