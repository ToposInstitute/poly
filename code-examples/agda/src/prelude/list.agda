module prelude.list where
open import Data.Nat renaming (zero to z; suc to s)
open import Data.Fin as Fin using (Fin)
import Data.Fin as Fin renaming (zero to z; suc to s)
open import Agda.Builtin.Sigma
open import Data.Product
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong)
open import Data.Empty
open import Function

Vect : ∀ {ℓ} → ℕ → Set ℓ → Set ℓ
Vect n t = Fin n → t
List : ∀ {ℓ} → Set ℓ → Set ℓ
List t = Σ[ n ∈ ℕ ] Vect n t
len : ∀ {ℓ} {a : Set ℓ} → List a → ℕ
len = fst
head : ∀ {ℓ} {a : Set ℓ} → (as : List a) → (len as ≢ z) → a
head (z , as) n≢0 = ⊥-elim (n≢0 refl)
head (s n , as) _ = as Fin.z
tail : ∀ {ℓ} {a : Set ℓ} → (as : List a) → (len as ≢ z) → List a
tail (z , as) n≢0 = ⊥-elim (n≢0 refl)
tail (s n , as) _ = n , (as ∘ Fin.inject₁)
