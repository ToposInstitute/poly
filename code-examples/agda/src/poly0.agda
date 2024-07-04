{-# OPTIONS --type-in-type #-}
module poly0 where
open import prelude
open import functors
open import poly.core public

variable
  A B C X Y : ∫
  I A⁺ B⁺ C⁺ X⁺ Y⁺ : Set
  A⁻ : A⁺ → Set
  B⁻ : B⁺ → Set
  C⁻ : C⁺ → Set
  X⁻ : X⁺ → Set
  Y⁻ : Y⁺ → Set
  

∃⊤ ∃⊥ ⊤∫ ∫∫ : Set → ∫
∃⊤ a = a , λ _ → ⊤
∃⊥ a = a , λ _ → ⊥
⊤∫ a = ⊤ , λ _ → a
∫∫ a = a , λ _ → a
𝒴 𝟘 : ∫
𝒴 = ⊤ , λ _ → ⊤
𝟘  = ⊥ , λ _ → ⊥

module _ {A@(A⁺ , A⁻) B@(B⁺ , B⁻) : ∫} where
  infixl 5 _★_
  -- infix notatjon for get
  _★_ : A⁺ → (l : ∫[ A , B ]) → B⁺
  σa ★ l = get l σa
  infixr 4 _#_←_
  -- Infix notatjon for set
  _#_←_ : (a⁺ : A⁺) → (A↝B : ∫[ A , B ]) → B⁻ (a⁺ ★ A↝B) → A⁻ a⁺
  a⁺ # l ← b⁻ = π₂ (l a⁺) b⁻
  _↕_ : (get : A⁺ → B⁺) → (set : (a⁺ : A⁺) → B⁻ (get a⁺) → A⁻ a⁺) → ∫[ A , B ]
  g ↕ s = λ a⁺ → (g a⁺) , (s a⁺)

module _ {A@(A⁺ , A⁻) C@(C⁺ , C⁻) : ∫} (l : ∫[ A , C ]) where
    -- vertical and cartesian factorization
    Factor : Σ[ B ∈ ∫ ] (∫[ A , B ]) × (∫[ B , C ]) 
    Factor = (A⁺ , C⁻ ∘ get l)
           , id ↕ set l
           , get l ↕ λ _ → id

module lenses (f : A⁺ → B⁺) where
    constant : ∫[ ∃⊥ A⁺ , ∃⊥ B⁺ ]
    emitter  : ∫[ ∃⊤ A⁺ , ∃⊤ B⁺ ]
    sensor   : ∫[ ⊤∫ B⁺ , ⊤∫ A⁺ ]
    constant a⁺ = f a⁺ , id
    emitter  a⁺ = f a⁺ , λ _ → tt
    sensor   _  = tt   , f
open lenses public
enclose : ((a⁺ : A⁺) → B⁻ a⁺) → ∫[ (A⁺ , B⁻) , 𝒴 ]
enclose f a⁺ = tt , λ _ → f a⁺
auto : ∫[ ∃⊤ A⁺ , 𝒴 ]
auto = enclose λ _ → tt


{-
lift∫ : (f : Set → Set) → ∫ → ∫
lift∫ f (A⁺ , A⁻) = A⁺ , f ∘ A⁻

liftLens : ∀ {A B} (f : Set → Set) → ∫[ A , B ] → ∫[ lift∫ f A , lift∫ f B ]
liftLens f l a⁺ with l a⁺
... | b⁺ , setb = b⁺ , φ setb
-}

{- 
module lift_comonad (f : Set → Set) {A : ∫} ⦃ f_monad : Monad f ⦄ where
    extract : lift∫ f A ↝ A
    extract a⁺ = a⁺ , η f_monad
    -- id ↕ λ _ → η
    duplicate : lift∫ f A ↝ lift∫ f (lift∫ f A)
    duplicate a⁺ = a⁺ , μ
    -}

module poly-ops where
  infixl 6 _⊗_
  infixl 5 _⊕_
  _⊕_ _⊗_ _⊠_ _⊚_ : ∫ → ∫ → ∫
  (A⁺ , A⁻) ⊕ (B⁺ , B⁻) = (A⁺ ⊎ B⁺) , (A⁻ ⨄ B⁻) -- coproduct
  (A⁺ , A⁻) ⊗ (B⁺ , B⁻) = (A⁺ × B⁺) , (A⁻ ⨃ B⁻) -- product
  (A⁺ , A⁻) ⊠ (B⁺ , B⁻) = (A⁺ × B⁺) , (A⁻ ⨉ B⁻) -- juxtapose
  (A⁺ , A⁻) ⊚ (B⁺ , B⁻) = (Σ[ a⁺ ∈ A⁺ ](A⁻ a⁺ → B⁺)) -- compose
                        , λ (_ , bs) → ∃ (B⁻ ∘ bs)

  -- N-ary
  Σ⊕ : (I → ∫) → ∫
  Σ⊕ {I = I} A = Σ I (π₁ ∘ A) , λ (i , a⁺) → π₂ (A i) a⁺
  Π⊗ : (I → ∫) → ∫
  Π⊗ {I = I} a = ((i : I) → π₁ (a i))
               , λ a⁺ → Σ[ i ∈ I ](π₂ (a i) (a⁺ i))
  Π⊠ : (I → ∫) → ∫
  Π⊠ {I = I} a = ((i : I) → π₁ (a i))
               , (λ a⁺ → (i : I) -> π₂ (a i) (a⁺ i))
  _ᵒ_ : ∫ → ℕ → ∫
  _ ᵒ ℕz = 𝒴
  a ᵒ ℕs n = a ⊚ (a ᵒ n)
open poly-ops public

module lens-ops where
  _⟦+⟧_ : ∀ {a b x y} → ∫[ a , b ] → ∫[ x , y ] → ∫[ a ⊕ x , b ⊕ y ] -- coproduct
  _⟦|⟧_ : ∀ {a b x  } → ∫[ a , x ] → ∫[ b , x ] → ∫[ a ⊕ b ,     x ] -- copair
  _⟦⊗⟧_ : ∀ {a b x y} → ∫[ a , b ] → ∫[ x , y ] → ∫[ a ⊗ x , b ⊗ y ] -- product
  _⟦×⟧_ : ∀ {x a b  } → ∫[ x , a ] → ∫[ x , b ] → ∫[ x     , a ⊗ b ] -- pair
  _⟦⊠⟧_ : ∀ {a b x y} → ∫[ a , b ] → ∫[ x , y ] → ∫[ a ⊠ x , b ⊠ y ] -- juxtaposition
  _⟦⊚⟧_ : ∀ {a b x y} → ∫[ a , b ] → ∫[ x , y ] → ∫[ a ⊚ x , b ⊚ y ] -- composition

  (a↝b ⟦+⟧ x↝y) = λ{(Σ₁ a⁺) → let b⁺ , setb = a↝b a⁺ in Σ₁ b⁺  , setb
                   ;(Σ₂ x⁺) → let y⁺ , sety = x↝y x⁺ in Σ₂ y⁺  , sety}

  (a↝x ⟦|⟧ b↝x) = λ{(Σ₁ a⁺) → a↝x a⁺
                   ;(Σ₂ b⁺) → b↝x b⁺}

  (a↝b ⟦⊗⟧ x↝y) (a⁺ , x⁺) with a↝b a⁺ | x↝y x⁺
  ... | b⁺ , setb | y⁺ , sety = (b⁺ , y⁺)
                  , λ{(Σ₁ b⁻) → Σ₁ (setb b⁻)
                     ;(Σ₂ y⁻) → Σ₂ (sety y⁻)}

  _⟦×⟧_ x↝a x↝b x⁺ with x↝a x⁺ | x↝b x⁺
  ... | a⁺ , seta | b⁺ , setb = (a⁺ , b⁺) , λ{(Σ₁ a⁻) → seta a⁻
                                             ;(Σ₂ b⁻) → setb b⁻}

  _⟦⊠⟧_ a↝b x↝y (a⁺ , x⁺) = ((a⁺ ★ a↝b) , (x⁺ ★ x↝y))
            , λ (b⁻ , y⁻) → (a⁺ # a↝b ← b⁻) , (x⁺ # x↝y ← y⁻)

  (a↝b ⟦⊚⟧ x↝y) (a⁺ , a⁻→x⁺) with a↝b a⁺
  ... | b⁺ , setb = (b⁺ , get x↝y ∘ a⁻→x⁺ ∘ setb)
                  , λ (b⁻ , y⁻) → let a⁻ = setb b⁻
                                  in a⁻ , (a⁻→x⁺ a⁻ # x↝y ← y⁻)

  -- N-ary
  Π⟦⊠⟧ : {as bs : I → ∫}
        → ((i : I) → (∫[ as i , bs i ]))
        → ∫[ Π⊠ as , Π⊠ bs ]
  Π⟦⊠⟧ ls as⁺ = (λ i → as⁺ i ★ ls i)
          , (λ dbs i → as⁺ i # ls i ← dbs i)
  _⟦ᵒ⟧_ : ∫[ A , B ] → (n : ℕ) → ∫[ A ᵒ n , B ᵒ n ]
  _⟦ᵒ⟧_ {a} {b} l = go where
    go : (n : ℕ) → ∫[ a ᵒ n , b ᵒ n ]
    go ℕz    = 𝒾 {x = 𝒴}
    go (ℕs n) = l ⟦⊚⟧ (go n)
open lens-ops public
