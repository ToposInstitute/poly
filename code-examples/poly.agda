module poly where
open import Function
open import Agda.Builtin.Sigma
open import Data.Product
open import Agda.Builtin.Unit
open import Data.Empty
open import Data.Sum
open import Data.Fin as Fin using (Fin)
open import Data.Nat as Nat using (ℕ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; _≢_; refl; cong)
-- boilerplate
module stream where
  record Stream (a : Set) : Set where
    constructor _∷_
    coinductive
    field
      hd : a
      tl : Stream a
open stream using (Stream)
module functors (f : Set → Set) where
    record Functor : Set₁ where
      field φ : ∀ {a b} → (a → b) → f a → f b
    open Functor ⦃...⦄ public
    record Monad : Set₁ where
      field
        ⦃ Functor⇒Monad ⦄ : Functor
        η : ∀ {a} → a → f a
        μ : ∀ {a} → f (f a) → f a
    open Monad ⦃...⦄ public
open functors public

module list where
  Vect : ∀ {ℓ} → ℕ → Set ℓ → Set ℓ
  Vect n t = Fin n → t
  List : ∀ {ℓ} → Set ℓ → Set ℓ
  List t = Σ[ n ∈ ℕ ] Vect n t
  len : ∀ {ℓ} {a : Set ℓ} → List a → ℕ
  len = fst
  head : ∀ {ℓ} {a : Set ℓ} → (as : List a) → (len as ≢ Nat.zero) → a
  head (Nat.zero , as) n≢0 = ⊥-elim (n≢0 refl)
  head (Nat.suc n , as) _ = as Fin.zero
  tail : ∀ {ℓ} {a : Set ℓ} → (as : List a) → (len as ≢ Nat.zero) → List a
  tail (Nat.zero , as) n≢0 = ⊥-elim (n≢0 refl)
  tail (Nat.suc n , as) _ = n , (as ∘ Fin.inject₁)
open list public
---------------------------

module arena where
  record Arena : Set₁ where
    constructor _◅_
    field
        σ : Set     -- "situation" / "sigma"
        ρ : σ → Set -- "possibility" / "pi"
  open Arena public
  module _ (a : Arena) where
    open Arena a renaming (σ to A⁺; ρ to A⁻)
    Display : Set
    Display = Σ A⁺ A⁻
    _⦅_⦆ : Set → Set -- Interpret a polynomial as a functor
    _⦅_⦆ y = Σ[ a⁺ ∈ A⁺ ](A⁻ a⁺ → y)
    -- a ⦅ ⊤ ⦆ ≡ A⁺
open arena public


module lens where
    module _ (a b : Arena) where
      open Arena a renaming (σ to A⁺; ρ to A⁻)
      open Arena b renaming (σ to B⁺; ρ to B⁻)
      infixr 8 _↝_
      _↝_ : Set
      _↝_ = (a⁺ : A⁺) → Σ[ b⁺ ∈ B⁺ ] (B⁻ b⁺ → A⁻ a⁺)
    module _ {a b : Arena} where
        open Arena a renaming (σ to A⁺; ρ to A⁻)
        open Arena b renaming (σ to B⁺; ρ to B⁻)
        infixl 5 _★_
        get : (a ↝ b) → σ a → σ b
        get l = fst ∘ l
        -- infix notation for get
        _★_ : σ a → (a ↝ b) → σ b
        σa ★ l = get l σa
        set :  (a↝b : a ↝ b) → (σa : σ a) → ρ b (σa ★ a↝b) → ρ a σa
        set l = snd ∘ l
        infixl 4 _#_←_
        -- Infix notation for set
        _#_←_ : (σa : σ a) → (a↝b : a ↝ b) → ρ b (σa ★ a↝b) → ρ a σa
        σa # l ← ρb  = snd (l σa) ρb
        _⇵_ : (get : A⁺ → B⁺) → (set : (a⁺ : A⁺) → B⁻ (get a⁺) → A⁻ a⁺) → a ↝ b
        g ⇵ s = λ a⁺ → (g a⁺) , (s a⁺)

    -- identity in Poly
    idLens : (a : Arena) → a ↝ a
    idLens a =  id ⇵ λ _ → id
    -- composition in Poly
    _▸_ : ∀ {a b c} → (a ↝ b) → (b ↝ c) → (a ↝ c)
    l1 ▸ l2 = (λ x → x ★ l1 ★ l2) ⇵
               λ σa x → σa # l1 ← (σa ★ l1 # l2 ← x)

    module _ {a c : Arena} (l : a ↝ c) where
      open Arena a renaming (σ to A⁺; ρ to A⁻)
      open Arena c renaming (σ to C⁺; ρ to C⁻)
      Factor : Σ[ b ∈ Arena ] (a ↝ b) × (b ↝ c)
      Factor = b , (vertf , cartf) where
        b : Arena
        σ b = A⁺; ρ b = C⁻ ∘ get l
        vertf : a ↝ b
        vertf = id ⇵ set l
        cartf : b ↝ c
        cartf = get l ⇵ λ _ → id
open lens

module arenas where
    -- An arena with non-dependent possibilities
    _◄_ : (i o : Set) → Arena
    o ◄ i = o ◅ (λ _ → i)

    Self : Set → Arena
    Self s = s ◄ s
    Closed : Arena
    Closed = ⊤ ◄ ⊤

    module reflections (t : Set) where
        Exception Emitter Sensor : Arena
        Exception = t ◄ ⊥
        Emitter   = t ◄ ⊤
        Sensor    = ⊤ ◄ t
    open reflections public
    module ev (a : Arena) where
      open Arena a renaming (σ to A⁺; ρ to A⁻)
      ev0 ev1 ev1y : Arena
      ev0 = Exception $ a ⦅ ⊥ ⦆
      fromEv0 : ev0 ↝ a
      fromEv0 = fst ⇵ snd
      ev1 = Exception A⁺ -- (a ⦅ ⊤ ⦆)
      toEv1 : a ↝ ev1
      toEv1 = id ⇵ λ _ → ⊥-elim

      ev1y = Emitter A⁺
      fromEv1y : ev1y ↝ a
      fromEv1y = id ⇵ (λ _ _ → tt)
    open ev public
open arenas public
module lenses {a b : Set} (f : a → b) where
  constant : Exception a ↝ Exception b
  constant = f ⇵ λ _ p → p
  emitter : Emitter a ↝ Emitter b
  emitter = f ⇵ λ _ (.tt) → tt
  sensor : Sensor b ↝ Sensor a
  sensor = (λ (.tt) → tt) ⇵ λ (.tt) → f
  enclose : a ◄ b ↝ ⊤ ◄ ⊤
  enclose = (λ _ → tt) ⇵ λ sh (.tt) → f sh
open lenses public
auto : {m : Set} → Emitter m ↝ Closed
auto {m} = enclose \ _ → tt

module ops where
  module sum where
    zero : Arena
    zero = ⊥ ◄ ⊥
    infixl 5 _⊕_
    _⊕_ : Arena → Arena → Arena
    a ⊕ b = (A⁺ ⊎ B⁺) ◅ (λ{(inj₁ a⁺) → A⁻ a⁺; (inj₂ b⁺) → B⁻ b⁺}) where
        open Arena a renaming (σ to A⁺; ρ to A⁻)
        open Arena b renaming (σ to B⁺; ρ to B⁻)
    sum : (Σ[ ind ∈ Set ](ind → Arena)) → Arena
    sum (ind , arena) = Σ ind (σ ∘ arena) ◅ λ (i , sh) → ρ (arena i) sh
    _⟦+⟧_ : ∀ {a b x y} → (a ↝ b) → (x ↝ y) → (a ⊕ x) ↝ (b ⊕ y)
    _⟦+⟧_ {a} {b} {x} {y} a↝b x↝y  = g ⇵ s where
        open Arena a renaming (σ to A⁺; ρ to A⁻)
        open Arena b renaming (σ to B⁺; ρ to B⁻)
        open Arena x renaming (σ to X⁺; ρ to X⁻)
        open Arena y renaming (σ to Y⁺; ρ to Y⁻)
        g : A⁺ ⊎ X⁺ → B⁺ ⊎ Y⁺
        g (inj₁ a⁺) = inj₁ (a⁺ ★ a↝b)
        g (inj₂ x⁺) = inj₂ (x⁺ ★ x↝y)
        s : (σa⊕x : A⁺ ⊎ X⁺) → ρ (b ⊕ y) (g σa⊕x) → ρ (a ⊕ x) σa⊕x
        s (inj₁ a⁺) b⁻ = a⁺ # a↝b ← b⁻
        s (inj₂ x⁺) y⁻ = x⁺ # x↝y ← y⁻
    -- copair
    _⟦|⟧_ : ∀ {a b x} → a ↝ x → b ↝ x → (a ⊕ b) ↝ x
    _⟦|⟧_ {a} {b} {x} a↝x b↝x = g ⇵ s where
        open Arena a renaming (σ to A⁺; ρ to A⁻)
        open Arena b renaming (σ to B⁺; ρ to B⁻)
        open Arena x renaming (σ to X⁺; ρ to X⁻)
        g : A⁺ ⊎ B⁺ → X⁺
        g (inj₁ a) = a ★ a↝x
        g (inj₂ b) = b ★ b↝x
        s : (σa⊕b : A⁺ ⊎ B⁺) → X⁻ (g σa⊕b) → ρ (a ⊕ b) σa⊕b
        s (inj₁ a) x = a # a↝x ← x
        s (inj₂ b) x = b # b↝x ← x
  module product where
    one = ⊥ ◄ ⊤
    infixl 6 _&_
    _&_ : Arena → Arena → Arena
    a & b = (A⁺ × B⁺) ◅ λ (a⁺ , b⁺) → A⁻ a⁺ ⊎ B⁻ b⁺ where
        open Arena a renaming (σ to A⁺; ρ to A⁻)
        open Arena b renaming (σ to B⁺; ρ to B⁻)

    {-# TERMINATING #-}
    prodList : List Arena → Arena
    prodList (Nat.zero , _) = one
    prodList as@(Nat.suc n , _) = head as (λ()) & prodList (tail as (λ()))

    _⟦&⟧_ : ∀ {a b x y} → (a ↝ b) → (x ↝ y) → (a & x) ↝ (b & y)
    _⟦&⟧_ {a} {b} {x} {y} a↝b x↝y = g ⇵ s where
      open Arena a renaming (σ to A⁺; ρ to A⁻)
      open Arena b renaming (σ to B⁺; ρ to B⁻)
      open Arena x renaming (σ to X⁺; ρ to X⁻)
      open Arena y renaming (σ to Y⁺; ρ to Y⁻)
      g : A⁺ × X⁺ → B⁺ × Y⁺
      g (a⁺ , x⁺) = (a⁺ ★ a↝b) , (x⁺ ★ x↝y)
      s : ((a⁺ , x⁺) : A⁺ × X⁺) → B⁻ (a⁺ ★ a↝b) ⊎ Y⁻ (x⁺ ★ x↝y) → A⁻ a⁺ ⊎ X⁻ x⁺
      s (a⁺ , x⁺) (inj₁ b⁻) = inj₁ (a⁺ # a↝b ← b⁻)
      s (a⁺ , x⁺) (inj₂ y⁻) = inj₂ (x⁺ # x↝y ← y⁻)

    prod : Σ[ ind ∈ Set ](ind → Arena) → Arena
    prod (ind , arena) = ((i : ind) → σ (arena i))
                       ◅ (λ a⁺ → Σ[ i ∈ ind ](ρ (arena i) (a⁺ i)))

    -- pair
    _⟦*⟧_ : ∀ {x a b} → x ↝ a → x ↝ b → x ↝ (a & b)
    _⟦*⟧_ {x} {a} {b} x↝a x↝b = g ⇵ s where
      open Arena a renaming (σ to A⁺; ρ to A⁻)
      open Arena b renaming (σ to B⁺; ρ to B⁻)
      open Arena x renaming (σ to X⁺; ρ to X⁻)
      g : X⁺ → A⁺ × B⁺
      g x⁺ = x⁺ ★ x↝a , x⁺ ★ x↝b
      s : (x⁺ : X⁺) → ρ (a & b) (g x⁺) → X⁻ x⁺
      s x⁺ (inj₁ a⁻) = set x↝a x⁺ a⁻
      s x⁺ (inj₂ b⁻) = set x↝b x⁺ b⁻
  module juxtaposition where
    infixl 6 _⊗_
    _⊗_ : Arena → Arena → Arena
    a ⊗ b = (A⁺ × B⁺) ◅ λ (a⁺ , b⁺) →  A⁻ a⁺ × B⁻ b⁺ where
      open Arena a renaming (σ to A⁺; ρ to A⁻)
      open Arena b renaming (σ to B⁺; ρ to B⁻)

    {-# TERMINATING #-}
    juxtList : List Arena → Arena
    juxtList (Nat.zero , _) = Closed -- ⊤ ◄ ⊤
    juxtList as@(Nat.suc n , _) = head as (λ ()) ⊗ juxtList (tail as (λ ()))

    _⊗⊗⊗_ : ∀ {a b x y} → a ↝ b → x ↝ y → (a ⊗ x) ↝ (b ⊗ y)
    _⊗⊗⊗_ {a} {b} {x} {y} a↝b x↝y = g ⇵ s where
      open Arena a renaming (σ to A⁺; ρ to A⁻)
      open Arena b renaming (σ to B⁺; ρ to B⁻)
      open Arena x renaming (σ to X⁺; ρ to X⁻)
      open Arena y renaming (σ to Y⁺; ρ to Y⁻)
      g : A⁺ × X⁺ → B⁺ × Y⁺
      g (a⁺ , x⁺) = (a⁺ ★ a↝b) , (x⁺ ★ x↝y)
      s : ((a⁺ , x⁺) : A⁺ × X⁺) → B⁻ (a⁺ ★ a↝b) × Y⁻ (x⁺ ★ x↝y) → A⁻ a⁺ × X⁻ x⁺
      s (a⁺ , x⁺) (b⁻ , y⁻) = (a⁺ # a↝b ← b⁻) , (x⁺ # x↝y ← y⁻)
  open juxtaposition public

  module compose where
    _⊚_ : Arena → Arena → Arena
    a ⊚ b = (Σ[ a⁺ ∈ A⁺ ](A⁻ a⁺ → B⁺)) ◅ λ (_ , bs) → ∃ (B⁻ ∘ bs) where
      open Arena a renaming (σ to A⁺; ρ to A⁻)
      open Arena b renaming (σ to B⁺; ρ to B⁻)

    _⟦⊚⟧_ : ∀ {a b x y} → a ↝ b → x ↝ y → (a ⊚ x) ↝ (b ⊚ y)
    _⟦⊚⟧_ {a} {b} {x} {y} a↝b x↝y = g ⇵ s where
      open Arena a renaming (σ to A⁺; ρ to A⁻)
      open Arena b renaming (σ to B⁺; ρ to B⁻)
      open Arena x renaming (σ to X⁺; ρ to X⁻)
      open Arena y renaming (σ to Y⁺; ρ to Y⁻)
      g : (Σ[ a⁺ ∈ A⁺ ](A⁻ a⁺ → X⁺)) → Σ[ b⁺ ∈ B⁺ ](B⁻ b⁺ → Y⁺)
      g (a⁺ , a⁻→x⁺) = (a⁺ ★ a↝b) , (get x↝y ∘ a⁻→x⁺ ∘ set a↝b a⁺)
      s : ((a⁺ , a⁻→x⁺) : (Σ[ a⁺ ∈ A⁺ ](A⁻ a⁺ → X⁺)))
        → ∃ (Y⁻ ∘ get x↝y ∘ a⁻→x⁺ ∘ set a↝b a⁺)
        → ∃ (X⁻ ∘ a⁻→x⁺)
      s (a⁺ , x⁺) (b⁻ , y⁻) = let a⁻ = a⁺ # a↝b ← b⁻
                              in a⁻ , (x⁺ a⁻ # x↝y ← y⁻)

    _ᵒ_ : Arena → ℕ → Arena
    _ ᵒ Nat.zero = Closed
    a ᵒ Nat.suc n = a ⊚ (a ᵒ n)

    _⟦ᵒ⟧_ : {a b : Arena} → a ↝ b → (n : ℕ) → (a ᵒ n) ↝ (b ᵒ n)
    _  ⟦ᵒ⟧ Nat.zero    = idLens Closed
    lens ⟦ᵒ⟧ Nat.suc n = lens ⟦⊚⟧ (lens ⟦ᵒ⟧ n)

  --  EmitterPow : (a : Set) (n : ℕ) → (Emitter a ᵒ n) ↝ Emitter (Vect n a)
 --   EmitterPow a Nat.zero = (λ _ ()) ⇵ (λ sh _ → tt)
--    EmitterPow a (Nat.suc n) = {!!}
  open compose public
open ops public

module _ (f : Set → Set) ⦃ f_functor : Functor f ⦄ where
    lift : Arena → Arena
    lift a = A⁺ ◅ (f ∘ A⁻) where
        open Arena a renaming (σ to A⁺; ρ to A⁻)
    liftLens : ∀ {a b} → a ↝ b → lift a ↝ lift b
    liftLens l = get l ⇵ (φ ∘ set l)

-- every monad in Set gives rise to a comonad in Poly
module lift_comonad {a : Arena} {f : Set → Set} ⦃ f_monad : Monad f ⦄ where
    extract : lift f a ↝ a
    extract = id ⇵ λ _ → η
    duplicate : lift f a ↝ lift f (lift f a)
    duplicate = id ⇵ λ _ → μ

module comonoid where
  record Comonoid : Set₁ where
    field
      domains : Arena
      ε : domains ↝ Closed
      δ : domains ↝ (domains ⊚ domains)

  module comonoids where
    open Comonoid
    MonSensor : (t : Set) → t → (t → t → t) → Comonoid
    domains (MonSensor t ε _∙_) = ⊤ ◄ t
    ε (MonSensor t ε _∙_) = sensor \ _ → ε
    δ (MonSensor t ε _∙_) = (λ (.tt) → (tt , λ _ → tt)) ⇵ λ (.tt) (x , y) → x ∙ y

    ContrGrpd : Set → Comonoid
    domains (ContrGrpd s) = s ◄ s
    ε (ContrGrpd _) = (λ _ → tt) ⇵ (λ sh _ → sh)
    δ (ContrGrpd _) = (λ x → x , id) ⇵ λ sh (_ , b) → b

    TrajComon : Comonoid
    TrajComon = MonSensor ℕ Nat.zero Nat._+_

  module _ (s : Set) where
    open Comonoid (comonoids.ContrGrpd s)
    _^δ_ : (n : ℕ) → (s ◄ s) ↝ ((s ◄ s) ᵒ n)
    _^δ_ Nat.zero  = ε
    _^δ_ (Nat.suc n) = δ ▸ (idLens (s ◄ s) ⟦⊚⟧ (_^δ_ n))

    module _ {a b x y : Arena} where
        duoidal : ((a ⊚ b) ⊗ (x ⊚ y)) ↝ ((a ⊗ x) ⊚ (b ⊗ y))
        duoidal ((a⁺ , bs) , x⁺ , ys) = ((a⁺ , x⁺) , (λ (a⁻ , y⁻) → bs a⁻ , ys y⁻))
                                      , λ ((a⁻ , x⁻) , b⁻ , y⁻) → (a⁻ , b⁻) , (x⁻ , y⁻)
open comonoid

module exp where
  _^_ : Arena → Arena → Arena
  a ^ b = product.prod (A⁺ , λ a⁺ → b ⊚ Exception (A⁻ a⁺)) where
    open Arena a renaming (σ to A⁺; ρ to A⁻)
    open Arena b renaming (σ to B⁺; ρ to B⁻)

    -- prod arena = λ ia⁺ → Σ[ a⁺ ∈ A⁺ ] × (B⁻ b⁺)
    --a ⊚ b = (Σ[ a⁺ ∈ A⁺ ](A⁻ a⁺ → B⁺)) ◅ λ (_ , bs) → ∃ (B⁻ ∘ bs) where

module internal-hom where
  _⊸_ : Arena → Arena → Arena
  a ⊸ b = product.prod (A⁺ , λ a⁺ → b ⊚ (A⁻ a⁺ ◄ ⊤)) where
-- Internal hom has lenses as situations and (indexed) possibilities as the target
--  a ⊸ b = ((a⁺ : A⁺) → Σ[ b⁺ ∈ B⁺ ](B⁻ b⁺ → A⁻ a⁺))
--        ◅ λ bs → Σ[ a⁺ ∈ A⁺ ](Σ (B⁻ (fst (bs a⁺)))(λ _ → ⊤))
    --  ≡ (a ↝ b) ◅ λ bs → Σ[ a⁺ ∈ A⁺ ](Σ (B⁻ (a⁺ ⋆ bs))(λ _ → ⊤))
    --  ≅ (a ↝ b) ◅ λ bs → (Σ A⁺ $ B⁻ ∘ get bs)
    open Arena a renaming (σ to A⁺; ρ to A⁻)
    open Arena b renaming (σ to B⁺; ρ to B⁻)
  eval : ∀ {a b} → (a ⊗ (a ⊸ b)) ↝ b
  eval {a} {b} = g ⇵ s where
    open Arena a renaming (σ to A⁺; ρ to A⁻)
    open Arena b renaming (σ to B⁺; ρ to B⁻)
    g : (A⁺ × ((a⁺ : A⁺) → Σ[ b⁺ ∈ B⁺ ] ((b⁻ : B⁻ b⁺) → A⁻ a⁺))) → B⁺
    g (a⁺ , bs) = proj₁ (bs a⁺)
    s : ((a⁺ , bs) : (A⁺ × ((a+ : A⁺) → Σ[ b⁺ ∈ B⁺ ] (B⁻ b⁺ → A⁻ a+))))
      → B⁻ (fst (bs a⁺))
      → Σ[ a⁻ ∈ A⁻ a⁺ ] Σ[ a+ ∈ A⁺ ] Σ[ b⁻ ∈ B⁻ (proj₁ (bs a+)) ] ⊤
    s (a⁺ , bs) b⁻ = let (_ , a⁻) = bs a⁺
                     in a⁻ b⁻ , (a⁺ , b⁻ , tt)

module dynamical where
    record DynSystem : Set₁ where
      field
        state : Set
        body : Arena
        pheno : (state ◄ state) ↝ body
    open DynSystem public
    static : DynSystem
    state static = ⊤
    body static = ⊤ ◄ ⊤
    pheno static =  id ⇵ \ _ (.tt) → tt -- emitter id -- idLens

    module _ (dyn1 dyn2 : DynSystem) where
        _XXX_ : DynSystem
        state _XXX_ = state dyn1 × state dyn2
        body _XXX_  = body  dyn1 ⊗ body  dyn2
        pheno _XXX_ (s , t)             = ((s ★ pheno dyn1)     , (t ★ pheno dyn2))
                            , λ (p , q) →  (s # pheno dyn1 ← p) , (t # pheno dyn2 ← q)
    {-# TERMINATING #-}
    juxtapose : List DynSystem → DynSystem
    juxtapose (Nat.zero , _) = static
    juxtapose ds@(Nat.suc n , _) = head ds (λ ()) XXX juxtapose (tail ds λ ())

    install : (d : DynSystem) (a : Arena) → (body d ↝ a) → DynSystem
    install d a l = record {state = state d; body = a; pheno = pheno d ▸ l}

    speedup : DynSystem → ℕ → DynSystem
    state (speedup dyn n) = state dyn
    body (speedup dyn n) = body dyn ᵒ n
    pheno (speedup dyn n) = (state dyn ^δ n) ▸ (pheno dyn ⟦ᵒ⟧ n)

    module Dyn (d : DynSystem) (e : body d ↝ (⊤ ◄ ⊤)) where
        open Stream
        run : state d → Stream (σ $ body d)
        hd (run s) = s ★ pheno d
        tl (run s) = run (s # pheno d ▸ e ← tt)
open dynamical

record Behavior (a : Arena) : Set where
    coinductive
    constructor _∷_
    field
      hd : σ a
      tl : ρ a hd → Behavior a
module behavior where
    module _ {a : Arena} (phys : a ↝ (⊤ ◄ ⊤)) where
      toStream : Behavior a → Stream (σ a)
      Stream.hd (toStream b) = Behavior.hd b
      Stream.tl (toStream b) = toStream (Behavior.tl b (Behavior.hd b # phys ← tt))
    module _ (d : DynSystem) where
      dynBehavior : state d → Behavior (body d)
      Behavior.hd (dynBehavior s) = s ★ pheno d
      Behavior.tl (dynBehavior s) d' = dynBehavior (s # pheno d ← d')
      run : (body d ↝ Closed) → state d → Stream (σ $ body d)
      run phys s = toStream phys (dynBehavior s)
