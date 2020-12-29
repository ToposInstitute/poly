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

module arena where
  record Arena : Set₁ where
    constructor _◅_
    field
        ς : Set     -- "situation" / "sigma" / "shape"
        ρ : ς → Set -- "possibility" / "pi" / "position"
  open Arena public
  module _ (a : Arena) where
    open Arena a renaming (ς to A⁺; ρ to A⁻)
    Display : Set
    Display = Σ A⁺ A⁻
    _⦅_⦆ : Set → Set -- Interpret a polynomial as a functor
    _⦅_⦆ y = Σ[ a⁺ ∈ A⁺ ](A⁻ a⁺ → y)
    -- a ⦅ ⊤ ⦆ ≡ A⁺
open arena public


module lens where
    module _ (a b : Arena) where
      open Arena a renaming (ς to A⁺; ρ to A⁻)
      open Arena b renaming (ς to B⁺; ρ to B⁻)
      infixr 8 _↝_
      _↝_ : Set
      _↝_ = (a⁺ : A⁺) → Σ[ b⁺ ∈ B⁺ ] (B⁻ b⁺ → A⁻ a⁺)
    module _ {a b : Arena} where
        open Arena a renaming (ς to A⁺; ρ to A⁻)
        open Arena b renaming (ς to B⁺; ρ to B⁻)
        infixl 5 _★_
        get : (a ↝ b) → ς a → ς b
        get l = fst ∘ l
        _★_ : ς a → (a ↝ b) → ς b
        ςa ★ l = get l ςa
        set :  (a↝b : a ↝ b) → (ςa : ς a) → ρ b (ςa ★ a↝b) → ρ a ςa
        set l = snd ∘ l
        infixl 4 _#_←_
        _#_←_ : (ςa : ς a) → (a↝b : a ↝ b) → ρ b (ςa ★ a↝b) → ρ a ςa
        ςa # l ← ρb  = snd (l ςa) ρb
        _⇵_ : (get : A⁺ → B⁺) → (set : (a⁺ : A⁺) → B⁻ (get a⁺) → A⁻ a⁺) → a ↝ b
        g ⇵ s = λ a⁺ → (g a⁺) , (s a⁺)
        
    idLens : (a : Arena) → a ↝ a
    idLens a =  id ⇵ λ _ → id
    _▸_ : ∀ {a b c} → (a ↝ b) → (b ↝ c) → (a ↝ c)
    l1 ▸ l2 = (λ x → x ★ l1 ★ l2) ⇵
               λ ςa x → ςa # l1 ← (ςa ★ l1 # l2 ← x)

    module _ {a c : Arena} (l : a ↝ c) where
      open Arena a renaming (ς to A⁺; ρ to A⁻)
      open Arena c renaming (ς to C⁺; ρ to C⁻)
      Factor : Σ[ b ∈ Arena ] (a ↝ b) × (b ↝ c)
      Factor = b , (vertf , cartf) where
        b : Arena
        ς b = A⁺; ρ b = C⁻ ∘ get l
        vertf : a ↝ b
        vertf = id ⇵ set l
        cartf : b ↝ c
        cartf = get l ⇵ λ _ → id
open lens

module arenas where
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
      open Arena a renaming (ς to A⁺; ρ to A⁻)
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

module functors (f : Set → Set) where
    record Functor : Set₁ where
      field φ : ∀ {a b} → (a → b) → f a → f b
    open Functor ⦃...⦄
    record Monad : Set₁ where
      field
        ⦃ Functor⇒Monad ⦄ : Functor
        η : ∀ {a} → a → f a
        μ : ∀ {a} → f (f a) → f a
    open Monad ⦃...⦄

  
    module _ ⦃ f_functor : Functor ⦄ where
      lift : Arena → Arena
      lift a = A⁺ ◅ (f ∘ A⁻) where
          open Arena a renaming (ς to A⁺; ρ to A⁻)
      liftLens : ∀ {a b} → a ↝ b → lift a ↝ lift b
      liftLens l = get l ⇵ (φ ∘ set l)


    module lift_comonad {a : Arena} ⦃ f_monad : Monad ⦄ where
      extract : lift a ↝ a
      extract = id ⇵ λ _ → η
      duplicate : lift a ↝ lift (lift a)
      duplicate = id ⇵ λ _ → μ

module stream where
  record Stream (a : Set) : Set where
    constructor _∷_
    coinductive
    field
      hd : a
      tl : Stream a
open stream using (Stream)
  
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
  
  

module ops where
  module sum where
    zero : Arena
    zero = ⊥ ◄ ⊥
    infixl 5 _⊕_
    _⊕_ : Arena → Arena → Arena
    a ⊕ b = (A⁺ ⊎ B⁺) ◅ (λ{(inj₁ a⁺) → A⁻ a⁺; (inj₂ b⁺) → B⁻ b⁺}) where
        open Arena a renaming (ς to A⁺; ρ to A⁻)
        open Arena b renaming (ς to B⁺; ρ to B⁻)
    sum : (Σ[ ind ∈ Set ](ind → Arena)) → Arena
    sum (ind , arena) = Σ ind (ς ∘ arena) ◅ λ (i , sh) → ρ (arena i) sh
    _⟦+⟧_ : ∀ {a b x y} → (a ↝ b) → (x ↝ y) → (a ⊕ x) ↝ (b ⊕ y)
    _⟦+⟧_ {a} {b} {x} {y} a↝b x↝y  = g ⇵ s where
        open Arena a renaming (ς to A⁺; ρ to A⁻)
        open Arena b renaming (ς to B⁺; ρ to B⁻)
        open Arena x renaming (ς to X⁺; ρ to X⁻)
        open Arena y renaming (ς to Y⁺; ρ to Y⁻)
        g : A⁺ ⊎ X⁺ → B⁺ ⊎ Y⁺
        g (inj₁ a⁺) = inj₁ (a⁺ ★ a↝b)
        g (inj₂ x⁺) = inj₂ (x⁺ ★ x↝y)
        s : (ςa⊕x : A⁺ ⊎ X⁺) → ρ (b ⊕ y) (g ςa⊕x) → ρ (a ⊕ x) ςa⊕x
        s (inj₁ a⁺) b⁻ = a⁺ # a↝b ← b⁻
        s (inj₂ x⁺) y⁻ = x⁺ # x↝y ← y⁻
    -- copair
    _⟦|⟧_ : ∀ {a b x} → a ↝ x → b ↝ x → (a ⊕ b) ↝ x
    _⟦|⟧_ {a} {b} {x} a↝x b↝x = g ⇵ s where
        open Arena a renaming (ς to A⁺; ρ to A⁻)
        open Arena b renaming (ς to B⁺; ρ to B⁻)
        open Arena x renaming (ς to X⁺; ρ to X⁻)
        g : A⁺ ⊎ B⁺ → X⁺
        g (inj₁ a) = a ★ a↝x
        g (inj₂ b) = b ★ b↝x
        s : (ςa⊕b : A⁺ ⊎ B⁺) → X⁻ (g ςa⊕b) → ρ (a ⊕ b) ςa⊕b
        s (inj₁ a) x = a # a↝x ← x
        s (inj₂ b) x = b # b↝x ← x
  module product where
    one = ⊥ ◄ ⊤
    infixl 6 _&_
    _&_ : Arena → Arena → Arena
    a & b = (A⁺ × B⁺) ◅ λ (a⁺ , b⁺) → A⁻ a⁺ ⊎ B⁻ b⁺ where
        open Arena a renaming (ς to A⁺; ρ to A⁻)
        open Arena b renaming (ς to B⁺; ρ to B⁻)

    {-# TERMINATING #-}
    prodList : List Arena → Arena
    prodList (Nat.zero , _) = one
    prodList as@(Nat.suc n , _) = head as (λ()) & prodList (tail as (λ()))

    _⟦&⟧_ : ∀ {a b x y} → (a ↝ b) → (x ↝ y) → (a & x) ↝ (b & y)
    _⟦&⟧_ {a} {b} {x} {y} a↝b x↝y = g ⇵ s where
      open Arena a renaming (ς to A⁺; ρ to A⁻)
      open Arena b renaming (ς to B⁺; ρ to B⁻)
      open Arena x renaming (ς to X⁺; ρ to X⁻)
      open Arena y renaming (ς to Y⁺; ρ to Y⁻)
      g : A⁺ × X⁺ → B⁺ × Y⁺
      g (a⁺ , x⁺) = (a⁺ ★ a↝b) , (x⁺ ★ x↝y)
      s : ((a⁺ , x⁺) : A⁺ × X⁺) → B⁻ (a⁺ ★ a↝b) ⊎ Y⁻ (x⁺ ★ x↝y) → A⁻ a⁺ ⊎ X⁻ x⁺
      s (a⁺ , x⁺) (inj₁ b⁻) = inj₁ (a⁺ # a↝b ← b⁻)
      s (a⁺ , x⁺) (inj₂ y⁻) = inj₂ (x⁺ # x↝y ← y⁻)
    
-- TODO: remove Σ
    prod : Σ[ ind ∈ Set ](ind → Arena) → Arena
    prod (ind , arena) = ((i : ind) → ς (arena i))
                       ◅ (λ a⁺ → Σ[ i ∈ ind ](ρ (arena i) (a⁺ i)))

    -- pair
    _⟦*⟧_ : ∀ {x a b} → x ↝ a → x ↝ b → x ↝ (a & b)
    _⟦*⟧_ {x} {a} {b} x↝a x↝b = g ⇵ s where
      open Arena a renaming (ς to A⁺; ρ to A⁻)
      open Arena b renaming (ς to B⁺; ρ to B⁻)
      open Arena x renaming (ς to X⁺; ρ to X⁻)
      g : X⁺ → A⁺ × B⁺
      g x⁺ = x⁺ ★ x↝a , x⁺ ★ x↝b
      s : (x⁺ : X⁺) → ρ (a & b) (g x⁺) → X⁻ x⁺
      s x⁺ (inj₁ a⁻) = set x↝a x⁺ a⁻
      s x⁺ (inj₂ b⁻) = set x↝b x⁺ b⁻
  module juxtaposition where
    infixl 6 _⅋_
    _⅋_ : Arena → Arena → Arena
    a ⅋ b = (A⁺ × B⁺) ◅ λ (a⁺ , b⁺) →  A⁻ a⁺ × B⁻ b⁺ where
      open Arena a renaming (ς to A⁺; ρ to A⁻)
      open Arena b renaming (ς to B⁺; ρ to B⁻)

    {-# TERMINATING #-}
    juxtList : List Arena → Arena
    juxtList (Nat.zero , _) = Closed -- ⊤ ◄ ⊤
    juxtList as@(Nat.suc n , _) = head as (λ ()) ⅋ juxtList (tail as (λ ()))

    _⅋⅋⅋_ : ∀ {a b x y} → a ↝ b → x ↝ y → (a ⅋ x) ↝ (b ⅋ y)
    _⅋⅋⅋_ {a} {b} {x} {y} a↝b x↝y = g ⇵ s where
      open Arena a renaming (ς to A⁺; ρ to A⁻)
      open Arena b renaming (ς to B⁺; ρ to B⁻)
      open Arena x renaming (ς to X⁺; ρ to X⁻)
      open Arena y renaming (ς to Y⁺; ρ to Y⁻)
      g : A⁺ × X⁺ → B⁺ × Y⁺
      g (a⁺ , x⁺) = (a⁺ ★ a↝b) , (x⁺ ★ x↝y)
      s : ((a⁺ , x⁺) : A⁺ × X⁺) → B⁻ (a⁺ ★ a↝b) × Y⁻ (x⁺ ★ x↝y) → A⁻ a⁺ × X⁻ x⁺
      s (a⁺ , x⁺) (b⁻ , y⁻) = (a⁺ # a↝b ← b⁻) , (x⁺ # x↝y ← y⁻)
  open juxtaposition public

  module compose where
    _⊗_ : Arena → Arena → Arena
    a ⊗ b = (Σ[ a⁺ ∈ A⁺ ](A⁻ a⁺ → B⁺)) ◅ λ (_ , bs) → ∃ (B⁻ ∘ bs) where
      open Arena a renaming (ς to A⁺; ρ to A⁻)
      open Arena b renaming (ς to B⁺; ρ to B⁻)

    _⟦⊗⟧_ : ∀ {a b x y} → a ↝ b → x ↝ y → (a ⊗ x) ↝ (b ⊗ y)
    _⟦⊗⟧_ {a} {b} {x} {y} a↝b x↝y = g ⇵ s where
      open Arena a renaming (ς to A⁺; ρ to A⁻)
      open Arena b renaming (ς to B⁺; ρ to B⁻)
      open Arena x renaming (ς to X⁺; ρ to X⁻)
      open Arena y renaming (ς to Y⁺; ρ to Y⁻)
      g : (Σ[ a⁺ ∈ A⁺ ](A⁻ a⁺ → X⁺)) → Σ[ b⁺ ∈ B⁺ ](B⁻ b⁺ → Y⁺)
      g (a⁺ , a⁻→x⁺) = (a⁺ ★ a↝b) , (get x↝y ∘ a⁻→x⁺ ∘ set a↝b a⁺)
      s : ((a⁺ , a⁻→x⁺) : (Σ[ a⁺ ∈ A⁺ ](A⁻ a⁺ → X⁺)))
        → ∃ (Y⁻ ∘ get x↝y ∘ a⁻→x⁺ ∘ set a↝b a⁺)
        → ∃ (X⁻ ∘ a⁻→x⁺)
      s (a⁺ , x⁺) (b⁻ , y⁻) = let a⁻ = a⁺ # a↝b ← b⁻
                              in a⁻ , (x⁺ a⁻ # x↝y ← y⁻)

    _ᵒ_ : Arena → ℕ → Arena
    _ ᵒ Nat.zero = Closed
    a ᵒ Nat.suc n = a ⊗ (a ᵒ n)

    
    _⟦ᵒ⟧_ : {a b : Arena} → a ↝ b → (n : ℕ) → (a ᵒ n) ↝ (b ᵒ n)
    _  ⟦ᵒ⟧ Nat.zero    = idLens Closed 
    lens ⟦ᵒ⟧ Nat.suc n = lens ⟦⊗⟧ (lens ⟦ᵒ⟧ n)

  --  EmitterPow : (a : Set) (n : ℕ) → (Emitter a ᵒ n) ↝ Emitter (Vect n a)
 --   EmitterPow a Nat.zero = (λ _ ()) ⇵ (λ sh _ → tt)
--    EmitterPow a (Nat.suc n) = {!!}
  open compose public
open ops public

module comonoid where
  record Comonoid : Set₁ where
    field
      domains : Arena
      ε : domains ↝ Closed
      δ : domains ↝ (domains ⊗ domains)

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
    _^δ_ (Nat.suc n) = δ ▸ (idLens (s ◄ s) ⟦⊗⟧ (_^δ_ n))

    module _ {a b x y : Arena} where
        duoidal : ((a ⊗ b) ⅋ (x ⊗ y)) ↝ ((a ⅋ x) ⊗ (b ⅋ y))
        duoidal ((a⁺ , bs) , x⁺ , ys) = ((a⁺ , x⁺) , (λ (a⁻ , y⁻) → bs a⁻ , ys y⁻))
                                      , λ ((a⁻ , x⁻) , b⁻ , y⁻) → (a⁻ , b⁻) , (x⁻ , y⁻)
open comonoid

module exp where
  _^_ : Arena → Arena → Arena
  a ^ b = product.prod (A⁺ , λ a⁺ → b ⊗ Exception (A⁻ a⁺)) where
    open Arena a renaming (ς to A⁺; ρ to A⁻)
    open Arena b renaming (ς to B⁺; ρ to B⁻)

    -- prod arena = λ ia⁺ → Σ[ a⁺ ∈ A⁺ ] × (B⁻ b⁺)
    --a ⊗ b = (Σ[ a⁺ ∈ A⁺ ](A⁻ a⁺ → B⁺)) ◅ λ (_ , bs) → ∃ (B⁻ ∘ bs) where

module internal-hom where
  _⊸_ : Arena → Arena → Arena
  a ⊸ b = product.prod (A⁺ , λ a⁺ → b ⊗ (A⁻ a⁺ ◄ ⊤)) where
--  a ⊸ b = ((a⁺ : A⁺) → Σ[ b⁺ ∈ B⁺ ](B⁻ b⁺ → A⁻ a⁺))
--        ◅ λ bs → Σ[ a⁺ ∈ A⁺ ](Σ (B⁻ (fst (bs a⁺)))(λ _ → ⊤))
    --  ≡ (a ↝ b) ◅ λ bs → Σ[ a⁺ ∈ A⁺ ](Σ (B⁻ (fst (bs a⁺)))(λ _ → ⊤))
    --  ≅ (a ↝ b) ◅ λ bs → (Σ A⁺ $ B⁻ ∘ fst ∘ bs)
    open Arena a renaming (ς to A⁺; ρ to A⁻)
    open Arena b renaming (ς to B⁺; ρ to B⁻)
  eval : ∀ {a b} → (a ⅋ (a ⊸ b)) ↝ b
  eval {a} {b} = g ⇵ s where
    open Arena a renaming (ς to A⁺; ρ to A⁻)
    open Arena b renaming (ς to B⁺; ρ to B⁻)
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
        body _XXX_  = body  dyn1 ⅋ body  dyn2
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
        run : state d → Stream (ς $ body d)
        hd (run s) = s ★ pheno d
        tl (run s) = run (s # pheno d ▸ e ← tt)
open dynamical

record Behavior (a : Arena) : Set where
    coinductive
    constructor _∷_
    field
      hd : ς a
      tl : ρ a hd → Behavior a
module behavior where
    module _ {a : Arena} (phys : a ↝ (⊤ ◄ ⊤)) where
      toStream : Behavior a → Stream (ς a)
      Stream.hd (toStream b) = Behavior.hd b
      Stream.tl (toStream b) = toStream (Behavior.tl b (Behavior.hd b # phys ← tt))
    module _ (d : DynSystem) where
      dynBehavior : state d → Behavior (body d)
      Behavior.hd (dynBehavior s) = s ★ pheno d
      Behavior.tl (dynBehavior s) d' = dynBehavior (s # pheno d ← d')
      run : (body d ↝ Closed) → state d → Stream (ς $ body d)
      run phys s = toStream phys (dynBehavior s)


module slice where -- prop 1.56 (slice definition seems wrong?)
  φ : ∀ {A B : Set} → (A → B) → (Set → A) → (Set → B)
  φ f a = f ∘ a

  Lens→Pshf : (a : Arena) → ς a → Set
  Lens→Pshf a _ = ς a

