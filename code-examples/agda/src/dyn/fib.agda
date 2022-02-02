{-# OPTIONS --type-in-type #-}
{-# OPTIONS --guardedness #-}
module dyn.fib where
open import prelude
open import functors
open import prelude.Stream using (take)
open import prelude.io
open import dyn


fib : Dyn
fib =  (plus   ⊠⊠⊠ delay ℕ) ⟫
    λ  (   f    ,     f₋  ) → f₋ , λ (.tt)
    → ((f₋ , f) ,     f   )
    where plus = fun→dyn (uncurry _ℕ+_)

main : IO ⊤
main = printStream (run fib auto (1 , 1))
