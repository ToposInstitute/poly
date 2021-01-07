module prelude.int where
open import Data.Nat as Nat renaming (suc to s; zero to z)
open import Agda.Builtin.Int public

⁺1 : Int → Int
⁺1 (pos n) = pos (s n)
⁺1 (negsuc z) = pos z
⁺1 (negsuc (s n)) = negsuc n

⁻1 : Int → Int
⁻1 (pos Nat.zero) = negsuc Nat.zero
⁻1 (pos (Nat.suc n)) = pos n
⁻1 (negsuc n) = negsuc (Nat.suc n)
