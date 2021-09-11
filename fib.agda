import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat


record Pair (A B : Set) : Set where
  constructor _×_
  field
    fst : A
    snd : B


_-_ : ℕ → ℕ → ℕ
0 - m = 0
n - 0 = n
(suc n) - (suc m) = n - m

fib-tail : ℕ → ℕ → ℕ → Pair ℕ ℕ
fib-tail 0 i j = i × j
fib-tail (suc s) i j = fib-tail s j (i + j)

fib : ℕ → Pair ℕ ℕ
fib 0 = 0 × 0
fib k = fib-tail k 1 0


-- Pair.fst (fib n)
theorem-fib-iter : (n : ℕ) → Pair.fst (fib n) ≡ Pair.snd (fib (n - 1))
theorem-fib-iter zero = refl
theorem-fib-iter (suc zero) = refl
theorem-fib-iter (suc (suc n)) =
    begin
        Pair.fst (fib (suc (suc n))) -- Pair.snd (fib (suc n))
    ≡⟨⟩
        Pair.fst (fib (suc n)) + Pair.fst (fib n)
    ≡⟨ cong ((_+_) _ Pair.fst (fib n)) (theorem-fib-iter (suc n))⟩
        Pair.snd (fib ((suc n) - 1)) + Pair.fst (fib n)
    ≡⟨⟩
        Pair.snd (fib n) + Pair.fst (fib n)
    ≡⟨⟩
        Pair.snd (fib (suc n))
    ∎

-- Pair.snd (fib n)

-- def fib : ℕ → ℕ × ℕ
--   | 0 := (0, 0)
--   | k := fib_tail k 1 0
