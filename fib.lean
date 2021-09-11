import tactic.basic
import tactic.congr
import init.data.nat

/- Nat minus, where 0 - n = 0 -/
def ominus : ℕ → ℕ → ℕ
  | 0 m := 0
  | n 0 := n
  | (n + 1) (m + 1) := ominus n m

infix ` ⊖ `:60 := ominus

def fib_tail : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0 i j := (i , j)
  | (s + 1) i j := fib_tail s j (i + j)

--def fib : ℕ → ℕ
--  | n := let (a , b) := fib_tail n 1 0 in b

def fib : ℕ → ℕ × ℕ
  | 0 := (0, 0)
  | k := fib_tail k 1 0

#eval fib 8
#eval fib (0 ⊖ 1)
#eval fib 0

/- Demuestra por inducción matemática que los valores de $i$ y $j$ al final
de la $k$-ésima iteración de Fibiter son $f_{k−1}$ y $f_k$, respectivamente,
en donde $f_n$ denota el $n$-ésimo numero de Fibonacci. -/

theorem fib_iter_l : ∀ (n : ℕ), 
  (fib n).1 = (fib (n ⊖ 1)).2 := by
begin
  intro,
  induction n,
  refl,
  suggest,
end

/-
theorem fib_iter_k : ∀ (n : ℕ), 
  fib n = ((fib (n ⊖ 1)).2 , (fib (n)).2)
  | 0 := rfl
  | (n + 1) := -/
