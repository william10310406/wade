/-
# 序列 (Sequences)

基于 Wade 第二章：R 中的序列
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Topology.Basic
import Mathlib.Topology.Order.Real
import Mathlib.Tactic

open Filter
open scoped Topology

namespace WadeAnalysis

-- 2 Sequences in ℝ
-- 2.1 Definition : A sequence of real numbers {xₙ} is said to converge to a real number a ∈ ℝ
-- if and only if for every ε > 0 there is an N ∈ ℕ (which in general depends on ε) such that
-- n ≥ N implies |xₙ - a| < ε.
-- 下面的 `converge_to` 就是這個 ε–N 定義在 Lean 裡的直接翻譯。
def converge_to (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |x n - a| < ε
-- {xₙ} : x : ℕ → ℝ
-- xₙ : x n
-- a ∈ ℝ : a : ℝ
-- ∀ ε > 0 : ∀ ε > 0
-- ∃ N ∈ ℕ : ∃ N : ℕ
-- ∀ n : ℕ, n ≥ N → |x n - a| < ε : ∀ n : ℕ, n ≥ N → |x n - a| < ε

-- 2.2 Example
-- (i) Prove that 1/n → 0 as n → ∞.
-- 下面用剛剛定義的 `converge_to`，證明序列 xₙ = 1/(n+1) 收斂到 0。
example : converge_to (fun n : ℕ => 1 / ((n : ℝ) + 1)) 0 := by
  -- 把 `converge_to` 的定義展開成 ε–N 的形式
  unfold converge_to
  -- 給定任意 ε > 0
  intro ε hε
  -- 選擇 N = ⌈1/ε⌉ + 1
  use (Nat.ceil (1 / ε) + 1 : ℕ)
  -- 現在要證明：當 n ≥ N 時，有 |1/(n+1) - 0| < ε
  intro n hn
  -- 先把「減 0」化簡掉
  simp [sub_zero]
  -- 之後都在實數上工作，先取得 (n : ℝ) + 1 > 0，方便後面處理倒數與絕對值
  have hpos : 0 < (n : ℝ) + 1 := by
    norm_cast
    linarith
  -- Step 1：由 n ≥ ⌈1/ε⌉ + 1 推出 (n : ℝ) + 1 > 1 / ε
  have h1 : (n : ℝ) + 1 > 1 / ε := by
    -- 把 `hn : n ≥ ceil(1/ε)+1` 轉成實數上的不等式
    have h2 : (n : ℝ) ≥ (Nat.ceil (1 / ε) : ℝ) + 1 := by
      exact_mod_cast hn
    -- ceil 的性質：ceil(1/ε) ≥ 1/ε
    have h3 : (1 / ε : ℝ) ≤ Nat.ceil (1 / ε) := by
      exact_mod_cast (Nat.le_ceil (1 / ε))
    -- 利用 h2, h3 得到 (n : ℝ) ≥ 1/ε + 1
    have h4 : (n : ℝ) ≥ 1 / ε + 1 := by
      linarith
    -- 進一步得到 (n : ℝ) + 1 ≥ 1/ε + 1
    have : (n : ℝ) + 1 ≥ 1 / ε + 1 := by
      linarith
    -- 於是 (n : ℝ) + 1 > 1/ε
    have : (n : ℝ) + 1 > 1 / ε := by
      linarith
    exact this
  -- Step 2：用 `one_div_lt` 把 (n+1) > 1/ε 轉成 1/(n+1) < ε
  have hdiv : 1 / ((n : ℝ) + 1) < ε :=
    (one_div_lt hpos hε).mpr h1
  -- Step 3：把分母改成 |n+1|，也就是證明 1/|n+1| < ε
  have hdiv' : 1 / |(n : ℝ) + 1| < ε := by
    have hposAbs : |(n : ℝ) + 1| = (n : ℝ) + 1 := abs_of_pos hpos
    simpa [hposAbs] using hdiv
  -- Step 4：把 1/|n+1| 改寫成 |n+1|⁻¹，與目標完全一致
  -- 目標是 |↑n + 1|⁻¹ < ε，這與 1 / |n+1| < ε 等價
  simpa [one_div] using hdiv'

-- 常數序列 c 收斂到 c
theorem converge_to_const (c : ℝ) :
    converge_to (fun _ : ℕ => c) c := by
  intro ε hε
  -- 任何 N 都可以，選 N = 0 最簡單
  use 0
  intro n hn
  -- |c - c| = 0 < ε
  have : |(fun _ : ℕ => c) n - c| = 0 := by
    simp
  simp [hε]   -- 0 < ε

-- 如果 xₙ → a，yₙ → b，則 (xₙ + yₙ) → (a + b)
theorem converge_to_add
    {x y : ℕ → ℝ} {a b : ℝ}
    (hx : converge_to x a) (hy : converge_to y b) :
    converge_to (fun n => x n + y n) (a + b) := by
  intro ε hε
  -- 對 ε/2 分別套在 x, y 的收斂定義上
  have hε2 : ε / 2 > 0 := by
    -- 只要 ε > 0 且 2 > 0，就有 ε/2 > 0
    have h2 : (0 : ℝ) < 2 := by norm_num
    exact div_pos hε h2
  -- 對 xₙ 的條件：存在 Nx，使得 n ≥ Nx ⇒ |xₙ - a| < ε/2
  obtain ⟨Nx, hNx⟩ := hx (ε / 2) hε2
  -- 對 yₙ 的條件：存在 Ny，使得 n ≥ Ny ⇒ |yₙ - b| < ε/2
  obtain ⟨Ny, hNy⟩ := hy (ε / 2) hε2
  -- 取 N = max Nx Ny
  refine ⟨max Nx Ny, ?_⟩
  intro n hn
  -- 後面會用到 n ≥ Nx, n ≥ Ny
  have hnx : n ≥ Nx := le_trans (le_max_left _ _) hn
  have hny : n ≥ Ny := le_trans (le_max_right _ _) hn
  -- 用三角不等式：| (xₙ + yₙ) - (a + b) | ≤ |xₙ - a| + |yₙ - b|
  have htriangle :
      |(x n + y n) - (a + b)| ≤ |x n - a| + |y n - b| := by
    -- 把 (xₙ + yₙ) - (a + b) 改寫成 (xₙ - a) + (yₙ - b)
    have : (x n + y n) - (a + b) = (x n - a) + (y n - b) := by ring
    simpa [this] using abs_add_le (x n - a) (y n - b)
  -- 由收斂性給出兩個 ε/2 的估計
  have hxε : |x n - a| < ε / 2 := hNx n hnx
  have hyε : |y n - b| < ε / 2 := hNy n hny
  -- 把這兩個估計加起來
  have hsum : |x n - a| + |y n - b| < ε := by
    have : |x n - a| + |y n - b| < ε / 2 + ε / 2 := by
      exact add_lt_add hxε hyε
    -- ε/2 + ε/2 = ε
    simpa [add_halves] using this
  -- 最後用夾擠：| (xₙ + yₙ) - (a + b) | ≤ ... < ε
  exact lt_of_le_of_lt htriangle hsum

-- 2.4 Remark. A sequence can have at most one limit.
theorem converge_to_unique {x : ℕ → ℝ} {a b : ℝ}
    (hx : converge_to x a) (hy : converge_to x b) :
    a = b := by
  classical -- 使用經典邏輯
  by_contra hne -- hne : ¬ a = b
  have hdist_pos : |a - b| > 0 := by
    have : a - b ≠ 0 := sub_ne_zero.mpr hne
    exact abs_pos.mpr this
  let ε : ℝ := |a - b| / 2
  have hε_pos : ε > 0 := by
    have h2 : (0 : ℝ) < 2 := by norm_num
    simpa [ε] using div_pos hdist_pos h2
  rcases hx ε hε_pos with ⟨Na, hNa⟩
  rcases hy ε hε_pos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have hN_ge_Na : N ≥ Na := le_max_left _ _
  have hN_ge_Nb : N ≥ Nb := le_max_right _ _
  have hxa : |x N - a| < ε := hNa N hN_ge_Na
  have hxb : |x N - b| < ε := hNb N hN_ge_Nb

  -- 用三角不等式：|a - b| ≤ |a - x N| + |x N - b|
  have htriangle :
      |a - b| ≤ |a - x N| + |x N - b| := by
    -- `abs_sub_le a (x N) b` 給出 |a - b| ≤ |a - xN| + |xN - b|
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      abs_sub_le a (x N) b

  -- 再證明右邊這個和其實 < |a - b|
  have hsum_lt : |a - x N| + |x N - b| < |a - b| := by
    -- 先把 |a - xN| 改寫成 |xN - a|，方便用 hxa
    have h1 : |a - x N| = |x N - a| := by
      simpa [abs_sub_comm]
    have hxa' : |a - x N| < ε := by
      simpa [h1] using hxa
    -- 利用 |a - xN| < ε、|xN - b| < ε 得到和 < ε + ε
    have hlt : |a - x N| + |x N - b| < ε + ε := by
      exact add_lt_add hxa' hxb
    -- 因為 ε = |a - b| / 2，所以 ε + ε = |a - b|
    simpa [ε, add_halves] using hlt

  -- 綜合：|a - b| ≤ ... < |a - b|，矛盾
  have : |a - b| < |a - b| :=
    lt_of_le_of_lt htriangle hsum_lt
  exact (lt_irrefl _ this)
end WadeAnalysis
