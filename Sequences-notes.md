## 序列收斂（Wade 2.1–2.2）學習筆記

這份筆記整理了在證明「\(1/n \to 0\)（Lean 中用 \(1/(n+1)\)）」時用到的 **語法、觀念與證明流程**，方便之後回顧。

---

### 1. ε–N 收斂定義在 Lean 中的表達

書上的定義：

\[
\{x_n\} \to a \iff \forall \varepsilon > 0,\ \exists N \in \mathbb N,\ \forall n \ge N,\ |x_n - a| < \varepsilon.
\]

在 `Sequences.lean` 中的 Lean 寫法：

```lean
def converge_to (x : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |x n - a| < ε
```

**對應關係：**

- 序列 \(\{x_n\}\)：`x : ℕ → ℝ`
- 第 \(n\) 項 `xₙ`：`x n`
- 極限 `a ∈ ℝ`：`a : ℝ`
- 「對每個 ε > 0」：`∀ ε > 0`
- 「存在 N ∈ ℕ」：`∃ N : ℕ`
- 「對所有 n ≥ N」：`∀ n : ℕ, n ≥ N →`
- 「\(|x_n - a| < ε\)」：`|x n - a| < ε`

---

### 2. 例題：\(1/n \to 0\)（Lean 寫成 \(1/(n+1)\)）

目標：

```lean
example : converge_to (fun n : ℕ => 1 / ((n : ℝ) + 1)) 0 := by
  ...
```

這裡選擇 `1 / ((n : ℝ) + 1)` 而不是 `1 / n` 的原因是：`ℕ` 從 `0` 開始，避免除以 `0` 的問題。

---

### 3. 常用語法與 tactic

- **`unfold`**

  ```lean
  unfold converge_to
  ```

  把 `converge_to` 這個定義「展開」成真正的公式（`∀ ε > 0, ∃ N, …`）。

- **引入假設與給出證明目標**

  ```lean
  intro ε hε     -- hε : ε > 0
  use (Nat.ceil (1 / ε) + 1 : ℕ)  -- 給出存在的 N
  intro n hn     -- hn : n ≥ N
  ```

- **`simp [sub_zero]`**

  ```lean
  simp [sub_zero]
  ```

  用來把 `|x - 0|` 簡化成 `|x|`。

- **`norm_cast` + `linarith`**

  把自然數的不等式轉成實數，再用線性不等式自動證明：

  ```lean
  have hpos : 0 < (n : ℝ) + 1 := by
    norm_cast
    linarith
  ```

- **`exact_mod_cast`**

  把 `hn : n ≥ ceil(1/ε) + 1` 轉成實數版本：

  ```lean
  have h2 : (n : ℝ) ≥ (Nat.ceil (1 / ε) : ℝ) + 1 := by
    exact_mod_cast hn
  ```

- **`Nat.le_ceil`（上取整的性質）**

  ```lean
  have h3 : (1 / ε : ℝ) ≤ Nat.ceil (1 / ε) := by
    exact_mod_cast (Nat.le_ceil (1 / ε))
  ```

- **`one_div_lt`（倒數不等式）**

  ```lean
  have hdiv : 1 / ((n : ℝ) + 1) < ε :=
    (one_div_lt hpos hε).mpr h1
  ```

  其中 `hpos : 0 < (n : ℝ) + 1`，`hε : 0 < ε`，
  `h1 : (n : ℝ) + 1 > 1 / ε`。
  `one_div_lt` 提供：

  \[
  (0 < a ∧ 0 < b) \Rightarrow (1/a < b \iff a > 1/b).
  \]

- **`abs_of_pos`**

  若知道 `x > 0`，可以把 `|x|` 換成 `x`：

  ```lean
  have hposAbs : |(n : ℝ) + 1| = (n : ℝ) + 1 := abs_of_pos hpos
  ```

- **`simpa [⋯] using h`**

  `simpa` = `simp` + `exact`，代表「先用 `simp` 簡化，再 `exact` 套用」：

  ```lean
  have hdiv' : 1 / |(n : ℝ) + 1| < ε := by
    have hposAbs : |(n : ℝ) + 1| = (n : ℝ) + 1 := abs_of_pos hpos
    simpa [hposAbs] using hdiv

  simpa [one_div] using hdiv'
  ```

---

### 4. 證明流程總結（用語言描述）

1. 定義收斂：`converge_to x a` 就是 ε–N 的條件。
2. 例題目標：證明 `x_n = 1/(n+1)` 收斂到 `0`。
3. 對任意 `ε > 0`，選 `N = ⌈1/ε⌉ + 1`。
4. 假設 `n ≥ N`，利用：
   - `n ≥ ceil(1/ε) + 1`
   - `ceil(1/ε) ≥ 1/ε`

   推出 `(n : ℝ) + 1 > 1/ε`。
5. 用 `one_div_lt` 把 `(n+1) > 1/ε` 變成 `1/(n+1) < ε`。
6. 因為 `(n : ℝ) + 1 > 0`，有 `|n+1| = n+1`，所以 `1/|n+1| = 1/(n+1)`，再改寫成 `|n+1|⁻¹`，與目標一致。

---

### 5. 建議複習方式

- 自己重新打一遍 `converge_to` 的定義。
- 關掉 InfoView，只看書上 2.1, 2.2，用自然語言先寫出證明，再對照這個 Lean 版本。
- 下次可以試著改寫成更短的版本（例如多用 `have` 合併步驟），練習把繁瑣計算壓縮成比較優雅的 proof script。

---

## 6. 常數序列與加法極限定理（為之後題目準備）

這一節整理 `Analysis/Sequences.lean` 中兩個重要的 lemma：

1. **常數序列收斂到自己**
2. **和的極限定理**：若 `xₙ → a` 且 `yₙ → b`，則 `(xₙ + yₙ) → (a + b)`

這些會在題目 `If xₙ → 2, prove that (2xₙ - 1) / xₙ → 5/2` 中用到。

### 6.1 常數序列收斂到自己

數學上很直觀：\((c, c, c, \dots)\) 對任意 ε，只要選任何 \(N\)（例如 0），後面的每一項都等於 \(c\)，所以 \(|c - c| = 0 < ε\)。

Lean 寫法：

```lean
theorem converge_to_const (c : ℝ) :
    converge_to (fun _ : ℕ => c) c := by
  intro ε hε
  -- 任何 N 都可以，選 N = 0 最簡單
  use 0
  intro n hn
  -- |c - c| = 0 < ε
  have : |(fun _ : ℕ => c) n - c| = 0 := by
    simp
  simp [this, hε]   -- 0 < ε
```

關鍵點：

- `fun _ : ℕ => c` 表示「不看 n 的常數序列」。
- 用一個 `have` 把 `|c - c| = 0` 算出來，再用 `simp` 以及 `hε : ε > 0` 得到 `0 < ε`。

### 6.2 加法極限定理：`xₙ → a`, `yₙ → b` ⇒ `(xₙ + yₙ) → (a + b)`

數學上是經典的 ε–N 證明：

1. 給定 ε > 0，分成兩半 ε/2。
2. 由 `xₙ → a` 得到：存在 `Nx`，使得對所有 `n ≥ Nx`，有 \(|xₙ - a| < ε/2\)。
3. 由 `yₙ → b` 得到：存在 `Ny`，使得對所有 `n ≥ Ny`，有 \(|yₙ - b| < ε/2\)。
4. 取 `N = max Nx Ny`，這樣 `n ≥ N` 時同時滿足兩個條件。
5. 三角不等式：
   \[
   |(x_n + y_n) - (a + b)| = |(x_n - a) + (y_n - b)|
   \le |x_n - a| + |y_n - b| < ε/2 + ε/2 = ε.
   \]

Lean 實作：

```lean
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
    have : (x n + y n) - (a + b) = (x n - a) + (y n - b) := by
      ring
    -- 使用三角不等式 abs_add_le
    have h := abs_add_le (x n - a) (y n - b)
    -- 把左邊改成需要的樣子
    simpa [this] using h
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
```

之後在做 `(2 xₙ - 1) / xₙ → 5/2` 這一題時，這兩個 lemma 就會派上用場：

- `converge_to_const` 給你「常數 2」的極限。
- `converge_to_add` 和類似的「乘常數」lemma 可以用來組合成更複雜的表達式的極限。



