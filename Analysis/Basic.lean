/-
# 分析學基礎 (An Introduction to Analysis)

基於 Wade 的《An Introduction to Analysis》第 4 版

這個檔案包含第一章：實數系統的基礎內容
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace WadeAnalysis

/-
## 第一章：实数系统 (Chapter 1: The Real Number System)

### Lean 基本語法說明

1. **類型註解語法**：`(值 : 類型)`
   - 例如：`(1 : ℝ)` 表示將數字 1 標註為實數類型

2. **檢查命令語法**：`#check <表達式>`
   - 用於檢查表達式的類型，不會執行程式碼

3. **定理聲明語法**：
   - `example (參數列表) : 命題 := 證明` - 匿名定理
   - `theorem 名稱 (參數列表) : 命題 := 證明` - 命名定理
   - `lemma 名稱 (參數列表) : 命題 := 證明` - 引理（與 theorem 相同）

4. **參數列表語法**：`(變數1 : 類型1) (變數2 : 類型2) ...`
   - 可以簡寫為 `(a b c : ℝ)` 表示 a, b, c 都是實數類型

5. **邏輯連接符**：
   - `→` 或 `→` - 蘊含（implies）
   - `↔` - 雙向蘊含（若且唯若，iff）
   - `∧` - 邏輯與（and）
   - `∨` - 邏輯或（or）
   - `¬` - 邏輯非（not）

6. **關係符號**：
   - `=` - 等於
   - `≤` - 小於等於
   - `≥` - 大於等於
   - `<` - 小於
   - `>` - 大於

7. **證明語法**：`:= 證明項`
   - 可以直接使用已有的定理，如 `add_comm a b`
   - 也可以使用策略（tactics）進行證明

### 1.1 引言 (Introduction)

在 Lean 中，實數系統已經透過 Mathlib 定義好了。
我們可以直接使用 `ℝ` (Real) 類型。
-/

-- 實數的基本類型
-- 語法：`#check <表達式>` - 檢查表達式的類型
-- 這會顯示表達式的類型資訊，用於驗證類型是否正確
#check ℝ
-- `ℝ` 是實數的類型，類型本身也是類型，所以會顯示 `Type`

-- 語法：`(值 : 類型)` - 類型註解（type annotation）
-- 這裡將數字 1 標註為實數類型
#check (1 : ℝ)
-- 這會顯示 `1 : ℝ`，表示 1 是實數類型

-- π 需要匯入三角函數模組，這裡先註解掉
-- #check (π : ℝ)

/-
### 1.2 有序域公理 (Ordered Field Axioms)

實數滿足有序域的所有公理。在 Lean 中，這些都已經內建了。

#### 公設語法說明

在 Lean 中，公設（axioms）通常以定理（theorem）或類型類（type class）的形式存在。
下面列出各個公設的語法結構：

1. **加法公理**
   - 交換律：`∀ a b : ℝ, a + b = b + a`
   - 結合律：`∀ a b c : ℝ, (a + b) + c = a + (b + c)`
   - 單位元（零元）：`∀ a : ℝ, a + 0 = a` 和 `∀ a : ℝ, 0 + a = a`
   - 逆元（負元）：`∀ a : ℝ, a + (-a) = 0` 和 `∀ a : ℝ, (-a) + a = 0`

2. **乘法公理**
   - 交換律：`∀ a b : ℝ, a * b = b * a`
   - 結合律：`∀ a b c : ℝ, (a * b) * c = a * (b * c)`
   - 單位元（單位元）：`∀ a : ℝ, a * 1 = a` 和 `∀ a : ℝ, 1 * a = a`
   - 逆元（倒數，對非零元）：`∀ a : ℝ, a ≠ 0 → a * a⁻¹ = 1`

3. **分配律**
   - 左分配律：`∀ a b c : ℝ, a * (b + c) = a * b + a * c`
   - 右分配律：`∀ a b c : ℝ, (a + b) * c = a * c + b * c`

4. **序公理**
   - 全序性：`∀ a b : ℝ, a ≤ b ∨ b ≤ a`
   - 傳遞性：`∀ a b c : ℝ, a ≤ b → b ≤ c → a ≤ c`
   - 反身性：`∀ a : ℝ, a ≤ a`
   - 加法保序：`∀ a b c : ℝ, a ≤ b → a + c ≤ b + c`
   - 乘法保序（正數）：`∀ a b c : ℝ, 0 ≤ c → a ≤ b → a * c ≤ b * c`

5. **完備性公理**
   - 上確界存在性：有上界的非空集合必有上確界
   - 語法：`∀ s : Set ℝ, s.Nonempty → BddAbove s → ∃ x : ℝ, IsLUB s x`
-/

-- ============================================
-- 1. 加法公理 (Addition Axioms)
-- ============================================

-- 公設 1.1：加法交換律 (Additive Commutativity)
-- 語法：`∀ (變數 : 類型), 命題` - 全稱量詞（for all）
-- `∀ a b : ℝ` 是 `∀ a : ℝ, ∀ b : ℝ` 的簡寫
-- 命題：`a + b = b + a` 表示加法滿足交換律
-- 在 Lean 中透過 `add_comm` 定理實作

-- 公設 1.2：加法結合律 (Additive Associativity)
-- 語法：`(a + b) + c = a + (b + c)` - 括號表示運算順序
-- 命題表示：無論先加哪兩個，結果都相同
-- 完整語法：`example (a b c : ℝ) : (a + b) + c = a + (b + c) := add_assoc a b c`
-- `(a b c : ℝ)` - 聲明三個實數變數
-- `(a + b) + c = a + (b + c)` - 要證明的等式
-- `add_assoc` - 加法結合律定理，參數順序對應：`add_assoc a b c`

-- 公設 1.3：加法單位元（零元）(Additive Identity)
-- 語法：`0 : ℝ` 表示實數零
-- 命題：`a + 0 = a` 表示零是加法的單位元
-- `add_zero` 定理：`a + 0 = a`

-- 公設 1.4：加法逆元（負元）(Additive Inverse)
-- 語法：`-a` 表示 a 的加法逆元（負數）
-- 命題：`a + (-a) = 0` 表示每個數都有加法逆元
-- `add_neg_cancel` 定理：`a + (-a) = 0`

-- ============================================
-- 2. 乘法公理 (Multiplication Axioms)
-- ============================================

-- 公設 2.1：乘法交換律 (Multiplicative Commutativity)
-- 語法：`a * b = b * a` - 乘法滿足交換律

-- 公設 2.2：乘法結合律 (Multiplicative Associativity)
-- 語法：`(a * b) * c = a * (b * c)` - 乘法滿足結合律

-- 公設 2.3：乘法單位元（單位元）(Multiplicative Identity)
-- 語法：`1 : ℝ` 表示實數一
-- 命題：`a * 1 = a` 表示一是乘法的單位元
-- `mul_one` 定理：`a * 1 = a`

-- 公設 2.4：乘法逆元（倒數，對非零元）(Multiplicative Inverse)
-- 語法：`a⁻¹` 或 `1 / a` 表示 a 的乘法逆元（倒數）
-- 語法：`a ≠ 0` 表示 a 不等於零
-- 語法：`→` 表示蘊含（implies），這裡表示"如果 a ≠ 0，則..."
-- 命題：`a ≠ 0 → a * a⁻¹ = 1` 表示非零數都有乘法逆元
-- 在 Lean 中，實數 ℝ 是域（Field），可以直接使用類型類實例的 `mul_inv_cancel`
-- 語法：透過類型類解析，Lean 會自動找到 Field 實例並應用 `mul_inv_cancel`
-- 注意：`a / a = 1` 等價於 `a * a⁻¹ = 1`，因為 `a / a = a * a⁻¹`

-- ============================================
-- 3. 分配律 (Distributivity)
-- ============================================

-- 公設 3：分配律 (Distributivity)
-- 左分配律：`a * (b + c) = a * b + a * c`
-- `mul_add` 定理實作左分配律

-- 右分配律：`(a + b) * c = a * c + b * c`
-- `add_mul` 定理實作右分配律

-- 定理：對於任意實數 a，有 0 · a = 0
-- 這個定理說明：零乘以任何數都等於零
-- 證明思路：使用分配律、加法結合律、加法逆元等基本公理
example (a : ℝ) : 0 * a = 0 := by
   -- 步驟 1：使用加法單位元公理（公設 1.3）
   -- `add_zero` 定理：`a + 0 = a`
   -- 這裡將 `0 * a` 寫成 `0 * a + 0` 的形式
   have h0a_add_0 : 0 * a = 0 * a + 0 := by
      rw [add_zero]

   -- 步驟 2：使用加法逆元公理（公設 1.4）
   -- `add_neg_cancel` 定理：`a + (-a) = 0`
   -- 取其對稱形式：`0 = a + (-a)`
   -- 這裡 `a` 是 `0 * a`，所以 `0 = 0 * a + (- (0 * a))`
   have h0_eq_0a_add_0a : 0 = 0 * a + (- (0 * a)) :=
      (add_neg_cancel (0 * a)).symm

   -- 步驟 3：將步驟 1 中的 `0` 替換成步驟 2 中的表達式
   -- 從 `0 * a = 0 * a + 0` 得到 `0 * a = 0 * a + (0 * a + (- (0 * a)))`
   -- 使用 `convert` 和 `rw [← h0_eq_0a_add_0a]` 來替換
   have h3 : 0 * a = 0 * a + (0 * a + (- (0 * a))) := by
      -- 從 h0a_add_0: 0 * a = 0 * a + 0
      -- 把右邊的 0 替換成 0 * a + (- (0 * a))（用 h0_eq_0a_add_0a 的反向）
      convert h0a_add_0 using 2
      rw [← h0_eq_0a_add_0a]

   -- 步驟 4：使用加法結合律（公設 1.2）
   -- `add_assoc` 定理：`(a + b) + c = a + (b + c)`
   -- 取其對稱形式：`a + (b + c) = (a + b) + c`
   -- 這裡將 `0 * a + (0 * a + (- (0 * a)))` 重組為 `(0 * a + 0 * a) + (- (0 * a))`
   have h4 : 0 * a + (0 * a + - (0 * a)) = (0 * a + 0 * a) + (- (0 * a)) :=
      (add_assoc (0 * a) (0 * a) (- (0 * a))).symm

   -- 步驟 5：使用分配律（公設 3）和加法單位元
   -- 首先用右分配律將 `0 * a + 0 * a` 寫成 `(0 + 0) * a`
   -- 然後用 `add_zero` 將 `(0 + 0) * a` 簡化為 `0 * a`
   -- 最終得到 `(0 * a + 0 * a) + (- (0 * a)) = 0 * a + (-(0 * a))`
   have h5 : (0 * a + 0 * a) + (- (0 * a)) = 0 * a + (-(0 * a)) := by
      -- 子步驟 5.1：使用右分配律 `add_mul` 的逆方向
      -- `add_mul` 定理：`(a + b) * c = a * c + b * c`
      -- 逆方向：`a * c + b * c = (a + b) * c`
      -- 這裡 `a = 0`, `b = 0`, `c = a`，所以 `0 * a + 0 * a = (0 + 0) * a`
      have h6 : 0 * a + 0 * a = (0 + 0) * a := by
         rw [← add_mul]
      -- 子步驟 5.2：使用加法單位元 `add_zero`
      -- `add_zero` 定理：`a + 0 = a`
      -- 這裡 `0 + 0 = 0`，所以 `(0 + 0) * a = 0 * a`
      rw [h6]
      rw [add_zero]

   -- 步驟 6：使用加法逆元公理（公設 1.4）
   -- `add_neg_cancel` 定理：`a + (-a) = 0`
   -- 這裡 `a` 是 `0 * a`，所以 `0 * a + (-(0 * a)) = 0`
   have h7 : 0 * a + (-(0 * a)) = 0 := add_neg_cancel (0 * a)

   -- 最終步驟：使用 `calc` 將以上所有步驟串聯起來
   -- 這是一個等式鏈式證明，每一步都使用前面建立的引理
   calc
      0 * a = 0 * a + (0 * a + - (0 * a)) := h3
      _ = (0 * a + 0 * a) + (- (0 * a)) := h4
      _ = 0 * a + (-(0 * a)) := h5
      _ = 0 := h7

-- 定理：對於任意實數 a，有 -a = (-1) · a
-- 這個定理說明：一個數的負數等於 -1 乘以這個數
-- 證明思路：先證明 a + (-1) * a = 0，然後使用加法逆元的性質
example (a : ℝ) : -a = (-1) * a := by
   -- 步驟 1：證明 a + (-1) * a = 0
   -- 這是證明的關鍵中間步驟，我們將使用分配律和加法逆元
   have h1 : a + (-1) * a = 0 := by
      calc
         a + (-1) * a
         -- 子步驟 1.1：使用乘法單位元（公設 2.3）
         -- `one_mul` 定理：`1 * a = a`
         -- 將 `a` 寫成 `1 * a` 的形式，以便後續使用分配律
         _ = 1 * a + (-1) * a := by rw [one_mul a]
         -- 子步驟 1.2：使用右分配律（公設 3.2）的逆方向
         -- `add_mul` 定理：`(a + b) * c = a * c + b * c`
         -- 逆方向：`a * c + b * c = (a + b) * c`
         -- 這裡 `a = 1`, `b = -1`, `c = a`，所以 `1 * a + (-1) * a = (1 + (-1)) * a`
         _ = (1 + (-1)) * a := by rw [← add_mul]
         -- 子步驟 1.3：使用加法逆元（公設 1.4）
         -- `add_neg_cancel` 定理：`a + (-a) = 0`
         -- 這裡 `a = 1`，所以 `1 + (-1) = 0`
         _ = 0 * a := by rw [add_neg_cancel (1 : ℝ)]
         -- 子步驟 1.4：使用零乘任何數等於零（前面已證明的定理）
         -- `zero_mul` 定理：`0 * a = 0`
         _ = 0 := by rw [zero_mul]

   -- 步驟 2：從 a + (-1) * a = 0 推導出 -a = (-1) * a
   -- 使用 `eq_neg_of_add_eq_zero_right` 定理
   -- 這個定理說：如果 `a + b = 0`，則 `b = -a`
   -- 這裡 `a = a`, `b = (-1) * a`，所以 `(-1) * a = -a`
   -- 然後使用 `eq_comm` 交換等式的兩邊，得到 `-a = (-1) * a`
   rw [eq_comm]
   exact eq_neg_of_add_eq_zero_right h1

-- 定理：對於任意實數 a，有 -(-a) = a
-- 這個定理說明：一個數的負數的負數等於原數
-- 證明思路：使用加法逆元公設、加法交換律和加法消去律
example (a : ℝ) : -(-a) = a := by
   -- 步驟 1：使用加法逆元公理（公設 1.4）
   -- `add_neg_cancel` 定理：`a + (-a) = 0`
   -- 對 `a` 應用：`a + (-a) = 0`
   have h1 : a + (-a) = 0 := add_neg_cancel a
   -- 對 `-a` 應用：`(-a) + (-(-a)) = 0`
   -- 這表示 `-a` 的加法逆元是 `-(-a)`
   have h2 : (-a) + (-(-a)) = 0 := add_neg_cancel (-a)

   -- 步驟 2：使用加法交換律（公設 1.1）
   -- `add_comm` 定理：`a + b = b + a`
   -- 將 h1 轉換為 `(-a) + a = 0` 的形式
   -- 這樣我們就有兩個以 `-a` 開頭的等式，方便後續使用消去律
   have h3 : (-a) + a = 0 := by rw [add_comm, h1]

   -- 步驟 3：使用加法消去律
   -- 如果 `x + y = 0` 且 `x + z = 0`，則 `y = z`
   -- 這裡 `x = -a`, `y = a`, `z = -(-a)`
   -- 從 `(-a) + a = 0` 和 `(-a) + (-(-a)) = 0` 得到 `a = -(-a)`
   -- 然後使用 `eq_comm` 交換等式的兩邊，得到 `-(-a) = a`
   have h5 : a = -(-a) := by
      -- 子步驟 3.1：建立等式 `(-a) + a = (-a) + (-(-a))`
      -- 我們有 `(-a) + a = 0`（h3）和 `(-a) + (-(-a)) = 0`（h2）
      -- 因為兩邊都等於 0，所以 `(-a) + a = (-a) + (-(-a))`
      have h6 : (-a) + a = (-a) + (-(-a)) := by
         rw [h3, h2]
      -- 子步驟 3.2：使用左消去律 `add_left_cancel`
      -- `add_left_cancel` 定理：如果 `a + b = a + c`，則 `b = c`
      -- 這裡 `a = -a`, `b = a`, `c = -(-a)`
      -- 從 `(-a) + a = (-a) + (-(-a))` 得到 `a = -(-a)`
      exact add_left_cancel h6

   -- 步驟 4：交換等式的兩邊
   -- 使用 `eq_comm` 從 `a = -(-a)` 得到 `-(-a) = a`
   rw [eq_comm]
   exact h5

-- 定理：對於任意實數 a, b，有 -(a - b) = b - a
-- 這個定理說明：一個減法的負數等於交換被減數和減數後的減法
-- 證明思路：使用減法轉加法、負數與乘法的關係、分配律、以及前面證明的定理
example (a b : ℝ) : -(a - b) = b - a := by
   calc
      -(a - b)
      -- 步驟 1：將減法轉換為加法形式
      -- `sub_eq_add_neg` 定理：`a - b = a + (-b)`
      -- 所以 `-(a - b) = -(a + (-b))`
      _ = -(a + (-b)) := by rw [sub_eq_add_neg]

      -- 步驟 2：使用負數與乘法的關係（練習題 2 的結果）
      -- `neg_one_mul` 定理：`-a = (-1) * a`
      -- 逆方向：`-x = (-1) * x`
      -- 這裡 `x = a + (-b)`，所以 `-(a + (-b)) = (-1) * (a + (-b))`
      _ = (-1) * (a + (-b)) := by rw [← neg_one_mul]

      -- 步驟 3：使用左分配律（公設 3.1）
      -- `mul_add` 定理：`a * (b + c) = a * b + a * c`
      -- 這裡 `a = -1`, `b = a`, `c = -b`
      -- 所以 `(-1) * (a + (-b)) = (-1) * a + (-1) * (-b)`
      _ = (-1) * a + (-1) * (-b) := by rw [mul_add]

      -- 步驟 4：使用負數與乘法的關係
      -- `neg_one_mul` 定理：`(-1) * a = -a`
      -- 所以 `(-1) * a + (-1) * (-b) = (-a) + (-1) * (-b)`
      _ = (-a) + (-1) * (-b) := by rw [neg_one_mul]

      -- 步驟 5：使用負數的負數等於原數（練習題 3 的結果）
      -- `neg_one_mul` 定理：`(-1) * (-b) = -(-b)`
      -- `neg_neg` 定理：`-(-b) = b`
      -- 所以 `(-a) + (-1) * (-b) = (-a) + b`
      _ = (-a) + b := by rw [neg_one_mul, neg_neg]

      -- 步驟 6：使用加法交換律（公設 1.1）
      -- `add_comm` 定理：`a + b = b + a`
      -- 所以 `(-a) + b = b + (-a)`
      _ = b + (-a) := by rw [add_comm]

      -- 步驟 7：轉換回減法形式
      -- `sub_eq_add_neg` 定理的逆方向：`a + (-b) = a - b`
      -- 所以 `b + (-a) = b - a`
      _ = b - a := by rw [← sub_eq_add_neg]

-- 定理：對於任意實數 a, b，如果 a * b = 0，則 a = 0 或 b = 0
-- 這個定理說明：如果兩個數的乘積為零，則至少有一個為零
-- 證明思路：使用反證法，假設 a ≠ 0 且 b ≠ 0，然後推導出矛盾
example (a b : ℝ) : a * b = 0 → a = 0 ∨ b = 0 := by
   -- 步驟 1：引入前提
   -- 假設 a * b = 0
   intro h

   -- 步驟 2：使用反證法
   -- 假設結論不成立：a ≠ 0 且 b ≠ 0
   by_contra h_not
   -- h_not 是 ¬(a = 0 ∨ b = 0)，即 a ≠ 0 且 b ≠ 0

   -- 步驟 3：使用德摩根定律展開否定
   -- `push_neg` 將 ¬(a = 0 ∨ b = 0) 轉換為 a ≠ 0 ∧ b ≠ 0
   push_neg at h_not

   -- 步驟 4：分解假設
   -- 從 h_not : a ≠ 0 ∧ b ≠ 0 得到兩個假設
   have ha_neq_0 : a ≠ 0 := h_not.left
   have hb_neq_0 : b ≠ 0 := h_not.right

   -- 步驟 5：從 a * b = 0 和 a ≠ 0 推導出 b = 0
   -- 這是反證法的關鍵步驟
   have hb_eq_0 : b = 0 := by
      calc
         b
         -- 子步驟 5.1：使用乘法單位元（公設 2.3）
         -- `one_mul` 定理：`1 * b = b`
         _ = 1 * b := by rw [one_mul]
         -- 子步驟 5.2：使用乘法逆元（公設 2.4）
         -- 因為 a ≠ 0，所以 a 有乘法逆元 a⁻¹
         -- `mul_inv_cancel` 定理：`a * a⁻¹ = 1`
         -- 使用 `field_simp` 自動處理類型推斷，將 1 替換為 a * a⁻¹
         _ = (a * a⁻¹) * b := by
            field_simp [ha_neq_0]
         -- 子步驟 5.3：使用乘法交換律和結合律（公設 2.1, 2.2）
         -- `mul_comm` 定理：`a * a⁻¹ = a⁻¹ * a`
         -- `mul_assoc` 定理：`(a⁻¹ * a) * b = a⁻¹ * (a * b)`
         _ = a⁻¹ * (a * b) := by rw [mul_comm a a⁻¹, mul_assoc]
         -- 子步驟 5.4：使用前提 h : a * b = 0
         -- 將 a * b 替換為 0
         _ = a⁻¹ * 0 := by rw [h]
         -- 子步驟 5.5：使用零乘任何數等於零（練習題 1 的結果）
         -- `mul_zero` 定理：`a * 0 = 0`
         _ = 0 := by rw [mul_zero]

   -- 步驟 6：得出矛盾
   -- 我們有 hb_neq_0 : b ≠ 0 和 hb_eq_0 : b = 0
   -- 這兩個命題矛盾，因此原假設不成立
   -- 所以 a = 0 ∨ b = 0 成立
   exact hb_neq_0 hb_eq_0

-- ============================================
-- 4. 序公理 (Order Axioms)
-- ============================================

-- 公設 4.1：全序性 (Total Order)
-- 語法：`≤` 表示小於等於關係
-- 語法：`∨` 表示邏輯或（or）
-- 命題：`a ≤ b ∨ b ≤ a` 表示任意兩個實數都可以比較大小
-- `le_total` 定理保證實數集是全序的

-- 公設 4.2：傳遞性 (Transitivity)
-- 語法：`→` 表示蘊含，可以鏈式使用
-- 命題：`a ≤ b → b ≤ c → a ≤ c` 表示如果 a ≤ b 且 b ≤ c，則 a ≤ c
-- `le_trans` 定理實作傳遞性

-- 公設 4.3：反身性 (Reflexivity)
-- 命題：`a ≤ a` 表示每個數都小於等於自己
-- `le_refl` 定理實作反身性

-- 公設 4.4：加法保序 (Order Preservation under Addition)
-- 語法：`a ≤ b → a + c ≤ b + c` 表示如果 a ≤ b，則兩邊同時加 c 後仍保持 ≤
-- `add_le_add_right` 定理實作加法保序

-- 公設 4.5：乘法保序（正數）(Order Preservation under Multiplication by Positive)
-- 語法：`0 ≤ c → a ≤ b → a * c ≤ b * c` 表示如果 c ≥ 0 且 a ≤ b，則 a * c ≤ b * c
-- `mul_le_mul_of_nonneg_right` 定理實作正數乘法保序

-- 定理：對於任意實數 a，如果 -1 < a < 1 且 a ≠ 0，則 a² > 0
-- 這個定理說明：在區間 (-1, 1) 內的非零實數，其平方必為正數
-- 證明思路：使用全序性將 a ≠ 0 轉換為 a < 0 或 a > 0，然後分情況證明
example (a : ℝ) : -1 < a → a < 1 → a ≠ 0 → a^2 > 0 := by
   -- 步驟 1：引入前提
   -- h1 : -1 < a（雖然在證明中不需要用到，但這是題目給出的條件）
   -- h2 : a < 1（雖然在證明中不需要用到，但這是題目給出的條件）
   -- h3 : a ≠ 0（這是證明的關鍵條件）
   intro h1 h2 h3

   -- 步驟 2：使用全序性（公設 4.1）將 a ≠ 0 轉換為 a < 0 或 a > 0
   -- `ne_iff_lt_or_gt` 定理：`a ≠ 0 ↔ a < 0 ∨ a > 0`
   -- 使用 `.mp` 得到：如果 a ≠ 0，則 a < 0 或 a > 0
   have h4 : a < 0 ∨ a > 0 := ne_iff_lt_or_gt.mp h3

   -- 步驟 3：建立 a² 與 a * a 的等價關係
   -- `pow_two` 定理：`a^2 = a * a`
   -- 這允許我們在 a² 和 a * a 之間轉換
   have h5 : a^2 = a * a := pow_two a

   -- 步驟 4：分情況證明
   -- 使用 `cases` 對 h4 進行分情況討論
   cases h4 with
   -- 情況 1：a < 0
   | inl h_neg =>
      -- 子步驟 4.1：證明 a * a > 0（當 a < 0 時）
      -- `mul_pos_of_neg_of_neg` 定理：如果 a < 0 且 b < 0，則 a * b > 0
      -- 這裡 a < 0 且 a < 0，所以 a * a > 0
      have h6 : a * a > 0 := mul_pos_of_neg_of_neg h_neg h_neg
      -- 子步驟 4.2：使用 calc 建立不等式鏈
      calc
         a^2
         -- 將 a² 轉換為 a * a
         _ = a * a := by rw [h5]
         -- 使用 h6 得到 a * a > 0
         _ > 0 := by exact h6
   -- 情況 2：a > 0
   | inr h_pos =>
      -- 子步驟 4.3：證明 a * a > 0（當 a > 0 時）
      -- `mul_pos` 定理：如果 a > 0 且 b > 0，則 a * b > 0
      -- 這裡 a > 0 且 a > 0，所以 a * a > 0
      have h6 : a * a > 0 := mul_pos h_pos h_pos
      -- 子步驟 4.4：使用 calc 建立不等式鏈
      calc
         a^2
         -- 將 a² 轉換為 a * a
         _ = a * a := by rw [h5]
         -- 使用 h6 得到 a * a > 0
         _ > 0 := by exact h6

-- 定理：對於任意實數 a，如果 0 < a < 1，則 0 < a² < a
-- 這個定理說明：在區間 (0, 1) 內的實數，其平方也在 (0, a) 內，即平方比原數小
-- 證明思路：分別證明 a² > 0 和 a² < a，然後組合這兩個結果
example (a : ℝ) : 0 < a → a < 1 → 0 < a^2 ∧ a^2 < a := by
   -- 步驟 1：引入前提
   -- h1 : 0 < a（a 是正數）
   -- h2 : a < 1（a 小於 1）
   intro h1 h2

   -- 步驟 2：建立 a² 與 a * a 的等價關係
   -- `pow_two` 定理：`a^2 = a * a`
   -- 這允許我們在 a² 和 a * a 之間轉換
   have h3 : a^2 = a * a := pow_two a

   -- 步驟 3：證明 a * a > 0
   -- `mul_pos` 定理：如果 a > 0 且 b > 0，則 a * b > 0
   -- 這裡 a > 0 (h1) 且 a > 0 (h1)，所以 a * a > 0
   have h4 : a * a > 0 := mul_pos h1 h1

   -- 步驟 4：證明 a² > 0
   -- 使用 calc 從 a² = a * a 和 a * a > 0 得到 a² > 0
   have h5 : a^2 > 0 := by
      calc
         a^2
         -- 將 a² 轉換為 a * a
         _ = a * a := h3
         -- 使用 h4：a * a > 0
         _ > 0 := h4

   -- 步驟 5：證明 a² < a
   -- 這是證明的關鍵步驟，需要使用乘法保序性質
   have h6 : a^2 < a := by
      -- 先將 a² 轉換為 a * a
      rw [h3]
      calc
         a * a
         -- 子步驟 5.1：使用乘法保序（公設 4.5）
         -- `mul_lt_mul_of_pos_right` 定理：如果 a < b 且 0 < c，則 c * a < c * b
         -- 這裡 a < 1 (h2) 且 0 < a (h1)，所以 a * a < a * 1
         -- 但我們需要 a * a < 1 * a，所以使用 mul_lt_mul_of_pos_right
         _ < 1 * a := mul_lt_mul_of_pos_right h2 h1
         -- 子步驟 5.2：使用乘法單位元（公設 2.3）
         -- `one_mul` 定理：`1 * a = a`
         _ = a := by rw [one_mul]

   -- 步驟 6：組合兩個結果
   -- 使用 `⟨h5, h6⟩` 將 `a^2 > 0` 和 `a^2 < a` 組合成 `0 < a^2 ∧ a^2 < a`
   exact ⟨h5, h6⟩




/-
### 絕對值 (Absolute Value)

絕對值的定義和性質
-/

-- 絕對值的定義
-- `abs` 是絕對值函數，類型為 `ℝ → ℝ`
-- 語法：`|a|` 是 `abs a` 的簡寫形式
#check abs

-- 定理：對於任意實數 a, b，有 |a * b| = |a| * |b|
-- 這個定理說明：絕對值對乘法是保持的，即乘積的絕對值等於絕對值的乘積
-- 證明思路：分情況討論 a 和 b 的符號（正、負、零）
example (a b : ℝ) : |a * b| = |a| * |b| := by
   have h_a : a ≤ 0 ∨ 0 ≤ a := le_total a 0  -- 對 a 分情況：a ≤ 0 或 a ≥ 0
   have h_b : b ≤ 0 ∨ 0 ≤ b := le_total b 0  -- 對 b 分情況：b ≤ 0 或 b ≥ 0
   cases h_a with  -- 對 a 的情況進行分情況討論
   | inl ha_neg =>  -- 情況 1：a ≤ 0
      cases h_b with  -- 對 b 的情況進行分情況討論
         | inl hb_neg =>  -- 情況 1.1：a ≤ 0 且 b ≤ 0
            have h_ab : a * b ≥ 0 := mul_nonneg_of_nonpos_of_nonpos ha_neg hb_neg  -- 兩個非正數相乘為非負數
            have h1 : |a * b| = a * b := by rw [abs_of_nonneg h_ab]  -- 因為 a * b ≥ 0，所以 |a * b| = a * b
            have h2 : |a| = -a := by rw [abs_of_nonpos ha_neg]  -- 因為 a ≤ 0，所以 |a| = -a
            have h3 : |b| = -b := by rw [abs_of_nonpos hb_neg]  -- 因為 b ≤ 0，所以 |b| = -b
            have h4 : |a| * |b| = -a * -b := by rw [h2, h3]  -- 將 |a| 和 |b| 替換為 -a 和 -b
            have h5 : -a * -b = a * b := by rw [neg_mul_neg]  -- 負數的乘積：(-a) * (-b) = a * b
            have h6 : |a| * |b| = a * b := by  -- 證明 |a| * |b| = a * b
               calc
                  |a| * |b|
                  _ = -a * -b := h4
                  _ = a * b := h5
            have h7 :|a * b| = |a| * |b| := by  -- 組合得到最終結果
               calc
                  |a * b|
                  _ = a * b := h1
                  _ = |a| * |b| := h6.symm
            exact h7
         | inr hb_pos =>  -- 情況 1.2：a ≤ 0 且 b ≥ 0
            have h_ab : a * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha_neg hb_pos  -- 非正數乘以非負數為非正數
            have h1 : |a * b| = - (a * b) := by rw [abs_of_nonpos h_ab]  -- 因為 a * b ≤ 0，所以 |a * b| = -(a * b)
            have h2 : |a| = -a := by rw [abs_of_nonpos ha_neg]  -- 因為 a ≤ 0，所以 |a| = -a
            have h3 : |b| = b := by rw [abs_of_nonneg hb_pos]  -- 因為 b ≥ 0，所以 |b| = b
            have h4 : |a| * |b| = (-a) * b := by rw [h2, h3]  -- 將 |a| 和 |b| 替換為 -a 和 b
            have h5 : -(a * b) = (-a) * b := by rw [neg_mul]  -- 負數的分配：-(a * b) = (-a) * b
            have h6 : |a * b| = |a| * |b| := by  -- 組合得到最終結果
               calc
                  |a * b|
                  _ = - (a * b) := h1
                  _ = (-a) * b := h5
                  _ = |a| * |b| := h4.symm
            exact h6
   | inr ha_pos =>  -- 情況 2：a ≥ 0
      cases h_b with  -- 對 b 的情況進行分情況討論
      | inl hb_neg =>  -- 情況 2.1：a ≥ 0 且 b ≤ 0
         have h_ab : b * a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hb_neg ha_pos  -- 非正數乘以非負數為非正數
         have h1 : a * b = b * a := by rw [mul_comm]  -- 使用乘法交換律
         have h2 : a * b ≤ 0 := by  -- 從 b * a ≤ 0 得到 a * b ≤ 0
            calc
               a * b
               _ = b * a := h1
               _ ≤ 0 := h_ab
         have h3 : |a * b| = - (a * b) := by rw [abs_of_nonpos h2]  -- 因為 a * b ≤ 0，所以 |a * b| = -(a * b)
         have h4 : |a| = a := by rw [abs_of_nonneg ha_pos]  -- 因為 a ≥ 0，所以 |a| = a
         have h5 : |b| = -b := by rw [abs_of_nonpos hb_neg]  -- 因為 b ≤ 0，所以 |b| = -b
         have h6 : |a| * |b| = a * (-b) := by rw [h4, h5]  -- 將 |a| 和 |b| 替換為 a 和 -b
         have h7 : - (a * b) = a * (-b) := by rw [← mul_neg]  -- 負數的分配：-(a * b) = a * (-b)
         have h8 : |a * b| = |a| * |b| := by  -- 組合得到最終結果
            calc
               |a * b|
               _ = - (a * b) := h3
               _ = a * (-b) := h7
               _ = |a| * |b| := h6.symm
         exact h8
      | inr hb_pos =>  -- 情況 2.2：a ≥ 0 且 b ≥ 0
         have h_ab : a * b ≥ 0 := mul_nonneg ha_pos hb_pos  -- 兩個非負數相乘為非負數
         have h1 : |a * b| = a * b := by rw [abs_of_nonneg h_ab]  -- 因為 a * b ≥ 0，所以 |a * b| = a * b
         have h2 : |a| = a := by rw [abs_of_nonneg ha_pos]  -- 因為 a ≥ 0，所以 |a| = a
         have h3 : |b| = b := by rw [abs_of_nonneg hb_pos]  -- 因為 b ≥ 0，所以 |b| = b
         have h4 : |a| * |b| = a * b := by rw [h2, h3]  -- 將 |a| 和 |b| 替換為 a 和 b
         have h6 : |a * b| = |a| * |b| := by  -- 組合得到最終結果
            calc
               |a * b|
               _ = a * b := h1
               _ = |a| * |b| := h4.symm
         exact h6

-- 定理 1.6：對於任意實數 a 和 M ≥ 0，有 |a| ≤ M 若且唯若 -M ≤ a ≤ M
-- 這個定理說明：絕對值不等式 |a| ≤ M 等價於 a 在區間 [-M, M] 內
theorem Theorem_1_6 (a M : ℝ) (hM : M ≥ 0): |a| ≤ M ↔ -M ≤ a ∧ a ≤ M := by
   constructor  -- 分別處理雙向等價的兩個方向
   intro h  -- 方向 1：假設 |a| ≤ M
   have h_a : a ≤ 0 ∨ 0 ≤ a := le_total a 0  -- 對 a 分情況
   cases h_a with
      | inl ha_neg =>  -- 情況 1.1：a ≤ 0
         have h1 : |a| = -a := by rw [abs_of_nonpos ha_neg]  -- 因為 a ≤ 0，所以 |a| = -a
         have h2 : -a ≤ M := by  -- 從 |a| ≤ M 得到 -a ≤ M
            calc
               -a
               _ = |a| := h1.symm
               _ ≤ M := h
         have h3 : (-1 : ℝ) ≤ 0 := by norm_num  -- 證明 -1 ≤ 0
         have h4 : M * (-1) ≤ (-a) * (-1) := mul_le_mul_of_nonpos_right h2 h3  -- 使用負數乘法保序
         have h5 : -M = M * (-1) := by rw [mul_neg_one]  -- M * (-1) = -M
         have h6 : (-a) * (-1) = a := by  -- 證明 (-a) * (-1) = a
            calc
               (-a) * (-1)
               _ = (-1) * (-a) := by rw [mul_comm]
               _ = -(-a) := by rw [neg_one_mul]
               _ = a := by rw [neg_neg]
         have h7 : -M ≤ a := by  -- 組合得到 -M ≤ a
            calc
               -M
               _ = M * (-1) := h5
               _ ≤ (-a) * (-1) := h4
               _ = a := h6
         have h8 : a ≤ M := by  -- 因為 a ≤ 0 且 M ≥ 0
            calc
               a
               _ ≤ 0 := ha_neg
               _ ≤ M := hM
         exact ⟨h7, h8⟩  -- 組合得到 -M ≤ a ∧ a ≤ M
      | inr ha_pos =>  -- 情況 1.2：a ≥ 0
         have h1 : |a| = a := by rw [abs_of_nonneg ha_pos]  -- 因為 a ≥ 0，所以 |a| = a
         have h2 : a ≤ M := by  -- 從 |a| ≤ M 得到 a ≤ M
            calc
               a
               _ = |a| := h1.symm
               _ ≤ M := h
         have h3 : -M ≤ a := by  -- 因為 a ≥ 0 且 M ≥ 0
            calc
               -M
               _ ≤ 0 := neg_nonpos.mpr hM  -- 因為 M ≥ 0，所以 -M ≤ 0
               _ ≤ a := ha_pos  -- 因為 a ≥ 0，所以 0 ≤ a
         have h4 : a ≤ M := by  -- 從 |a| ≤ M 得到 a ≤ M
            calc
               a
               _ = |a| := h1.symm
               _ ≤ M := h
         exact ⟨h3, h4⟩  -- 組合得到 -M ≤ a ∧ a ≤ M
   intro h  -- 方向 2：假設 -M ≤ a ∧ a ≤ M
   rcases h with ⟨h1, h2⟩  -- 分解為 h1 : -M ≤ a 和 h2 : a ≤ M
   have h_a : a ≤ 0 ∨ 0 ≤ a := le_total a 0  -- 對 a 分情況
   cases h_a with
      | inl ha_neg =>  -- 情況 2.1：a ≤ 0
         have h3 : |a| = -a := by rw [abs_of_nonpos ha_neg]  -- 因為 a ≤ 0，所以 |a| = -a
         have h4 : |a| ≤ M := by  -- 證明 |a| ≤ M
            have h4a : -a ≤ M := by  -- 從 -M ≤ a 得到 -a ≤ M
               have h4a1 : (-1 : ℝ) ≤ 0 := by norm_num  -- 證明 -1 ≤ 0
               calc
                  -a
                  _ = a * (-1) := by rw [mul_neg_one]  -- -a = a * (-1)
                  _ ≤ -M * (-1) := mul_le_mul_of_nonpos_right h1 h4a1  -- 使用負數乘法保序
                  _ = -(-M) := by rw [mul_neg_one]  -- -M * (-1) = -(-M)
                  _ = M := by rw [neg_neg]  -- -(-M) = M
            calc
               |a|
               _ = -a := h3
               _ ≤ M := h4a
         exact h4
      | inr ha_pos =>  -- 情況 2.2：a ≥ 0
         have h1 : |a| = a := by rw [abs_of_nonneg ha_pos]  -- 因為 a ≥ 0，所以 |a| = a
         have h2 : |a| ≤ M := by  -- 從 a ≤ M 得到 |a| ≤ M
            calc
               |a|
               _ = a := h1
               _ ≤ M := h2
         exact h2

-- 定理 1.7(1)：對於任意實數 a，有 |a| ≥ 0 且 |a| = 0 若且唯若 a = 0
-- 這個定理說明：絕對值非負，且絕對值為零當且僅當數本身為零
theorem Theorem_1_7_1 (a : ℝ) : |a| ≥ 0 ∧ |a| = 0 ↔ a = 0 := by
   constructor  -- 分別處理雙向等價的兩個方向
   intro h  -- 方向 1：假設 |a| ≥ 0 ∧ |a| = 0
   have h1 : |a| ≥ 0 := h.1  -- 提取 |a| ≥ 0
   have h2 : |a| = 0 := h.2  -- 提取 |a| = 0
   by_contra h_not  -- 假設 a ≠ 0（反證法）
   have h3 : a < 0 ∨ 0 < a := ne_iff_lt_or_gt.mp h_not  -- 從 a ≠ 0 得到 a < 0 或 a > 0
   cases h3 with
   | inl ha_neg =>  -- 情況 1：a < 0
      have h4 : |a| = -a := by rw [abs_of_neg ha_neg]  -- 因為 a < 0，所以 |a| = -a
      have h5 : -a > 0 := by  -- 證明 -a > 0
         have h5a : (-1 : ℝ) < 0 := by norm_num  -- 證明 -1 < 0
         calc
            -a
            _ = a * (-1) := by rw [mul_neg_one]  -- -a = a * (-1)
            _ > 0 * (-1) := mul_lt_mul_of_neg_right ha_neg h5a  -- 使用負數乘法保序（嚴格）
            _ = 0 := by rw [zero_mul]  -- 0 * (-1) = 0
      have h6 : |a| ≠ 0 := by  -- 證明 |a| ≠ 0
         rw [h4]  -- 將 |a| 替換為 -a
         exact ne_of_gt h5  -- 從 -a > 0 得到 -a ≠ 0
      exact h6 h2  -- 與 h2 : |a| = 0 矛盾
   | inr ha_pos =>  -- 情況 2：0 < a
      have h4 : |a| = a := by rw [abs_of_pos ha_pos]  -- 因為 0 < a，所以 |a| = a
      have h5 : |a| ≠ 0 := by  -- 證明 |a| ≠ 0
         rw [h4]  -- 將 |a| 替換為 a
         exact ne_of_gt ha_pos  -- 從 a > 0 得到 a ≠ 0
      exact h5 h2  -- 與 h2 : |a| = 0 矛盾
   intro h  -- 方向 2：假設 a = 0
   have h1 : |a| = 0 := by  -- 證明 |a| = 0
      calc
         |a|
         _ = |0| := by rw [h]  -- 將 a 替換為 0
         _ = 0 := abs_zero  -- |0| = 0
   have h2 : |a| ≥ 0 := abs_nonneg a  -- |a| ≥ 0（絕對值非負）
   exact ⟨h2, h1⟩  -- 組合得到 |a| ≥ 0 ∧ |a| = 0

-- 定理 1.7(2)：對於任意實數 a, b，有 |a - b| = |b - a|
-- 這個定理說明：絕對值對減法具有交換性，即 |a - b| = |b - a|
theorem Theorem_1_7_2 (a b : ℝ) : |a - b| = |b - a| := by
   have h1 : a - b = -(b - a) := by rw [neg_sub]  -- a - b = -(b - a)
   calc
      |a - b|
      _ = |-(b - a)| := by rw [h1]  -- 將 a - b 替換為 -(b - a)
      _ = |b - a| := by rw [abs_neg]  -- |-(b - a)| = |b - a|

-- 定理 1.7(3)：對於任意實數 a, b，有 |a + b| ≤ |a| + |b| 且 ||a| - |b|| ≤ |a - b|
-- 這個定理包含兩個部分：三角不等式和反向三角不等式
theorem Theorem_1_7_3 (a b : ℝ) : |a + b| ≤ |a| + |b| ∧ |(|a| - |b|)| ≤ |a - b| := by
   constructor  -- 分別處理兩個不等式
   have h_ab : a + b ≤ 0 ∨ 0 ≤ a + b := le_total (a + b) 0  -- 對 a + b 分情況
   cases h_ab with  -- 分情況討論
   | inl hab_neg =>  -- 情況 1：a + b ≤ 0
      calc
         |a + b|
         _ = - (a + b) := by rw [abs_of_nonpos hab_neg]  -- 因為 a + b ≤ 0，所以 |a + b| = -(a + b)
         _ = -a + (-b) := by rw [neg_add]  -- -(a + b) = -a + (-b)
         _ = -a - b := by rw [← sub_eq_add_neg]  -- -a + (-b) = -a - b
         _ ≤ |a| + |b| := by  -- 需要證明 -a - b ≤ |a| + |b|
            have h1 : -a ≤ |a| := by  -- 證明 -a ≤ |a|
               have h1a : a ≤ 0 ∨ 0 ≤ a := le_total a 0  -- 對 a 分情況
               cases h1a with
               | inl ha_neg =>  -- 情況 1.1：a ≤ 0
                  have h1a1 : |a| = -a := by rw [abs_of_nonpos ha_neg]  -- 因為 a ≤ 0，所以 |a| = -a
                  calc
                     -a
                     _ = |a| := h1a1.symm  -- -a = |a|
                     _ ≤ |a| := le_refl |a|  -- |a| ≤ |a|
               | inr ha_pos =>  -- 情況 1.2：a ≥ 0
                  have h1a1 : |a| = a := by rw [abs_of_nonneg ha_pos]  -- 因為 a ≥ 0，所以 |a| = a
                  calc
                     -a
                     _ ≤ 0 := neg_nonpos.mpr ha_pos  -- 因為 a ≥ 0，所以 -a ≤ 0
                     _ ≤ a := ha_pos  -- 因為 a ≥ 0，所以 0 ≤ a
                     _ = |a| := h1a1.symm  -- a = |a|
            have h2 : -b ≤ |b| := by  -- 類似地證明 -b ≤ |b|
               have h2a : b ≤ 0 ∨ 0 ≤ b := le_total b 0  -- 對 b 分情況
               cases h2a with
               | inl hb_neg =>  -- 情況 2.1：b ≤ 0
                  have h2a1 : |b| = -b := by rw [abs_of_nonpos hb_neg]  -- 因為 b ≤ 0，所以 |b| = -b
                  calc
                     -b
                     _ = |b| := h2a1.symm  -- -b = |b|
                     _ ≤ |b| := le_refl |b|  -- |b| ≤ |b|
               | inr hb_pos =>  -- 情況 2.2：b ≥ 0
                  have h2a1 : |b| = b := by rw [abs_of_nonneg hb_pos]  -- 因為 b ≥ 0，所以 |b| = b
                  calc
                     -b
                     _ ≤ 0 := neg_nonpos.mpr hb_pos  -- 因為 b ≥ 0，所以 -b ≤ 0
                     _ ≤ b := hb_pos  -- 因為 b ≥ 0，所以 0 ≤ b
                     _ = |b| := h2a1.symm  -- b = |b|
            calc
               -a - b
               _ = -a + (-b) := by rw [← sub_eq_add_neg]  -- -a - b = -a + (-b)
               _ ≤ |a| + |b| := add_le_add h1 h2  -- 使用加法保序
   | inr hab_pos =>  -- 情況 2：a + b ≥ 0
      calc
         |a + b|
         _ = a + b := by rw [abs_of_nonneg hab_pos]  -- 因為 a + b ≥ 0，所以 |a + b| = a + b
         _ ≤ |a| + |b| := by  -- 需要證明 a + b ≤ |a| + |b|
            have h1 : a ≤ |a| := by  -- 證明 a ≤ |a|
               have h1a : a ≤ 0 ∨ 0 ≤ a := le_total a 0  -- 對 a 分情況
               cases h1a with
               | inl ha_neg =>  -- 情況 2.1：a ≤ 0
                  have h1a1 : |a| = -a := by rw [abs_of_nonpos ha_neg]  -- 因為 a ≤ 0，所以 |a| = -a
                  calc
                     a
                     _ ≤ 0 := ha_neg  -- a ≤ 0
                     _ ≤ -a := neg_nonneg.mpr ha_neg  -- 因為 a ≤ 0，所以 0 ≤ -a
                     _ = |a| := h1a1.symm  -- -a = |a|
               | inr ha_pos =>  -- 情況 2.2：a ≥ 0
                  have h1a1 : |a| = a := by rw [abs_of_nonneg ha_pos]  -- 因為 a ≥ 0，所以 |a| = a
                  calc
                     a
                     _ = |a| := h1a1.symm  -- a = |a|
                     _ ≤ |a| := le_refl |a|  -- |a| ≤ |a|
            have h2 : b ≤ |b| := by  -- 類似地證明 b ≤ |b|
               have h2a : b ≤ 0 ∨ 0 ≤ b := le_total b 0  -- 對 b 分情況
               cases h2a with
               | inl hb_neg =>  -- 情況 2.3：b ≤ 0
                  have h2a1 : |b| = -b := by rw [abs_of_nonpos hb_neg]  -- 因為 b ≤ 0，所以 |b| = -b
                  calc
                     b
                     _ ≤ 0 := hb_neg  -- b ≤ 0
                     _ ≤ -b := neg_nonneg.mpr hb_neg  -- 因為 b ≤ 0，所以 0 ≤ -b
                     _ = |b| := h2a1.symm  -- -b = |b|
               | inr hb_pos =>  -- 情況 2.4：b ≥ 0
                  have h2a1 : |b| = b := by rw [abs_of_nonneg hb_pos]  -- 因為 b ≥ 0，所以 |b| = b
                  calc
                     b
                     _ = |b| := h2a1.symm  -- b = |b|
                     _ ≤ |b| := le_refl |b|  -- |b| ≤ |b|
            exact add_le_add h1 h2  -- 使用加法保序
   · -- 證明 ||a| - |b|| ≤ |a - b|（反向三角不等式）
      -- 使用第一個不等式來證明第二個
      -- 從 |a| = |(a - b) + b| ≤ |a - b| + |b| 得到 |a| - |b| ≤ |a - b|
      have h1 : |a| - |b| ≤ |a - b| := by  -- 證明 |a| - |b| ≤ |a - b|
         have h1a : |a| = |(a - b) + b| := by ring  -- |a| = |(a - b) + b|
         -- 需要證明 |(a - b) + b| ≤ |a - b| + |b|，這需要重複使用第一個不等式的證明過程
         have h1b : |(a - b) + b| ≤ |a - b| + |b| := by  -- 對 |(a - b) + b| 應用三角不等式
            -- 重複第一個不等式的證明過程，對 (a - b) 和 b 應用
            have h_ab2 : (a - b) + b ≤ 0 ∨ 0 ≤ (a - b) + b := le_total ((a - b) + b) 0  -- 對 (a - b) + b 分情況
            cases h_ab2 with
            | inl hab2_neg =>  -- 情況 1：(a - b) + b ≤ 0
               calc
                  |(a - b) + b|
                  _ = -((a - b) + b) := by rw [abs_of_nonpos hab2_neg]  -- 因為 (a - b) + b ≤ 0，所以 |(a - b) + b| = -((a - b) + b)
                  _ = -(a - b) - b := by ring  -- -((a - b) + b) = -(a - b) - b
                  _ ≤ |a - b| + |b| := by  -- 需要證明 -(a - b) - b ≤ |a - b| + |b|
                     have h1c : -(a - b) ≤ |a - b| := by  -- 證明 -(a - b) ≤ |a - b|
                        have h1c1 : a - b ≤ 0 ∨ 0 ≤ a - b := le_total (a - b) 0
                        cases h1c1 with
                        | inl hab_neg2 =>
                           have h1c2 : |a - b| = -(a - b) := by rw [abs_of_nonpos hab_neg2]
                           calc
                              -(a - b)
                              _ = |a - b| := h1c2.symm
                              _ ≤ |a - b| := le_refl |a - b|
                        | inr hab_pos2 =>
                           have h1c2 : |a - b| = a - b := by rw [abs_of_nonneg hab_pos2]
                           calc
                              -(a - b)
                              _ ≤ 0 := neg_nonpos.mpr hab_pos2
                              _ ≤ a - b := hab_pos2
                              _ = |a - b| := h1c2.symm
                     have h1d : -b ≤ |b| := by
                        have h1d1 : b ≤ 0 ∨ 0 ≤ b := le_total b 0
                        cases h1d1 with
                        | inl hb_neg2 =>
                           have h1d2 : |b| = -b := by rw [abs_of_nonpos hb_neg2]
                           calc
                              -b
                              _ = |b| := h1d2.symm
                              _ ≤ |b| := le_refl |b|
                        | inr hb_pos2 =>
                           have h1d2 : |b| = b := by rw [abs_of_nonneg hb_pos2]
                           calc
                              -b
                              _ ≤ 0 := neg_nonpos.mpr hb_pos2
                              _ ≤ b := hb_pos2
                              _ = |b| := h1d2.symm
                     calc
                        -(a - b) - b
                        _ = -(a - b) + (-b) := by rw [← sub_eq_add_neg]
                        _ ≤ |a - b| + |b| := add_le_add h1c h1d
            | inr hab2_pos =>
               -- 類似第一個不等式的證明
               calc
                  |(a - b) + b|
                  _ = (a - b) + b := by rw [abs_of_nonneg hab2_pos]
                  _ ≤ |a - b| + |b| := by
                     have h1c : a - b ≤ |a - b| := by
                        have h1c1 : a - b ≤ 0 ∨ 0 ≤ a - b := le_total (a - b) 0
                        cases h1c1 with
                        | inl hab_neg2 =>
                           have h1c2 : |a - b| = -(a - b) := by rw [abs_of_nonpos hab_neg2]
                           calc
                              a - b
                              _ ≤ 0 := hab_neg2
                              _ ≤ -(a - b) := neg_nonneg.mpr hab_neg2
                              _ = |a - b| := h1c2.symm
                        | inr hab_pos2 =>
                           have h1c2 : |a - b| = a - b := by rw [abs_of_nonneg hab_pos2]
                           calc
                              a - b
                              _ = |a - b| := h1c2.symm
                              _ ≤ |a - b| := le_refl |a - b|
                     have h1d : b ≤ |b| := by
                        have h1d1 : b ≤ 0 ∨ 0 ≤ b := le_total b 0
                        cases h1d1 with
                        | inl hb_neg2 =>
                           have h1d2 : |b| = -b := by rw [abs_of_nonpos hb_neg2]
                           calc
                              b
                              _ ≤ 0 := hb_neg2
                              _ ≤ -b := neg_nonneg.mpr hb_neg2
                              _ = |b| := h1d2.symm
                        | inr hb_pos2 =>
                           have h1d2 : |b| = b := by rw [abs_of_nonneg hb_pos2]
                           calc
                              b
                              _ = |b| := h1d2.symm
                              _ ≤ |b| := le_refl |b|
                     exact add_le_add h1c h1d
         calc
            |a| - |b|
            _ = |(a - b) + b| - |b| := by rw [h1a]  -- 將 |a| 替換為 |(a - b) + b|
            _ ≤ (|a - b| + |b|) - |b| := sub_le_sub_right h1b |b|  -- 使用減法保序
            _ = |a - b| := by ring  -- 簡化得到 |a - b|
      have h2 : -|a - b| ≤ |a| - |b| := by  -- 證明 -|a - b| ≤ |a| - |b|
         -- 類似地，從 |b| = |(b - a) + a| ≤ |b - a| + |a| = |a - b| + |a| 得到
         have h2a : |b| = |(b - a) + a| := by ring  -- |b| = |(b - a) + a|
         have h2b : |(b - a) + a| ≤ |b - a| + |a| := by  -- 對 |(b - a) + a| 應用三角不等式
            -- 類似 h1b 的證明
            have h_ba : (b - a) + a ≤ 0 ∨ 0 ≤ (b - a) + a := le_total ((b - a) + a) 0
            cases h_ba with
            | inl hba_neg =>
               calc
                  |(b - a) + a|
                  _ = -((b - a) + a) := by rw [abs_of_nonpos hba_neg]
                  _ = -(b - a) - a := by ring
                  _ ≤ |b - a| + |a| := by
                     -- 類似前面的證明
                     have h2c : -(b - a) ≤ |b - a| := by
                        have h2c1 : b - a ≤ 0 ∨ 0 ≤ b - a := le_total (b - a) 0
                        cases h2c1 with
                        | inl hba_neg2 =>
                           have h2c2 : |b - a| = -(b - a) := by rw [abs_of_nonpos hba_neg2]
                           calc
                              -(b - a)
                              _ = |b - a| := h2c2.symm
                              _ ≤ |b - a| := le_refl |b - a|
                        | inr hba_pos2 =>
                           have h2c2 : |b - a| = b - a := by rw [abs_of_nonneg hba_pos2]
                           calc
                              -(b - a)
                              _ ≤ 0 := neg_nonpos.mpr hba_pos2
                              _ ≤ b - a := hba_pos2
                              _ = |b - a| := h2c2.symm
                     have h2d : -a ≤ |a| := by
                        have h2d1 : a ≤ 0 ∨ 0 ≤ a := le_total a 0
                        cases h2d1 with
                        | inl ha_neg2 =>
                           have h2d2 : |a| = -a := by rw [abs_of_nonpos ha_neg2]
                           calc
                              -a
                              _ = |a| := h2d2.symm
                              _ ≤ |a| := le_refl |a|
                        | inr ha_pos2 =>
                           have h2d2 : |a| = a := by rw [abs_of_nonneg ha_pos2]
                           calc
                              -a
                              _ ≤ 0 := neg_nonpos.mpr ha_pos2
                              _ ≤ a := ha_pos2
                              _ = |a| := h2d2.symm
                     calc
                        -(b - a) - a
                        _ = -(b - a) + (-a) := by rw [← sub_eq_add_neg]
                        _ ≤ |b - a| + |a| := add_le_add h2c h2d
            | inr hba_pos =>
               calc
                  |(b - a) + a|
                  _ = (b - a) + a := by rw [abs_of_nonneg hba_pos]
                  _ ≤ |b - a| + |a| := by
                     have h2c : b - a ≤ |b - a| := by
                        have h2c1 : b - a ≤ 0 ∨ 0 ≤ b - a := le_total (b - a) 0
                        cases h2c1 with
                        | inl hba_neg2 =>
                           have h2c2 : |b - a| = -(b - a) := by rw [abs_of_nonpos hba_neg2]
                           calc
                              b - a
                              _ ≤ 0 := hba_neg2
                              _ ≤ -(b - a) := neg_nonneg.mpr hba_neg2
                              _ = |b - a| := h2c2.symm
                        | inr hba_pos2 =>
                           have h2c2 : |b - a| = b - a := by rw [abs_of_nonneg hba_pos2]
                           calc
                              b - a
                              _ = |b - a| := h2c2.symm
                              _ ≤ |b - a| := le_refl |b - a|
                     have h2d : a ≤ |a| := by
                        have h2d1 : a ≤ 0 ∨ 0 ≤ a := le_total a 0
                        cases h2d1 with
                        | inl ha_neg2 =>
                           have h2d2 : |a| = -a := by rw [abs_of_nonpos ha_neg2]
                           calc
                              a
                              _ ≤ 0 := ha_neg2
                              _ ≤ -a := neg_nonneg.mpr ha_neg2
                              _ = |a| := h2d2.symm
                        | inr ha_pos2 =>
                           have h2d2 : |a| = a := by rw [abs_of_nonneg ha_pos2]
                           calc
                              a
                              _ = |a| := h2d2.symm
                              _ ≤ |a| := le_refl |a|
                     exact add_le_add h2c h2d
         calc
            -|a - b|
            _ = -|b - a| := by rw [abs_sub_comm]  -- |a - b| = |b - a|
            _ ≤ -(|b| - |a|) := by  -- 需要證明 -|b - a| ≤ -(|b| - |a|)
               -- 從 |b| ≤ |b - a| + |a| 得到 |b| - |a| ≤ |b - a|
               -- 所以 -|b - a| ≤ -(|b| - |a|)
               have h2c : |b| - |a| ≤ |b - a| := by  -- 證明 |b| - |a| ≤ |b - a|
                  calc
                     |b| - |a|
                     _ = |(b - a) + a| - |a| := by rw [h2a]  -- 將 |b| 替換為 |(b - a) + a|
                     _ ≤ (|b - a| + |a|) - |a| := sub_le_sub_right h2b |a|  -- 使用減法保序
                     _ = |b - a| := by ring  -- 簡化得到 |b - a|
               exact neg_le_neg h2c  -- 使用負數保序（方向反轉）
            _ = |a| - |b| := by ring  -- 簡化得到 |a| - |b|
      exact abs_le.mpr ⟨h2, h1⟩  -- 從 -|a - b| ≤ |a| - |b| ≤ |a - b| 得到 ||a| - |b|| ≤ |a - b|

-- 定理 1.9(1)：對於任意實數 x, y，有 (∀ ε > 0, x < y + ε) ↔ x ≤ y
-- 這個定理說明：x 小於等於 y 若且唯若對於所有正數 ε，x 都小於 y + ε
theorem Theorem_1_9_1 (x y : ℝ) : (∀ ε > 0, x < y + ε) ↔ x ≤ y := by
   constructor  -- 分別處理雙向等價的兩個方向
   intro h  -- 方向 1：假設 ∀ ε > 0, x < y + ε
   by_contra h_not  -- 假設 ¬(x ≤ y)，即 x > y（反證法）
   push_neg at h_not  -- 將 ¬(x ≤ y) 轉換為 x > y
   have h1 : x - y > 0 := by  -- 從 x > y 得到 x - y > 0
      calc
         x - y
         _ > y - y := sub_lt_sub_right h_not y  -- 從 x > y 得到 x - y > y - y
         _ = 0 := sub_self y  -- y - y = 0
   have h2 : x < y + (x - y) := h (x - y) h1  -- 對 ε = x - y 應用假設 h
   have h3 : y + (x - y) = x := by ring  -- y + (x - y) = x
   rw [h3] at h2  -- 將 y + (x - y) 替換為 x
   exact lt_irrefl x h2  -- 矛盾：x < x
   intro h ε hε  -- 方向 2：假設 x ≤ y，引入任意 ε > 0
   have h_cases : x < y ∨ x = y := lt_or_eq_of_le h  -- 從 x ≤ y 得到 x < y 或 x = y
   cases h_cases with
   | inl h_lt =>  -- 情況 1：x < y
      calc
         x
         _ < y := h_lt  -- x < y
         _ < y + ε := lt_add_of_pos_right y hε  -- 因為 ε > 0，所以 y < y + ε
   | inr h_eq =>  -- 情況 2：x = y
      calc
         x
         _ = y := h_eq  -- x = y
         _ < y + ε := lt_add_of_pos_right y hε  -- 因為 ε > 0，所以 y < y + ε

-- 定理 1.9(2)：對於任意實數 x, y，有 (∀ ε > 0, x > y - ε) ↔ x ≥ y
-- 這個定理說明：x 大於等於 y 若且唯若對於所有正數 ε，x 都大於 y - ε
theorem Theorem_1_9_2 (x y : ℝ) : (∀ ε > 0, x > y - ε) ↔ x ≥ y := by
   constructor  -- 分別處理雙向等價的兩個方向
   intro h  -- 方向 1：假設 ∀ ε > 0, x > y - ε
   by_contra h_not  -- 假設 ¬(x ≥ y)，即 x < y（反證法）
   push_neg at h_not  -- 將 ¬(x ≥ y) 轉換為 x < y
   have h1 : y - x > 0 := by  -- 從 x < y 得到 y - x > 0
      calc
         y - x
         _ > x - x := sub_lt_sub_right h_not x  -- 從 x < y 得到 y - x > x - x
         _ = 0 := sub_self x  -- x - x = 0
   have h2 : x > y - (y - x) := h (y - x) h1  -- 對 ε = y - x 應用假設 h
   have h3 : y - (y - x) = x := by ring  -- y - (y - x) = x
   rw [h3] at h2  -- 將 y - (y - x) 替換為 x
   exact lt_irrefl x h2  -- 矛盾：x > x
   intro h ε hε  -- 方向 2：假設 x ≥ y，引入任意 ε > 0
   have h_cases : y < x ∨ y = x := lt_or_eq_of_le h  -- 從 x ≥ y（即 y ≤ x）得到 y < x 或 y = x
   cases h_cases with
   | inl h_lt =>  -- 情況 1：y < x，即 x > y
      calc
         x
         _ > y := h_lt  -- 從 y < x 得到 x > y
         _ > y - ε := by  -- 需要證明 y > y - ε
            calc
               y
               _ = y - 0 := by ring  -- y = y - 0
               _ > y - ε := sub_lt_sub_left hε y  -- 從 0 < ε 得到 y - 0 > y - ε
   | inr h_eq =>  -- 情況 2：y = x，即 x = y
      calc
         x
         _ = y := h_eq.symm  -- x = y
         _ > y - ε := by  -- 需要證明 y > y - ε
            calc
               y
               _ = y - 0 := by ring  -- y = y - 0
               _ > y - ε := sub_lt_sub_left hε y  -- 從 0 < ε 得到 y - 0 > y - ε

-- (3) |a| < ε, ∀ ε > 0 ↔ a = 0
theorem Theorem_1_9_3 (a : ℝ) : (∀ ε > 0, |a| < ε) ↔ a = 0 := by
   constructor  -- 分別處理雙向等價的兩個方向
   intro h  -- 方向 1：假設 ∀ ε > 0, |a| < ε
   have h1 : ∀ ε > 0, |a| < 0 + ε := by  -- 將 |a| < ε 改寫為 |a| < 0 + ε
      intro ε hε  -- 引入 ε 和 ε > 0
      calc
         |a|
         _ < ε := h ε hε  -- 應用 h
         _ = 0 + ε := by ring  -- ε = 0 + ε
   have h2 : |a| ≤ 0 := (Theorem_1_9_1 |a| 0).1 h1  -- 使用 Theorem 1.9(1) 得到 |a| ≤ 0
   have h3 : |a| ≥ 0 := abs_nonneg a  -- |a| ≥ 0（絕對值非負）
   have h4 : |a| = 0 := le_antisymm h2 h3  -- 從 |a| ≤ 0 和 |a| ≥ 0 得到 |a| = 0
   have h5 : a = 0 := (Theorem_1_7_1 a).1 ⟨h3, h4⟩  -- 使用 Theorem 1.7(1) 得到 a = 0
   exact h5  -- 完成方向 1 的證明
   intro h  -- 方向 2：假設 a = 0
   have h1 : |a| ≥ 0 ∧ |a| = 0 := (Theorem_1_7_1 a).mpr h  -- 使用 Theorem 1.7(1) 得到 |a| ≥ 0 ∧ |a| = 0
   have h2 : |a| = 0 := h1.2  -- 提取 |a| = 0
   have h3 : ∀ ε > 0, |a| < ε := by  -- 證明 ∀ ε > 0, |a| < ε
      intro ε hε  -- 引入 ε 和 ε > 0
      calc
         |a|
         _ = 0 := h2  -- |a| = 0
         _ < ε := hε  -- 0 < ε
   exact h3  -- 完成方向 2 的證明

-- 絕對值的三角不等式
-- 語法：`|a|` 是絕對值的記號，`≤` 是小於等於
-- 三角不等式：|a + b| ≤ |a| + |b|
-- `abs_add_le` 是三角不等式的定理

-- 絕對值的其他性質
-- 語法：`≥` 表示大於等於，等價於 `≤` 的反向
-- `abs_nonneg` 表示絕對值非負

-- 語法：`↔` 表示雙向蘊含（若且唯若，iff）
-- `abs_eq_zero` 表示：|a| = 0 若且唯若 a = 0

-- 定義 1.10：上界與上確界
def is_upper_bound (M : ℝ) (E : Set ℝ) : Prop :=
   ∀ a ∈ E, a ≤ M  -- M 是集合 E 的上界：對所有 a ∈ E，有 a ≤ M

def bounded_above (E : Set ℝ) : Prop :=
   ∃ M : ℝ, is_upper_bound M E  -- 集合 E 有上界：存在 M 使得 M 是 E 的上界

def is_supremum (s : ℝ) (E : Set ℝ) : Prop :=
   is_upper_bound s E ∧ (∀ M : ℝ, is_upper_bound M E → s ≤ M)  -- s 是 E 的上確界：s 是上界，且是所有上界中最小的

-- Example 1.11. If E = [0, 1],prove that sup E = 1.
theorem Example_1_11 : is_supremum 1 (Set.Icc 0 1) := by
   constructor  -- 分開 is_supremum 的兩個部分：上界性和最小性
   intro x hx  -- 第一部分：引入 x 和 x ∈ [0, 1]
   exact hx.2  -- 從 x ∈ [0, 1] 得到 x ≤ 1（hx.2 提取第二個條件）
   intro M hM  -- 第二部分：引入 M 和 hM : M 是 [0, 1] 的上界
   by_contra h_not  -- 假設 ¬(1 ≤ M)（反證法）
   push_neg at h_not  -- 將 ¬(1 ≤ M) 轉換為 M < 1
   have h1_in : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by  -- 證明 1 ∈ [0, 1]
      exact ⟨ by norm_num, by norm_num ⟩  -- 0 ≤ 1 且 1 ≤ 1（norm_num 自動證明）
   have h_contra : 1 ≤ M := hM 1 h1_in  -- 因為 M 是上界，所以 1 ≤ M
   have h : (1 : ℝ) < 1 := lt_of_le_of_lt h_contra h_not  -- 從 1 ≤ M 和 M < 1 得到 1 < 1
   exact lt_irrefl (1 : ℝ) h  -- 1 < 1 矛盾（lt_irrefl 表示一個數不能嚴格小於自己）

-- Remark 1.12. If a set has one upper bound, it has infinitely many upper bounds.
theorem Remark_1_12 (E : Set ℝ) (M : ℝ) (hM : is_upper_bound M E) :
   ∀ N : ℝ, N ≥ M → is_upper_bound N E := by
   intro N hN a ha  -- 引入 N、N ≥ M、a 和 a ∈ E
   have h1 : a ≤ M := hM a ha  -- 因為 M 是上界，所以 a ≤ M
   exact le_trans h1 hN  -- 從 a ≤ M 和 M ≤ N 得到 a ≤ N（傳遞性）

-- Remark 1.13. If a set has a supremum, then it has only one supremum.
theorem Remark_1_13 (E : Set ℝ) (s1 s2 : ℝ) (hs1 : is_supremum s1 E) (hs2 : is_supremum s2 E) :
   s1 = s2 := by
   have h1 : s1 ≤ s2 := hs1.2 s2 hs2.1  -- s1 是上確界，s2 是上界，所以 s1 ≤ s2
   have h2 : s2 ≤ s1 := hs2.2 s1 hs1.1  -- s2 是上確界，s1 是上界，所以 s2 ≤ s1
   have h4 : s1 = s2 := le_antisymm h1 h2  -- 從 s1 ≤ s2 和 s2 ≤ s1 得到 s1 = s2
   exact h4  -- 完成證明

-- Theorem 1.14. If E has a finite supremum and ε > 0 is any positive number, then there is a point a ∈ E such that
-- sup E - ε < a ≤ sup E.
theorem Theorem_1_14 (E : Set ℝ) (s : ℝ) (hs : is_supremum s E) (ε : ℝ) (hε : ε > 0) :
   ∃ a ∈ E, s - ε < a ∧ a ≤ s := by
   by_contra h_not  -- 假設不存在這樣的 a（反證法）
   have h1 : ∀ a ∈ E, a ≤ s - ε := by  -- 證明對所有 a ∈ E，有 a ≤ s - ε
      intro a ha  -- 引入 a ∈ E
      have h2 : a ≤ s := hs.1 a ha  -- s 是上界，所以 a ≤ s
      by_cases h3 : s - ε < a  -- 分情況：s - ε < a 或 s - ε ≥ a
      · have h4 : s - ε < a ∧ a ≤ s := ⟨ h3, h2 ⟩  -- 如果 s - ε < a，則滿足條件
        exact absurd ⟨ a, ha, h4 ⟩ h_not  -- 與 h_not 矛盾（存在這樣的 a）
      · push_neg at h3  -- s - ε ≥ a，即 a ≤ s - ε
        exact h3  -- 這就是我們要的
   have h5 : is_upper_bound (s - ε) E := h1  -- s - ε 是上界
   have h6 : s ≤ s - ε := hs.2 (s - ε) h5  -- s 是上確界，所以 s ≤ s - ε
   have h7 : ε ≤ 0 := by linarith  -- 從 s ≤ s - ε 得到 ε ≤ 0
   exact not_le_of_gt hε h7  -- ε > 0 與 ε ≤ 0 矛盾

-- Theorem 1.15. If E ⊆ ℤ has a supremum, then sup E ∈ E. In particular, if the
-- supremum of a set, which contains only integers, exists, that supremum must be
-- an integer.
theorem Theorem_1_15 (E : Set ℤ) (s : ℝ) (hs : is_supremum s (E.image (Int.cast : ℤ → ℝ))) :
   (s : ℝ) ∈ (E.image (Int.cast : ℤ → ℝ)) := by
   by_contra h_not  -- 反證法：假設 s 不在 E 的像中
   have h1 : ∃ a ∈ E.image (Int.cast : ℤ → ℝ), s - (1/2 : ℝ) < a ∧ a ≤ s :=
      Theorem_1_14 (E.image (Int.cast : ℤ → ℝ)) s hs (1/2 : ℝ) (by norm_num)  -- 使用定理 1.14，取 ε = 1/2
   obtain ⟨a, ha_in, h1_left, h1_right⟩ := h1  -- 分解存在性證明，得到 a ∈ E 的像，且 s - 1/2 < a ≤ s
   obtain ⟨n, hn_in, hn_eq⟩ := ha_in  -- 因為 a 在 E 的像中，存在整數 n ∈ E 使得 a = ↑n
   have h2 : a = (n : ℝ) := hn_eq.symm  -- a 等於整數 n 的實數轉換
   have h3 : a < s := by  -- 證明 a < s（關鍵步驟）
      by_contra h_eq  -- 假設 a ≥ s
      push_neg at h_eq  -- 轉換為 a ≥ s
      have h4 : a = s := le_antisymm h1_right h_eq  -- 從 a ≤ s 和 a ≥ s 得到 a = s
      rw [← h2, h4] at hn_eq  -- 將 a 替換為 s，得到 s = ↑n
      have h5 : s = (n : ℝ) := h4.symm.trans h2  -- s = a = ↑n
      have h6 : (n : ℝ) ∈ E.image (Int.cast : ℤ → ℝ) := ⟨ n, hn_in, rfl ⟩  -- n 在 E 的像中
      rw [← h5] at h6  -- 將 ↑n 替換為 s
      exact h_not h6  -- 與假設矛盾（s 在 E 的像中）
   have h7 : s - a > 0 := sub_pos.mpr h3  -- 從 a < s 得到 s - a > 0
   have h8 : ∃ b ∈ E.image (Int.cast : ℤ → ℝ), a < b ∧ b ≤ s := by  -- 存在另一個整數 b，使得 a < b ≤ s
      have h9 : ∃ b ∈ E.image (Int.cast : ℤ → ℝ), s - (s - a) < b ∧ b ≤ s :=
         Theorem_1_14 (E.image (Int.cast : ℤ → ℝ)) s hs (s - a) h7  -- 使用定理 1.14，取 ε = s - a
      obtain ⟨ b, hb_in, hb_left, hb_right⟩ := h9  -- 分解存在性證明
      have h10 : a = s - (s - a) := by ring  -- 代數恆等式：a = s - (s - a)
      have h11 : a < b := by rw [h10]; exact hb_left  -- 從 s - (s - a) < b 得到 a < b
      use b, hb_in, h11, hb_right  -- 構造存在性證明
   obtain ⟨ b, hb_in, hb_left, hb_right⟩ := h8  -- 分解得到整數 b，滿足 a < b ≤ s
   obtain ⟨ m, hm_in, hm_eq⟩ := hb_in  -- 因為 b 在 E 的像中，存在整數 m ∈ E 使得 b = ↑m
   have h12 : b = (m : ℝ) := hm_eq.symm  -- b 等於整數 m 的實數轉換
   have h13 : 0 < b - a := sub_pos.mpr hb_left  -- 從 a < b 得到 b - a > 0
   have h14 : b - a < 1 := by  -- 證明 b - a < 1（關鍵不等式）
      have h15 : s - (1/2 : ℝ) < a := h1_left  -- 從 h1 得到 s - 1/2 < a
      calc
         b - a
         _ ≤ s - a := sub_le_sub_right hb_right a  -- 從 b ≤ s 得到 b - a ≤ s - a
         _ < 1/2 := by linarith  -- 從 s - 1/2 < a 得到 s - a < 1/2
         _ < 1 := by norm_num  -- 1/2 < 1
   have h16 : b - a = (m - n : ℝ) := by rw [h12, h2]  -- b - a = ↑m - ↑n = ↑(m - n)
   have h17 : (0 : ℝ) < (m - n : ℝ) ∧ (m - n : ℝ) < 1 := by  -- 0 < ↑(m - n) < 1
      constructor
      rw [← h16]; exact h13  -- 從 b - a > 0 得到 ↑(m - n) > 0
      rw [← h16]; exact h14  -- 從 b - a < 1 得到 ↑(m - n) < 1
   have h18 : ¬ (∃ k : ℤ, (0 : ℝ) < (k : ℝ) ∧ (k : ℝ) < 1) := by  -- 不存在整數 k 使得 0 < ↑k < 1
      intro h  -- 假設存在這樣的 k
      obtain ⟨ k, hk_left, hk_right⟩ := h  -- 分解存在性證明
      have h19 : (k : ℤ) ≤ 0 ∨ (k : ℤ) ≥ 1 := by  -- 整數的三歧性：k ≤ 0 或 k ≥ 1
         by_cases h_le : (k : ℤ) ≤ 0  -- 分情況：k ≤ 0 或 k > 0
         left; exact h_le  -- 情況 1：k ≤ 0
         right  -- 情況 2：k > 0
         push_neg at h_le  -- 轉換為 k > 0
         exact Int.add_one_le_of_lt h_le  -- 從 k > 0 得到 k ≥ 1（整數性質）
      cases h19 with
      | inl h_le =>  -- 情況 1：k ≤ 0
         have h20 : (k : ℝ) ≤ 0:= by
            rw [← Int.cast_zero]
            exact Int.cast_le.mpr h_le  -- 整數轉換保序：k ≤ 0 則 ↑k ≤ 0
         linarith  -- 與 hk_left : ↑k > 0 矛盾
      | inr h_ge =>  -- 情況 2：k ≥ 1
         have h21 : (k : ℝ) ≥ 1 := by
            rw [← Int.cast_one]
            exact Int.cast_le.mpr h_ge  -- 整數轉換保序：k ≥ 1 則 ↑k ≥ 1
         linarith  -- 與 hk_right : ↑k < 1 矛盾
   -- 使用 Int.cast_sub 转换：↑(m - n) = ↑m - ↑n
   -- 注意：(m - n : ℝ) 等价于 ↑(m - n)
   have h22 : (0 : ℝ) < ↑(m - n) := by  -- 證明 0 < ↑(m - n)
      calc
         (0 : ℝ)
         _ < ↑m - ↑n := h17.1  -- 從 h17 得到 0 < ↑m - ↑n
         _ = ↑(m - n) := (Int.cast_sub m n).symm  -- 使用整數轉換的減法性質
   have h23 : ↑(m - n) < (1 : ℝ) := by  -- 證明 ↑(m - n) < 1
      calc
         ↑(m - n)
         _ = ↑m - ↑n := Int.cast_sub m n  -- 使用整數轉換的減法性質
         _ < (1 : ℝ) := h17.2  -- 從 h17 得到 ↑m - ↑n < 1
   exact h18 ⟨m - n, h22, h23⟩  -- 與 h18 矛盾（存在整數 m - n 使得 0 < ↑(m - n) < 1）

end WadeAnalysis
