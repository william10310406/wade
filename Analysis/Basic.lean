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

-- Completeness Axiom : If E is a nonempty subset of ℝ that is bounded above,
-- then E has a finite supremum.

-- Theorem 1.16 : Given real numbers a and b, with a > 0, there is an integer n ∈ ℕ such that b < na.
theorem Theorem_1_16 (a b : ℝ) (ha : a > 0) :  -- 定理 1.16（阿基米德性質）：給定正實數 a 和任意實數 b
   ∃ n : ℕ, b < n * a := by  -- 存在自然數 n 使得 b < n * a
   by_cases h_case : b < a  -- 情況分析：b < a 或 a ≤ b
   use 1  -- 若 b < a，取 n = 1
   simp  -- 簡化目標為 b < a
   exact h_case  -- 用假設 b < a 完成證明
   push_neg at h_case  -- 否則，將 ¬(b < a) 轉換為 a ≤ b
   let E : Set ℝ := {x : ℝ | ∃ k : ℕ, x = (k : ℝ) * a ∧ (k : ℝ) * a ≤ b}  -- 定義集合 E = {ka | k ∈ ℕ 且 ka ≤ b}
   have h_nonempty : Set.Nonempty E := by  -- 證明 E 非空
      use (1 : ℝ) * a  -- 提供元素 1 * a
      use 1  -- 提供自然數 k = 1
      constructor  -- 證明合取：(1) 1 * a = 1 * a，(2) 1 * a ≤ b
      · simp  -- 證明等式 (1 : ℝ) * a = (1 : ℝ) * a
      · simp  -- 簡化 1 * a 為 a
        exact h_case  -- 使用 a ≤ b 證明 1 * a ≤ b
   have h_bounded : bounded_above E := by  -- 證明 E 有上界
      use b  -- 聲稱 b 是 E 的上界
      intro x hx  -- 對任意 x ∈ E
      obtain ⟨ k, hk_eq, hk_le⟩ := hx  -- 從 x ∈ E 得到：x = ka 且 ka ≤ b
      rw [hk_eq]  -- 將 x 改寫為 ka
      exact hk_le  -- 用 ka ≤ b 證明 x ≤ b
   have h_sup : ∃ s : ℝ, is_supremum s E := by  -- 證明 E 有上確界
      have h_bdd : BddAbove E := by  -- 先將 bounded_above 轉換為 Mathlib 的 BddAbove
         obtain ⟨M, hM⟩ := h_bounded  -- 從 bounded_above E 取得上界 M
         use M  -- 用 M 構造 BddAbove 的證明
         exact hM  -- M 是 E 的上界
      use sSup E  -- 應用完備性公設：使用 Mathlib 的 sSup（上確界）
      constructor  -- 證明 sSup E 滿足上確界的兩個性質
      · intro x hx  -- (1) sSup E 是上界：對任意 x ∈ E
        exact le_csSup h_bdd hx  -- 用 Mathlib 定理證明 x ≤ sSup E
      · intro M hM  -- (2) sSup E 是最小上界：對任意 E 的上界 M
        exact csSup_le h_nonempty hM  -- 用 Mathlib 定理證明 sSup E ≤ M
   obtain ⟨s, hs_sup⟩ := h_sup  -- 取得上確界 s 及其性質 hs_sup
   have h_s_in_E : s ∈ E := by  -- 證明 s ∈ E（關鍵步驟）
      by_contra h_not  -- 反證法：假設 s ∉ E
      have h_eps_pos : a / 2 > 0 := div_pos ha (by norm_num)  -- a / 2 > 0（因為 a > 0）
      have h_approx : ∃ x ∈ E, s - (a / 2) < x ∧ x ≤ s :=  -- 由定理 1.14（上確界逼近性質）
         Theorem_1_14 E s hs_sup (a / 2) h_eps_pos  -- 存在 x ∈ E 使得 s - a/2 < x ≤ s
      obtain ⟨x, hx_in, hx_left, hx_right⟩ := h_approx  -- 取得這樣的 x 及其性質
      obtain ⟨k, hk_eq, hk_le⟩ := hx_in  -- 從 x ∈ E 得到：x = ka 且 ka ≤ b
      have h_x_lt_s : x < s := by  -- 證明 x < s（嚴格小於）
         by_contra h_ge  -- 反證法：假設 ¬(x < s)
         push_neg at h_ge  -- 轉換為 s ≤ x
         have h_eq : x = s := le_antisymm hx_right h_ge  -- 由 x ≤ s 和 s ≤ x 得 x = s
         rw [hk_eq] at h_eq  -- 將 x = ka 代入得 ka = s
         have h_s_in : s ∈ E := by  -- 這表示 s ∈ E
            use k  -- 見證者為 k
            exact ⟨h_eq.symm, hk_le⟩  -- s = ka 且 ka ≤ b
         exact h_not h_s_in  -- 矛盾：s ∈ E 但我們假設 s ∉ E
      have h_gap : s - x > 0 := sub_pos.mpr h_x_lt_s  -- 由 x < s 得 s - x > 0
      have h_approx2 : ∃ y ∈ E, s - (s - x) < y ∧ y ≤ s :=  -- 再次應用定理 1.14
         Theorem_1_14 E s hs_sup (s - x) h_gap  -- 存在 y ∈ E 使得 x < y ≤ s
      obtain ⟨y, hy_in, hy_left, hy_right⟩ := h_approx2  -- 取得這樣的 y
      obtain ⟨m, hm_eq, hm_le⟩ := hy_in  -- 從 y ∈ E 得到：y = ma 且 ma ≤ b
      have h_y_gt_x : y > x := by  -- 證明 y > x
         have h10 : x = s - (s - x) := by ring  -- 代數計算：x = s - (s - x)
         rw [h10]  -- 改寫目標
         exact hy_left  -- 由 s - (s - x) < y 得證
      rw [hk_eq, hm_eq] at h_y_gt_x  -- 改寫為 ma > ka
      have h_m_gt_k : (m : ℕ) > k := by  -- 證明 m > k（作為自然數）
         by_contra h_le  -- 反證法：假設 ¬(m > k)
         push_neg at h_le  -- 轉換為 m ≤ k
         have h_m_le_k : (m : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr h_le  -- 轉型到實數：m ≤ k
         have h_mul_le : (m : ℝ) * a ≤ (k : ℝ) * a := by  -- 兩邊乘以 a
            have h_pos : 0 ≤ a := le_of_lt ha  -- a ≥ 0
            exact mul_le_mul_of_nonneg_right h_m_le_k h_pos  -- 得 ma ≤ ka
         linarith  -- 矛盾：ma ≤ ka 但 ma > ka
      have h_m_ge_k1 : (m : ℕ) ≥ k + 1 := Nat.succ_le_of_lt h_m_gt_k  -- 由 m > k 得 m ≥ k + 1
      have h_n_in_E : ((k + 1 : ℕ) : ℝ) * a ∈ E := by  -- 證明 (k+1)a ∈ E
         have h_k1_le_b : ((k + 1 : ℕ) : ℝ) * a ≤ b := by  -- 證明 (k+1)a ≤ b
            have h_mul_le : ((k + 1 : ℕ) : ℝ) * a ≤ (m : ℝ) * a := by  -- 先證 (k+1)a ≤ ma
               have h_nat_le : (k + 1 : ℕ) ≤ m := h_m_ge_k1  -- k + 1 ≤ m
               have h_cast_le : ((k + 1 : ℕ) : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr h_nat_le  -- 轉型到實數
               have h_pos : 0 ≤ a := le_of_lt ha  -- a ≥ 0
               exact mul_le_mul_of_nonneg_right h_cast_le h_pos  -- 兩邊乘以 a
            have h_y_le_s : y ≤ s := hy_right  -- y ≤ s
            have h_s_le_b : s ≤ b := by  -- 證明 s ≤ b
               have h_b_ub : is_upper_bound b E := by  -- b 是 E 的上界
                  intro z hz  -- 對任意 z ∈ E
                  obtain ⟨n, hn_eq, hn_le⟩ := hz  -- z = na 且 na ≤ b
                  rw [hn_eq]  -- 改寫 z 為 na
                  exact hn_le  -- z = na ≤ b
               exact hs_sup.2 b h_b_ub  -- s 是最小上界，所以 s ≤ b
            have h_m_le_b : (m : ℝ) * a ≤ b := hm_le  -- ma ≤ b
            linarith  -- 由 (k+1)a ≤ ma 和 ma ≤ b 得 (k+1)a ≤ b
         use k + 1, rfl, h_k1_le_b  -- 構造證明：(k+1)a = (k+1)a 且 (k+1)a ≤ b
      have h_n_gt_s : ((k + 1 : ℕ) : ℝ) * a > s := by  -- 證明 (k+1)a > s
         have h_add : ((k + 1 : ℕ) : ℝ) * a = (k : ℝ) * a + a := by simp; ring  -- (k+1)a = ka + a
         rw [h_add]  -- 改寫目標為 ka + a > s
         have h_x_eq : x = (k : ℝ) * a := hk_eq  -- x = ka
         rw [← h_x_eq]  -- 改寫為 x + a > s
         linarith  -- 由 s - x < a/2 < a 推得 x + a > s
      have h_n_le_s : ((k + 1 : ℕ) : ℝ) * a ≤ s := hs_sup.1 _ h_n_in_E  -- 由 (k+1)a ∈ E 和 s 是上界得 (k+1)a ≤ s
      linarith  -- 矛盾：(k+1)a > s 且 (k+1)a ≤ s，所以原假設 s ∉ E 不成立
   obtain ⟨k, hk_eq, hk_le⟩ := h_s_in_E  -- 從 s ∈ E 得到：s = ka 且 ka ≤ b
   use k + 1  -- 取 n = k + 1
   by_cases h_case2 : ((k + 1 : ℕ) : ℝ) * a ≤ b  -- 情況分析：(k+1)a ≤ b 或 b < (k+1)a
   · have h_n_in_E : ((k + 1 : ℕ) : ℝ) * a ∈ E := ⟨k + 1, rfl, h_case2⟩  -- 若 (k+1)a ≤ b，則 (k+1)a ∈ E
     have h_gt : ((k + 1 : ℕ) : ℝ) * a > s := by  -- 證明 (k+1)a > s
        have h_add : ((k + 1 : ℕ) : ℝ) * a = (k : ℝ) * a + a := by simp; ring  -- (k+1)a = ka + a
        rw [h_add, ← hk_eq]  -- 改寫為 s + a > s（因為 s = ka）
        linarith  -- 由 a > 0 得 s + a > s
     have h_le : ((k + 1 : ℕ) : ℝ) * a ≤ s := hs_sup.1 _ h_n_in_E  -- 由 (k+1)a ∈ E 和 s 是上界得 (k+1)a ≤ s
     have h_s_lt_s : s < s := by  -- 推出矛盾：s < s
        have h_lt : s < ((k + 1 : ℕ) : ℝ) * a := gt_iff_lt.mp h_gt  -- 由 (k+1)a > s 得 s < (k+1)a
        exact lt_of_lt_of_le h_lt h_le  -- 由 s < (k+1)a 和 (k+1)a ≤ s 得 s < s
     exact False.elim (lt_irrefl s h_s_lt_s)  -- 矛盾消去：由 s < s（不可能）證明任何結論
   · push_neg at h_case2  -- 否則，¬((k+1)a ≤ b) 即 b < (k+1)a
     exact h_case2  -- 這正是我們要證明的目標 b < (k+1)a

-- Theorem 1.18 : If a, b ∈ ℝ satisfy a < b, then there is a q ∈ ℚ ∋ a < q < b.
theorem Theorem_1_18 (a b : ℝ) (hab : a < b) : ∃ q : ℚ, a < q ∧ q < b := by  -- 定理 1.18：有理數稠密性，給定 a < b，存在有理數 q 使得 a < q < b
   have h_pos : 0 < b - a := sub_pos.mpr hab  -- 由 a < b 得到 0 < b - a
   have h_arch1 : ∃ n : ℕ, (1 : ℝ) < n * (b - a) := Theorem_1_16 (b - a) 1 h_pos  -- 由阿基米德性質得到存在自然數 n 使得 1 < n * (b - a)
   obtain ⟨n, hn_gt⟩ := h_arch1  -- 取出這樣的 n，並記 hn_gt : 1 < n * (b - a)
   have hn_pos : (n : ℝ) > 0 := by  -- 證明 n > 0（反證法）
      by_contra h_neg  -- 假設 n 不大於 0
      push_neg at h_neg  -- 轉換為 n ≤ 0
      have hn_noneg : (n : ℝ) ≥ 0 := Nat.cast_nonneg n  -- 但自然數必定 ≥ 0
      have hn_zero : (n : ℝ) = 0 := le_antisymm h_neg hn_noneg  -- 所以 n = 0
      rw [hn_zero] at hn_gt  -- 代入得 1 < 0 * (b - a)
      simp at hn_gt  -- 化簡得 1 < 0
      norm_num at hn_gt  -- 這是矛盾，完成反證
   have h_inv : (1 : ℝ) / n < b - a := by  -- 證明 1/n < b - a
      have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos  -- n > 0 故 n ≠ 0
      suffices 1 < n * (b - a) by  -- 只需證明 1 < n * (b - a)（反向推理）
         calc (1 : ℝ) / n  -- 計算鏈證明 1/n < b - a
            _ = 1 / n * 1 := by ring  -- 1/n = (1/n) * 1
            _ < 1 / n * (n * (b - a)) := by  -- (1/n) * 1 < (1/n) * (n * (b - a))
               apply mul_lt_mul_of_pos_left this  -- 由 1 < n * (b - a) 和 1/n > 0 得證
               exact div_pos one_pos hn_pos  -- 確認 1/n > 0
            _ = b - a := by field_simp  -- (1/n) * n * (b - a) = b - a
      exact hn_gt  -- 而 1 < n * (b - a) 即為 hn_gt
   let m : ℤ := Int.floor (n * a) + 1  -- 定義 m 為大於 n*a 的最小整數：m = ⌊n*a⌋ + 1
   have hm_gt : (n : ℝ) * a < m := by  -- 證明 n * a < m
      calc (n : ℝ) * a  -- 計算鏈
        _ < ↑⌊n * a⌋ + 1 := Int.lt_floor_add_one (n * a)  -- n*a < ⌊n*a⌋ + 1（floor 的性質）
        _ = ↑(⌊n * a⌋ + 1) := by norm_cast  -- 類型轉換：實數加法轉整數加法
        _ = ↑(Int.floor (n * a) + 1) := rfl  -- 即為 m 的定義
   have hm_le : (m : ℝ) ≤ (n : ℝ) * a + 1 := by  -- 證明 m ≤ n*a + 1
      calc (m : ℝ)  -- 計算鏈
        _ = ↑(Int.floor (n * a) + 1) := by rfl  -- m 的定義
        _ = ↑⌊n * a⌋ + 1 := by norm_cast  -- 類型轉換：整數加法轉實數加法
        _ ≤ (n * a) + 1 := by linarith [Int.floor_le (n * a)]  -- 因為 ⌊n*a⌋ ≤ n*a（floor 的性質）
   let q : ℚ := m / n  -- 構造有理數 q = m/n
   have hq_real : (q : ℝ) = (m : ℝ) / (n : ℝ) := by  -- 證明有理數 q 轉實數等於 m/n
      simp only [q, Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]  -- 展開有理數到實數的轉換
   use q  -- 使用 q 作為所求的有理數
   constructor  -- 需要證明 a < q 且 q < b 兩個目標
   -- 證明 a < q
   calc (a : ℝ)  -- 計算鏈證明 a < q（在實數域）
     _ = (n : ℝ) * a / n := by field_simp  -- a = (n*a) / n
     _ < (m : ℝ) / n := by exact div_lt_div_of_pos_right hm_gt hn_pos  -- (n*a)/n < m/n（因為 n*a < m 且 n > 0）
     _ = (q : ℝ) := hq_real.symm  -- m/n = q（在實數域）
   -- 證明 q < b
   calc (q : ℝ)  -- 計算鏈證明 q < b（在實數域）
     _ = (m : ℝ) / n := hq_real  -- q = m/n（在實數域）
     _ ≤ ((n : ℝ) * a + 1) / n := by exact div_le_div_of_nonneg_right hm_le (le_of_lt hn_pos)  -- m/n ≤ (n*a + 1)/n（因為 m ≤ n*a + 1 且 n > 0）
     _ = (n : ℝ) * a / n + 1 / n := by ring  -- (n*a + 1)/n = (n*a)/n + 1/n
     _ = a + 1 / n := by field_simp  -- (n*a)/n + 1/n = a + 1/n
     _ < a + (b - a) := by linarith [h_inv]  -- a + 1/n < a + (b - a)（因為 1/n < b - a）
     _ = (b : ℝ) := by ring  -- a + (b - a) = b

-- Definition 1.19 : Bounded below, infimum, and bounded
-- 定義 1.19：下界、下確界和有界

-- i) Lower bound and bounded below
-- 下界：若 m ≤ a 對所有 a ∈ E 成立，則 m 是 E 的下界
def is_lower_bound (m : ℝ) (E : Set ℝ) : Prop :=
  ∀ a ∈ E, m ≤ a

-- 有下界：存在下界
def bounded_below (E : Set ℝ) : Prop :=
  ∃ m : ℝ, is_lower_bound m E

-- ii) Infimum (greatest lower bound)
-- 下確界：t 是下界，且 t 大於所有其他下界
def is_infimum (t : ℝ) (E : Set ℝ) : Prop :=
  is_lower_bound t E ∧ ∀ m : ℝ, is_lower_bound m E → m ≤ t

-- iii) Bounded (both above and below)
-- 有界：既有上界又有下界
def bounded (E : Set ℝ) : Prop :=
  bounded_above E ∧ bounded_below E

-- Theorem 1.20 : Let E ⊆ ℝ be nonempty.
-- (1) E has a supremum iff -E has an infimum, in which case inf(-E) = -sup(E).
-- 定理 1.20(1)：E 有上確界 ⟺ -E 有下確界，且 inf(-E) = -sup(E)

-- 定義取負的集合：-E = {-x : x ∈ E}
def neg_set (E : Set ℝ) : Set ℝ := {x | -x ∈ E}  -- 注意：x ∈ neg_set E ⟺ -x ∈ E

-- 定理 1.20(1) 包含兩個部分：
-- (a) E 有上確界 ⟺ -E 有下確界（等價性）
-- (b) 若成立，則 inf(-E) = -sup(E)（關係式）
theorem Theorem_1_20_1 (E : Set ℝ):
   ((∃ s, is_supremum s E) ↔ (∃ t, is_infimum t (neg_set E))) ∧  -- 第一部分：等價性
   (∀ s t, is_supremum s E → is_infimum t (neg_set E) → t = -s) := by  -- 第二部分：關係式
   constructor  -- 分解合取（∧）：需要證明兩個部分
   {
      -- 【第一部分】證明等價性：(∃ s, is_supremum s E) ↔ (∃ t, is_infimum t (neg_set E))
      constructor  -- 分解雙向蘊涵（↔）：需要證明 (⇒) 和 (⇐)
      {
         -- 【⇒ 方向】若 E 有上確界 s，則 -E 有下確界 -s
         intro h  -- 假設：h : ∃ s, is_supremum s E
         obtain ⟨s, hs⟩ := h  -- 解構存在性：取出上確界 s 和證據 hs : is_supremum s E
         use -s  -- 聲稱：-s 是 neg_set E 的下確界（需要證明 is_infimum (-s) (neg_set E)）
         constructor  -- 分解 is_infimum 的定義：(1) -s 是下界 ∧ (2) -s 是最大的下界
         {
            -- 【證明 -s 是下界】即證明：∀ x ∈ neg_set E, -s ≤ x
            intro x hx  -- 任取 x ∈ neg_set E（即 -x ∈ E）
            have h1 : -x ≤ s := hs.1 (-x) hx  -- 因為 s 是 E 的上界，所以 -x ≤ s
            linarith  -- 線性算術推理：從 -x ≤ s 得到 -s ≤ x
         }
         {
            -- 【證明 -s 是最大的下界】即證明：∀ m, is_lower_bound m (neg_set E) → m ≤ -s
            intro m hm  -- 任取下界 m（hm : 對所有 x ∈ neg_set E，m ≤ x）
            have h1 : s ≤ -m := by  -- 先證明 s ≤ -m，然後得到 m ≤ -s
               apply hs.2  -- 用上確界的性質：若 -m 是 E 的上界，則 s ≤ -m
               intro a ha  -- 證明 -m 是 E 的上界：任取 a ∈ E，證明 a ≤ -m
               have h2 : m ≤ -a := hm (-a) (by simp [neg_set]; exact ha)  -- 因為 -a ∈ neg_set E 且 m 是下界，所以 m ≤ -a
               linarith  -- 從 m ≤ -a 得到 a ≤ -m
            linarith  -- 從 s ≤ -m 得到 m ≤ -s
         }
      }
      {
         -- 【⇐ 方向】若 -E 有下確界 t，則 E 有上確界 -t
         intro h  -- 假設：h : ∃ t, is_infimum t (neg_set E)
         obtain ⟨t, ht⟩ := h  -- 解構存在性：取出下確界 t 和證據 ht : is_infimum t (neg_set E)
         use -t  -- 聲稱：-t 是 E 的上確界（需要證明 is_supremum (-t) E）
         constructor  -- 分解 is_supremum 的定義：(1) -t 是上界 ∧ (2) -t 是最小的上界
         {
            -- 【證明 -t 是上界】即證明：∀ x ∈ E, x ≤ -t
            intro x hx  -- 任取 x ∈ E
            have h1 : -x ∈ neg_set E := by  -- 先證明 -x ∈ neg_set E
               simp [neg_set]  -- 展開 neg_set 的定義：-x ∈ neg_set E ⟺ -(-x) ∈ E ⟺ x ∈ E
               exact hx  -- 而 hx : x ∈ E
            have h2 : t ≤ -x := ht.1 (-x) h1  -- 因為 t 是 neg_set E 的下界，所以 t ≤ -x
            linarith  -- 從 t ≤ -x 得到 x ≤ -t
         }
         {
            -- 【證明 -t 是最小的上界】即證明：∀ M, is_upper_bound M E → -t ≤ M
            intro m hm  -- 任取上界 m（hm : 對所有 x ∈ E，x ≤ m）
            have h1 : -m ≤ t := by  -- 先證明 -m ≤ t，然後得到 -t ≤ m
               apply ht.2  -- 用下確界的性質：若 -m 是 neg_set E 的下界，則 -m ≤ t
               intro x hx  -- 證明 -m 是 neg_set E 的下界：任取 x ∈ neg_set E，證明 -m ≤ x
               -- hx : x ∈ neg_set E，根據定義就是 -x ∈ E
               have h2 : -x ≤ m := hm (-x) hx  -- 因為 -x ∈ E 且 m 是上界，所以 -x ≤ m
               linarith  -- 從 -x ≤ m 得到 -m ≤ x
            linarith  -- 從 -m ≤ t 得到 -t ≤ m
         }
      }
   }
   {
      -- 【第二部分】證明關係式：若 s 是 E 的上確界，t 是 -E 的下確界，則 t = -s
      intro s t hs ht  -- 引入 s, t 和假設 hs : is_supremum s E, ht : is_infimum t (neg_set E)
      -- 策略：用雙向不等式 t ≤ -s 且 -s ≤ t，然後用 le_antisymm 得到 t = -s
      have h1 : t ≤ -s := by  -- 證明 t ≤ -s
         have h2 : s ≤ -t := by  -- 先證明 s ≤ -t（等價於 t ≤ -s）
            apply hs.2  -- 用上確界的性質：若 -t 是 E 的上界，則 s ≤ -t
            intro a ha  -- 證明 -t 是 E 的上界：任取 a ∈ E，證明 a ≤ -t
            have h3 : t ≤ -a := ht.1 (-a) (by simp [neg_set]; exact ha)  -- 因為 -a ∈ neg_set E 且 t 是下界，所以 t ≤ -a
            linarith  -- 從 t ≤ -a 得到 a ≤ -t
         linarith  -- 從 s ≤ -t 得到 t ≤ -s
      have h2 : -s ≤ t := by  -- 證明 -s ≤ t
         apply ht.2  -- 用下確界的性質：若 -s 是 neg_set E 的下界，則 -s ≤ t
         intro a ha  -- 證明 -s 是 neg_set E 的下界：任取 a ∈ neg_set E，證明 -s ≤ a
         -- ha : a ∈ neg_set E，根據定義就是 -a ∈ E
         have h3 : -a ≤ s := hs.1 (-a) ha  -- 因為 -a ∈ E 且 s 是上界，所以 -a ≤ s
         linarith  -- 從 -a ≤ s 得到 -s ≤ a
      exact le_antisymm h1 h2  -- 由 t ≤ -s 且 -s ≤ t，得到 t = -s（反對稱性）
   }

-- Theorem 1.20(2) : E has a infimum iff -E has a supremum, in which case sup(-E) = -inf(E).
-- 定理 1.20(2)：E 有下確界 ⟺ -E 有上確界，且 sup(-E) = -inf(E)

theorem Theorem_1_20_2 (E : Set ℝ):
   ((∃ t, is_infimum t E) ↔ (∃ s, is_supremum s (neg_set E))) ∧  -- 第一部分：等價性
   (∀ t s, is_infimum t E → is_supremum s (neg_set E) → s = -t) := by  -- 第二部分：關係式
   constructor  -- 分解合取（∧）：需要證明兩個部分
   {
      -- 【第一部分】證明等價性：(∃ t, is_infimum t E) ↔ (∃ s, is_supremum s (neg_set E))
      constructor  -- 分解雙向蘊涵（↔）：需要證明 (⇒) 和 (⇐)
      {
         -- 【⇒ 方向】若 E 有下確界 t，則 -E 有上確界 -t
         intro h  -- 假設：h : ∃ t, is_infimum t E
         obtain ⟨t, ht⟩ := h  -- 解構存在性：取出下確界 t 和證據 ht : is_infimum t E
         use -t  -- 聲稱：-t 是 neg_set E 的上確界（需要證明 is_supremum (-t) (neg_set E)）
         constructor  -- 分解 is_supremum 的定義：(1) -t 是上界 ∧ (2) -t 是最小的上界
         {
            -- 【證明 -t 是上界】即證明：∀ x ∈ neg_set E, x ≤ -t
            intro x hx  -- 任取 x ∈ neg_set E（即 -x ∈ E）
            have h1 : -x ∈ E := hx  -- 根據 neg_set 的定義，x ∈ neg_set E 意味著 -x ∈ E
            have h2 : t ≤ -x := ht.1 (-x) h1  -- 因為 t 是 E 的下界，所以 t ≤ -x
            linarith  -- 線性算術推理：從 t ≤ -x 得到 x ≤ -t
         }
         {
            -- 【證明 -t 是最小的上界】即證明：∀ m, is_upper_bound m (neg_set E) → -t ≤ m
            intro m hm  -- 任取上界 m（hm : 對所有 x ∈ neg_set E，x ≤ m）
            have h1 : -m ≤ t := by  -- 先證明 -m ≤ t，然後得到 -t ≤ m
               apply ht.2  -- 用下確界的性質：若 -m 是 E 的下界，則 -m ≤ t
               intro a ha  -- 證明 -m 是 E 的下界：任取 a ∈ E，證明 -m ≤ a
               have h2 : -a ∈ neg_set E := by simp [neg_set]; exact ha  -- 因為 a ∈ E，所以 -a ∈ neg_set E
               have h3 : -a ≤ m := hm (-a) h2  -- 因為 -a ∈ neg_set E 且 m 是上界，所以 -a ≤ m
               linarith  -- 從 -a ≤ m 得到 -m ≤ a
            linarith  -- 從 -m ≤ t 得到 -t ≤ m
         }
      }
      {
         -- 【⇐ 方向】若 -E 有上確界 s，則 E 有下確界 -s
         intro h  -- 假設：h : ∃ s, is_supremum s (neg_set E)
         obtain ⟨s, hs⟩ := h  -- 解構存在性：取出上確界 s 和證據 hs : is_supremum s (neg_set E)
         use -s  -- 聲稱：-s 是 E 的下確界（需要證明 is_infimum (-s) E）
         constructor  -- 分解 is_infimum 的定義：(1) -s 是下界 ∧ (2) -s 是最大的下界
         {
            -- 【證明 -s 是下界】即證明：∀ x ∈ E, -s ≤ x
            intro x hx  -- 任取 x ∈ E
            have h1 : -x ∈ neg_set E := by simp [neg_set]; exact hx  -- 先證明 -x ∈ neg_set E
            have h2 : -x ≤ s := hs.1 (-x) h1  -- 因為 s 是 neg_set E 的上界，所以 -x ≤ s
            linarith  -- 從 -x ≤ s 得到 -s ≤ x
         }
         {
            -- 【證明 -s 是最大的下界】即證明：∀ m, is_lower_bound m E → m ≤ -s
            intro m hm  -- 任取下界 m（hm : 對所有 x ∈ E，m ≤ x）
            have h1 : -m ≥ s := by  -- 先證明 -m ≥ s（即 s ≤ -m），然後得到 m ≤ -s
               apply hs.2  -- 用上確界的性質：若 -m 是 neg_set E 的上界，則 s ≤ -m
               intro y hy  -- 證明 -m 是 neg_set E 的上界：任取 y ∈ neg_set E，證明 y ≤ -m
               have h2 : -y ∈ E := hy  -- hy : y ∈ neg_set E，根據定義就是 -y ∈ E
               have h3 : m ≤ -y := hm (-y) h2  -- 因為 -y ∈ E 且 m 是下界，所以 m ≤ -y
               linarith  -- 從 m ≤ -y 得到 y ≤ -m
            linarith  -- 從 s ≤ -m 得到 m ≤ -s
         }
      }
   }
   {
      -- 【第二部分】證明關係式：若 t 是 E 的下確界，s 是 -E 的上確界，則 s = -t
      intro t s ht hs  -- 引入 t, s 和假設 ht : is_infimum t E, hs : is_supremum s (neg_set E)
      -- 策略：用雙向不等式 s ≤ -t 且 -t ≤ s，然後用 le_antisymm 得到 s = -t
      have h1 : s ≤ -t := by  -- 證明 s ≤ -t
         apply hs.2  -- 用上確界的性質：若 -t 是 neg_set E 的上界，則 s ≤ -t
         intro x hx  -- 證明 -t 是 neg_set E 的上界：任取 x ∈ neg_set E，證明 x ≤ -t
         have h2 : -x ∈ E := hx  -- hx : x ∈ neg_set E，根據定義就是 -x ∈ E
         have h3 : t ≤ -x := ht.1 (-x) h2  -- 因為 t 是 E 的下界，所以 t ≤ -x
         linarith  -- 從 t ≤ -x 得到 x ≤ -t
      have h2 : -t ≤ s := by  -- 證明 -t ≤ s
         have h3 : -s ≤ t := by  -- 先證明 -s ≤ t（等價於 -t ≤ s）
            apply ht.2  -- 用下確界的性質：若 -s 是 E 的下界，則 -s ≤ t
            intro a ha  -- 證明 -s 是 E 的下界：任取 a ∈ E，證明 -s ≤ a
            have h4 : -a ∈ neg_set E := by simp [neg_set]; exact ha  -- 因為 a ∈ E，所以 -a ∈ neg_set E
            have h5 : -a ≤ s := hs.1 (-a) h4  -- 因為 -a ∈ neg_set E 且 s 是上界，所以 -a ≤ s
            linarith  -- 從 -a ≤ s 得到 -s ≤ a
         linarith  -- 從 -s ≤ t 得到 -t ≤ s
      exact le_antisymm h1 h2  -- 由 s ≤ -t 且 -t ≤ s，得到 s = -t（反對稱性）
   }

-- Theorem 1.21 : Suppoes that A ⊆ B are nonempty subsets of ℝ.
-- (1) If B has a supremum, then sup(A) ≤ sup(B)
-- 定理 1.21(1)：若 A ⊆ B，則 sup(A) ≤ sup(B)
theorem Theorem_1_21_1 (A B : Set ℝ) (hA_sub_B : A ⊆ B) :
   ∀ s t, is_supremum s B → is_supremum t A → t ≤ s := by  -- 若 s = sup B，t = sup A，則 t ≤ s
   intro s t hs ht  -- 引入上確界 s, t 和假設 hs : is_supremum s B, ht : is_supremum t A
   -- 【策略】用 t 的最小性：只需證明 s 是 A 的上界
   apply ht.2  -- 用上確界 t 的最小性：若 s 是 A 的上界，則 t ≤ s
   -- 【證明 s 是 A 的上界】即證明：∀ a ∈ A, a ≤ s
   intro a ha  -- 任取 a ∈ A
   have ha_in_B : a ∈ B := hA_sub_B ha  -- 因為 A ⊆ B 且 a ∈ A，所以 a ∈ B
   exact hs.1 a ha_in_B  -- 因為 s 是 B 的上界且 a ∈ B，所以 a ≤ s（用 hs.1：上界性質）

-- (2) If B has a infimum, then inf(A) ≥ inf(B)
-- 定理 1.21(2)：若 A ⊆ B，則 inf(B) ≤ inf(A)（注意方向與上確界相反）
theorem Theorem_1_21_2 (A B : Set ℝ) (hA_sub_B : A ⊆ B) :
   ∀ t s, is_infimum s B → is_infimum t A → s ≤ t := by  -- 若 s = inf B，t = inf A，則 s ≤ t
   intro t s ht hs  -- 引入下確界 t, s 和假設 ht : is_infimum s B, hs : is_infimum t A
   -- 【策略】用 t 的最大性：只需證明 s 是 A 的下界
   apply hs.2  -- 用下確界 t 的最大性：若 s 是 A 的下界，則 s ≤ t（hs 對應 is_infimum t A）
   -- 【證明 s 是 A 的下界】即證明：∀ a ∈ A, s ≤ a
   intro a ha  -- 任取 a ∈ A
   have ha_in_B : a ∈ B := hA_sub_B ha  -- 因為 A ⊆ B 且 a ∈ A，所以 a ∈ B
   exact ht.1 a ha_in_B  -- 因為 s 是 B 的下界且 a ∈ B，所以 s ≤ a（用 ht.1：下界性質）

/-
## 1.38 Definition：有限集合與可數集合

定義 1.38（Wade）：設 E 為集合。

i) E 稱為 **finite**（有限）：
   當且僅當 E = ∅ 或存在 1-1 函數從 {1, 2, ..., n} 到 E（對某個 n ∈ ℕ）

ii) E 稱為 **countable**（可數）：
   當且僅當存在 1-1 函數從 ℕ 到 E

iii) E 稱為 **at most countable**（至多可數）：
   當且僅當 E 是有限的或可數的

iv) E 稱為 **uncountable**（不可數）：
   當且僅當 E 既非有限也非可數

### 重要例子

**有限集合**：
- {1, 2, 3}
- 任何 n 個元素的集合

**可數集合（可數無窮）**：
- ℕ（自然數）
- ℤ（整數）
- ℚ（有理數）← 令人驚訝！

**不可數集合**：
- ℝ（實數）← Cantor 對角線論證
- [0, 1]（閉區間）
- (0, 1)（開區間）

### 注意事項

在 Lean 的 Mathlib 中，這些概念有內建定義，但具體的 API 可能因版本而異。
本教材主要關注數學概念的理解，具體的形式化證明可以參考最新的 Mathlib 文檔。

關鍵定理（留待後續證明）：
1. 有理數 ℚ 是可數的（Cantor 對角線排列）
2. 實數 ℝ 是不可數的（Cantor 對角線論證）
3. 可數多個可數集合的並集仍是可數的
-/

-- 1.39 Remark. [CANTOR'S DIAGONALIZATION ARGUMENT]
-- The open interval (0, 1) is uncountable.
-- 備註：完整的形式化證明需要實數的十進制表示理論，
-- 這超出了本課程的範圍。我們將此定理作為公理。

axiom Cantor_Diagonalization : ¬∃ f : ℕ → Set.Ioo (0 : ℝ) 1, Function.Surjective f

/-
## 2.7 Definition：數列的有界性

設 {xₙ} 為實數數列（即函數 x : ℕ → ℝ）。
-/

-- i) 數列上方有界（bounded above）
def seq_bounded_above (x : ℕ → ℝ) : Prop :=
  bounded_above (Set.range x)

-- ii) 數列下方有界（bounded below）
def seq_bounded_below (x : ℕ → ℝ) : Prop :=
  bounded_below (Set.range x)

-- iii) 數列有界（bounded）
def seq_bounded (x : ℕ → ℝ) : Prop :=
  bounded (Set.range x)

-- 等價形式：數列有界 ⟺ 既上方有界又下方有界
theorem seq_bounded_iff (x : ℕ → ℝ) :
    seq_bounded x ↔ seq_bounded_above x ∧ seq_bounded_below x := by
  unfold seq_bounded seq_bounded_above seq_bounded_below bounded
  rfl

-- 2.1 Definition：收斂（ε–N 定義）
def converge_to (x : ℕ → ℝ) (a : ℝ) : Prop :=  -- xₙ → a
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N → |x n - a| < ε  -- ∀ ε > 0, ∃ N, n ≥ N ⇒ |xₙ - a| < ε

-- 輔助引理：有限集合有上界（用 max' 取最大值）
lemma finite_set_has_upper_bound (s : Finset ℝ) (hs : s.Nonempty) :  -- s 非空
    ∃ M, ∀ x ∈ s, x ≤ M := by  -- 存在 M 使得 ∀ x ∈ s, x ≤ M
  use s.max' hs  -- 取 M = s 的最大元素
  intro x hx  -- 任取 x ∈ s
  exact Finset.le_max' s x hx  -- 由 max' 的性質得 x ≤ max'

-- Theorem 2.8 : Every convergent sequence is bounded.
theorem Theorem_2_8 (x : ℕ → ℝ) (a : ℝ) (h : converge_to x a) : seq_bounded x := by
   unfold seq_bounded bounded bounded_above bounded_below  -- 展開數列有界與集合有界的定義
   constructor  -- 分成上方有界與下方有界兩部分
   {
      -- 【上方有界】證明 bounded_above (Set.range x)
      obtain ⟨N, hN⟩ := h 1 (by norm_num : (0 : ℝ) < 1)  -- 取 ε = 1 得到尾部估計：n ≥ N ⇒ |x n - a| < 1

      have h_tail : ∀ n ≥ N, x n ≤ a + 1 := by  -- 尾部上界：n ≥ N ⇒ x n ≤ a + 1
        intro n hn  -- 任取 n ≥ N
        have h_conv : |x n - a| < 1 := hN n hn  -- 由收斂性得到 |x n - a| < 1
        have h_parts := abs_sub_lt_iff.mp h_conv  -- 轉成 (x n - a < 1) ∧ (a - x n < 1)
        linarith  -- 從不等式推出 x n ≤ a + 1

      by_cases h_case : N = 0  -- 分情況：N = 0 或 N > 0
      · use a + 1  -- 若 N = 0，整個序列都在尾部，直接取上界 a + 1
        intro y hy  -- 任取 y ∈ range x
        obtain ⟨n, rfl⟩ := hy  -- 由 range 的定義，y = x n
        have : n ≥ N := by  -- 需要餵給 h_tail 的條件 n ≥ N
          simp [h_case]  -- N = 0 時等價於 n ≥ 0
        exact h_tail n this  -- 由尾部上界得到 x n ≤ a + 1
      · let head_set := Finset.image x (Finset.range N)  -- 頭部有限集合：{x 0, x 1, ..., x (N-1)}

        have h_nonempty : head_set.Nonempty := by  -- 證明頭部集合非空（因為 N > 0）
          use x 0  -- 見證元素 x 0
          simp [head_set]  -- 展開 image / range 的會員條件
          use 0  -- 令 index = 0
          constructor
          · exact Nat.pos_of_ne_zero h_case  -- N ≠ 0 ⇒ 0 < N，所以 0 ∈ range N
          · rfl  -- x 0 = x 0

        obtain ⟨M_head, hM_head⟩ := finite_set_has_upper_bound head_set h_nonempty  -- 取頭部上界 M_head

        use max (a + 1) M_head  -- 整體上界取 max(尾部上界, 頭部上界)

        intro y hy  -- 任取 y ∈ range x
        obtain ⟨n, rfl⟩ := hy  -- 由 range 的定義，y = x n

        rcases lt_or_ge n N with hn | hn  -- 分情況：n < N（頭部）或 n ≥ N（尾部）
        · have h_in : x n ∈ head_set := by  -- 先證明 x n ∈ 頭部集合
            simp [head_set]  -- 展開 image / range
            refine ⟨n, hn, rfl⟩  -- 提供見證 n，並給出 n < N 與 x n = x n
          -- 頭部：x n ≤ M_head ≤ max (a+1) M_head
          exact le_trans (hM_head (x n) h_in) (le_max_right (a + 1) M_head)
        · -- 尾部：x n ≤ a+1 ≤ max (a+1) M_head
          exact le_trans (h_tail n hn) (le_max_left (a + 1) M_head)
   }
   {
      -- 【下方有界】證明 bounded_below (Set.range x)（與上方有界完全對稱）
      obtain ⟨N, hN⟩ := h 1 (by norm_num : (0 : ℝ) < 1)  -- 同樣取 ε = 1

      have h_tail : ∀ n ≥ N, a - 1 ≤ x n := by  -- 尾部下界：n ≥ N ⇒ a - 1 ≤ x n
        intro n hn  -- 任取 n ≥ N
        have h_conv : |x n - a| < 1 := hN n hn  -- |x n - a| < 1
        have h_parts := abs_sub_lt_iff.mp h_conv  -- (x n - a < 1) ∧ (a - x n < 1)
        linarith  -- 推出 a - 1 ≤ x n

      by_cases h_case : N = 0  -- 分情況：N = 0 或 N > 0
      · use a - 1  -- 若 N = 0，整個序列都在尾部，直接取下界 a - 1
        intro y hy  -- 任取 y ∈ range x
        obtain ⟨n, rfl⟩ := hy  -- y = x n
        have : n ≥ N := by  -- n ≥ 0
          simp [h_case]
        exact h_tail n this  -- 得到 a - 1 ≤ x n
      · let head_set := Finset.image x (Finset.range N)  -- 頭部有限集合

        have h_nonempty : head_set.Nonempty := by  -- 頭部非空（N > 0）
          use x 0
          simp [head_set]
          use 0
          constructor
          · exact Nat.pos_of_ne_zero h_case
          · rfl

        have h_has_min : ∃ m, ∀ x_val ∈ head_set, m ≤ x_val := by  -- 頭部有下界（用 min'）
          use head_set.min' h_nonempty  -- 取 m = 最小元素
          intro x_val hx  -- 任取 x_val ∈ head_set
          exact Finset.min'_le head_set x_val hx  -- min' ≤ x_val

        obtain ⟨m_head, hm_head⟩ := h_has_min  -- 取頭部下界 m_head

        use min (a - 1) m_head  -- 整體下界取 min(尾部下界, 頭部下界)

        intro y hy  -- 任取 y ∈ range x
        obtain ⟨n, rfl⟩ := hy  -- y = x n

        rcases lt_or_ge n N with hn | hn  -- n < N（頭部）或 n ≥ N（尾部）
        · have h_in : x n ∈ head_set := by  -- x n ∈ 頭部
            simp [head_set]
            refine ⟨n, hn, rfl⟩
          -- 頭部：min (a-1) m_head ≤ m_head ≤ x n
          exact le_trans (min_le_right (a - 1) m_head) (hm_head (x n) h_in)
        · -- 尾部：min (a-1) m_head ≤ a-1 ≤ x n
          exact le_trans (min_le_left (a - 1) m_head) (h_tail n hn)
   }

-- Theorem 2.9 [Squeeze Theorem] : Suppose that {x_n}, {y_n}, and {w_n} are real sequences.
-- (i) If x_n → a and y_n → a (the same a) as n → ∞, and if there is an N₀ ∈ ℕ such that
-- x_n ≤ w_n ≤ y_n for n ≥ Nₒ, then w_n → a as n → ∞.
theorem Theorem_2_9_i (x y w : ℕ → ℝ) (a : ℝ)
   (hx : converge_to x a) (hy : converge_to y a)  -- 假設：xₙ → a 且 yₙ → a
   (hxy : ∃ N₀ : ℕ, ∀ (n : ℕ), n ≥ N₀ → x n ≤ w n ∧ w n ≤ y n) :  -- 假設：存在 N₀，使得 n ≥ N₀ 時 xₙ ≤ wₙ ≤ yₙ
   converge_to w a := by  -- 目標：wₙ → a
   unfold converge_to  -- 展開收斂定義：∀ ε > 0, ∃ N, ∀ n ≥ N, |w n - a| < ε
   intro ε hε  -- 任取 ε > 0
   obtain ⟨Nx, hNx⟩ := hx ε hε  -- 由 xₙ → a 得到 Nx：n ≥ Nx ⇒ |x n - a| < ε
   obtain ⟨Ny, hNy⟩ := hy ε hε  -- 由 yₙ → a 得到 Ny：n ≥ Ny ⇒ |y n - a| < ε
   obtain ⟨N₀, hN₀⟩ := hxy  -- 由夾擠條件取出 N₀：n ≥ N₀ ⇒ x n ≤ w n ∧ w n ≤ y n
   refine ⟨max (max Nx Ny) N₀, ?_⟩  -- 取 N = max(max Nx Ny) N₀，同時滿足三個門檻
   intro n hn  -- 任取 n ≥ N
   have hn_max : n ≥ max Nx Ny := le_trans (le_max_left _ _) hn  -- 由 n ≥ max(max Nx Ny) N₀ 得 n ≥ max Nx Ny
   have hnNx : n ≥ Nx := le_trans (le_max_left _ _) hn_max  -- 由 n ≥ max Nx Ny 得 n ≥ Nx
   have hnNy : n ≥ Ny := le_trans (le_max_right _ _) hn_max  -- 由 n ≥ max Nx Ny 得 n ≥ Ny
   have hnN₀ : n ≥ N₀ := le_trans (le_max_right _ _) hn  -- 由 n ≥ max(max Nx Ny) N₀ 得 n ≥ N₀
   have hw : x n ≤ w n ∧ w n ≤ y n := hN₀ n hnN₀  -- 由夾擠條件得到 x n ≤ w n 且 w n ≤ y n
   apply (abs_sub_lt_iff).2  -- 將 |w n - a| < ε 改寫成 (w n - a < ε) ∧ (a - w n < ε)
   constructor  -- 分成兩個不等式：w n - a < ε 與 a - w n < ε
   {
      -- 【第一個目標】證明 w n - a < ε（用 w n ≤ y n 與 y n → a）
      have hy_abs : |y n - a| < ε := hNy n hnNy  -- 由 n ≥ Ny 得 |y n - a| < ε
      have hy_lt : y n - a < ε := (abs_sub_lt_iff.mp hy_abs).1  -- 由 |y n - a| < ε 取出 y n - a < ε
      have hw_le : w n - a ≤ y n - a := sub_le_sub_right hw.2 a  -- 由 w n ≤ y n 推出 w n - a ≤ y n - a
      exact lt_of_le_of_lt hw_le hy_lt  -- 串接：w n - a ≤ y n - a < ε
   }
   {
      -- 【第二個目標】證明 a - w n < ε（用 x n ≤ w n 與 x n → a）
      have hx_abs : |x n - a| < ε := hNx n hnNx  -- 由 n ≥ Nx 得 |x n - a| < ε
      have hx_lt : a - x n < ε := (abs_sub_lt_iff.mp hx_abs).2  -- 由 |x n - a| < ε 取出 a - x n < ε
      have hw_ge : a - w n ≤ a - x n := sub_le_sub_left hw.1 a  -- 由 x n ≤ w n 推出 a - w n ≤ a - x n
      exact lt_of_le_of_lt hw_ge hx_lt  -- 串接：a - w n ≤ a - x n < ε
   }

-- (ii) If x_n → 0 as n → ∞ and {y_n} is bounded, then x_n y_n → 0 as n → ∞.
theorem Theorem_2_9_ii (x y : ℕ → ℝ) (h : converge_to x 0) (hy : seq_bounded y) :
   converge_to (fun n => x n * y n) 0 := by  -- 目標：xₙ → 0 且 y 有界 ⇒ (xₙ*yₙ) → 0
      unfold converge_to  -- 展開收斂定義
      intro ε hε  -- 任取 ε > 0
      have hy' : bounded (Set.range y) := by
         -- seq_bounded y 的定義就是 bounded (Set.range y)
         simpa [seq_bounded] using hy
      have hy_above : bounded_above (Set.range y) := hy'.1  -- y 的值域有上界
      have hy_below : bounded_below (Set.range y) := hy'.2  -- y 的值域有下界
      obtain ⟨U, hU⟩ := hy_above  -- 取上界 U：∀ z ∈ range y, z ≤ U
      obtain ⟨L, hL⟩ := hy_below  -- 取下界 L：∀ z ∈ range y, L ≤ z
      -- 定義 B，並證明 ∀ n, |y n| ≤ B
      let B : ℝ := max |L| |U|  -- 取 B = max(|L|,|U|)，用來控制 |y n|
      have hB0 : 0 ≤ B := by
         have : 0 ≤ |L| := abs_nonneg L
         exact le_trans this (le_max_left _ _)
      have h_abs_y : ∀ n : ℕ, |y n| ≤ B := by
         intro n
         have hyU : y n ≤ U := hU (y n) ⟨n, rfl⟩  -- 由上界性質得 y n ≤ U
         have hyL : L ≤ y n := hL (y n) ⟨n, rfl⟩  -- 由下界性質得 L ≤ y n
         have hy_le_B : y n ≤ B := by
            have : y n ≤ |U| := le_trans hyU (le_abs_self U)
            exact le_trans this (le_max_right _ _)
         have hnegB_le_y : -B ≤ y n := by
            have : - |L| ≤ L := neg_abs_le L
            have h1: - |L| ≤ y n := le_trans this hyL
            have h2: - B ≤ - |L| := by
               have : |L| ≤ B := le_max_left _ _
               exact neg_le_neg this
            exact le_trans h2 h1
         have : -B ≤ y n ∧ y n ≤ B := ⟨hnegB_le_y, hy_le_B⟩
         exact (abs_le).2 this  -- 由 -B ≤ y n ≤ B 得 |y n| ≤ B
      have hB1_pos : 0 < B + 1 := by linarith [hB0]  -- B ≥ 0 ⇒ B+1 > 0
      obtain ⟨N, hN⟩ := h (ε / (B + 1)) (by exact div_pos hε hB1_pos)  -- 用 ε/(B+1) 套用 xₙ → 0，得到 N
      refine ⟨N, ?_⟩  -- 取這個 N 作為收斂到 0 的門檻
      intro n hn  -- 任取 n ≥ N
      have hx_small : |x n| < ε / (B + 1) := by
         simpa [sub_zero] using hN n hn  -- 由 |x n - 0| < ε/(B+1) 得 |x n| < ε/(B+1)
      have hy_bd : |y n| ≤ B := h_abs_y n  -- 由有界性得 |y n| ≤ B
      -- 目標：|x n * y n - 0| < ε
      have h_mul_abs : |x n * y n| < ε := by
         have hmul : |x n * y n| = |x n| * |y n| := by
            simp [abs_mul]
         have h1 : |x n| * |y n| ≤ |x n| * B :=
            mul_le_mul_of_nonneg_left hy_bd (abs_nonneg (x n))
         have hB_le : B ≤ B + 1 := by linarith
         have h2 : |x n| * B ≤ |x n| * (B + 1) :=
            mul_le_mul_of_nonneg_left hB_le (abs_nonneg (x n))
         have hne : (B + 1) ≠ 0 := ne_of_gt hB1_pos
         have hx_mul : |x n| * (B + 1) < ε := by
            have htmp := (mul_lt_mul_of_pos_right hx_small hB1_pos)
            -- 右邊化簡：(ε/(B+1))*(B+1) = ε
            have hR : (ε / (B + 1)) * (B + 1) = ε := by
               field_simp [hne]
            simpa [hR] using htmp
         -- 串接 ≤ ≤ < 得 <
         have : |x n| * |y n| < ε := lt_of_le_of_lt (le_trans h1 h2) hx_mul
         -- 回到 |x n * y n|
         simpa [hmul] using this
      simpa [sub_zero] using h_mul_abs  -- |x n * y n - 0| = |x n * y n|

-- Theorem 2.12 : Suppose that {x_n} and {y_n} are real sequences and that α ∈ ℝ. If {x_n} and {y_n} are convergent.
-- (i) lim_{n → ∞} (x_n + y_n) = lim_{n → ∞} x_n + lim_{n → ∞} y_n
theorem Theorem_2_12_i (x y : ℕ → ℝ) (a b : ℝ)
   (hx : converge_to x a) (hy : converge_to y b) :  -- 假設：xₙ → a 且 yₙ → b
   converge_to (fun n => x n + y n) (a + b) := by  -- 目標：(xₙ + yₙ) → (a + b)
   unfold converge_to  -- 展開收斂定義：∀ ε > 0, ∃ N, ∀ n ≥ N, |(x n + y n) - (a + b)| < ε
   intro ε hε  -- 任取 ε > 0
   have hε2 : ε / 2 > 0 := by  -- 證明 ε/2 > 0（方便套用 hx, hy）
      have : (0 : ℝ) < 2 := by norm_num  -- 2 > 0
      exact div_pos hε this  -- ε>0 且 2>0 ⇒ ε/2>0
   obtain ⟨Nx, hNx⟩ := hx (ε / 2) hε2  -- 對 xₙ → a 套用 ε/2，得到 Nx：n ≥ Nx ⇒ |x n - a| < ε/2
   obtain ⟨Ny, hNy⟩ := hy (ε / 2) hε2  -- 對 yₙ → b 套用 ε/2，得到 Ny：n ≥ Ny ⇒ |y n - b| < ε/2
   refine ⟨max Nx Ny, ?_⟩  -- 取 N = max Nx Ny，使得同時滿足 n ≥ Nx 與 n ≥ Ny
   intro n hn  -- 任取 n ≥ N
   have hnNx : n ≥ Nx := le_trans (le_max_left _ _) hn  -- 由 n ≥ max Nx Ny 推出 n ≥ Nx
   have hnNy : n ≥ Ny := le_trans (le_max_right _ _) hn  -- 由 n ≥ max Nx Ny 推出 n ≥ Ny
   have hxε : |x n - a| < ε / 2 := hNx n hnNx  -- 得到 |x n - a| < ε/2
   have hyε : |y n - b| < ε / 2 := hNy n hnNy  -- 得到 |y n - b| < ε/2
   have htriangle :
      |(x n + y n) - (a + b)| ≤ |x n - a| + |y n - b| := by  -- 三角不等式型態
      have : (x n + y n) - (a + b) = (x n - a) + (y n - b) := by ring  -- 代數改寫成 (x n - a) + (y n - b)
      simpa [this] using abs_add_le (x n - a) (y n - b)  -- 用 |u+v| ≤ |u|+|v|
   have hsum :
      |x n - a| + |y n - b| < ε := by  -- 兩個 ε/2 估計相加得到 < ε
      have : |x n - a| + |y n - b| < ε / 2 + ε / 2 := add_lt_add hxε hyε  -- 分別加起來
      simpa [add_halves] using this  -- ε/2 + ε/2 = ε
   exact lt_of_le_of_lt htriangle hsum  -- 夾擠：|(x+y)-(a+b)| ≤ ... < ε

-- (ii) lim_{n → ∞} (α * x_n) = α lim_{n → ∞} x_ n
theorem Theorem_2_12_ii (x : ℕ → ℝ) (α : ℝ) (a : ℝ) (hx : converge_to x a) :  -- 假設：xₙ → a
   converge_to (fun n => α * x n) (α * a) := by  -- 目標：(α*xₙ) → (α*a)
   unfold converge_to  -- 展開收斂定義
   intro ε hε  -- 任取 ε > 0
   by_cases hα : α = 0  -- 分情況：α = 0 或 α ≠ 0
   {
      subst hα  -- 用 α = 0 改寫所有目標
      refine ⟨0, ?_⟩  -- 任何 N 都可，取 N = 0
      intro n hn  -- 任取 n ≥ 0
      simpa using hε  -- 目標化簡成 0 < ε，正好是 hε
   }
   {
      have hαpos : 0 < |α| := abs_pos.mpr hα  -- α ≠ 0 ⇒ |α| > 0
      obtain ⟨N, hN⟩ := hx (ε / |α|) (by exact div_pos hε hαpos)  -- 對 ε/|α| 套用 xₙ → a，得到 N
      refine ⟨N, ?_⟩  -- 取這個 N
      intro n hn  -- 任取 n ≥ N
      have hxδ : |x n - a| < ε / |α| := hN n hn  -- 得到 |x n - a| < ε/|α|
      have hαne : |α| ≠ 0 := ne_of_gt hαpos  -- |α| ≠ 0（供除法化簡）
      have habs_mul : |α * (x n - a)| < ε := by  -- 證明 |α*(x n - a)| < ε
         have hmul : |α| * |x n - a| < |α| * (ε / |α|) :=  -- 兩邊同乘 |α|（正數）
            mul_lt_mul_of_pos_left hxδ hαpos
         have hR : |α| * (ε / |α|) = ε := by  -- 化簡 |α|*(ε/|α|) = ε
            calc
              |α| * (ε / |α|) = (ε / |α|) * |α| := by simp [mul_comm]
              _ = (ε * |α|) / |α| := by simp [div_mul_eq_mul_div]
              _ = ε := by simpa using (mul_div_cancel_right₀ ε hαne)
         have habs : |α * (x n - a)| = |α| * |x n - a| := abs_mul α (x n - a)  -- |α*(x n-a)| = |α|*|x n-a|
         have : |α * (x n - a)| < |α| * (ε / |α|) := lt_of_eq_of_lt habs hmul  -- 把左邊改寫成 |α*(x n-a)|
         simpa [hR] using this  -- 再把右邊改成 ε
      have hrewrite : α * x n - α * a = α * (x n - a) := by ring  -- 代數改寫：α*x n - α*a = α*(x n-a)
      -- 目標是 |α*x n - α*a| < ε，改寫後用 habs_mul
      simpa [hrewrite] using habs_mul
   }

-- (iii) lim_{n → ∞} (x_n * y_n) = lim_{n → ∞} x_n * lim_{n → ∞} y_n
theorem Theorem_2_12_iii (x y : ℕ → ℝ) (a b : ℝ) (hx : converge_to x a) (hy : converge_to y b) :  -- 假設：xₙ → a 且 yₙ → b
   converge_to (fun n => x n * y n) (a * b) := by  -- 目標：xₙyₙ → ab
   -- 【策略】代數分解：xₙyₙ - ab = xₙ(yₙ - b) + b(xₙ - a)，再證右邊兩項都 → 0，最後用加法極限定理合併
   unfold converge_to  -- 展開收斂定義：∀ ε > 0, ∃ N, ∀ n ≥ N, |x n * y n - a*b| < ε
   intro ε hε  -- 任取 ε > 0
   have hx_bd : seq_bounded x := Theorem_2_8 x a hx  -- 由定理 2.8：收斂 ⇒ 有界，得到 x 有界
   have hy0 : converge_to (fun n => y n - b) 0 := by  -- 證明 (yₙ - b) → 0
      unfold converge_to
      intro δ hδ  -- 任取 δ > 0
      obtain ⟨N, hN⟩ := hy δ hδ  -- 由 yₙ → b 得 n ≥ N ⇒ |y n - b| < δ
      refine ⟨N, ?_⟩
      intro n hn
      -- |(y n - b) - 0| = |y n - b|
      simpa [sub_eq_add_neg, sub_zero, sub_sub] using hN n hn
   have hprod1' : converge_to (fun n => (y n - b) * x n) 0 :=  -- 由 2.9(ii)：(y-b)→0 且 x 有界 ⇒ (y-b)*x → 0
      Theorem_2_9_ii (fun n => y n - b) x hy0 hx_bd
   have hprod1 : converge_to (fun n => x n * (y n - b)) 0 := by  -- 換回 x*(y-b) 的形式（乘法交換）
      simpa [mul_comm] using hprod1'
   have hx0 : converge_to (fun n => x n - a) 0 := by  -- 證明 (xₙ - a) → 0
      unfold converge_to
      intro δ hδ
      obtain ⟨N, hN⟩ := hx δ hδ  -- 由 xₙ → a 得 n ≥ N ⇒ |x n - a| < δ
      refine ⟨N, ?_⟩
      intro n hn
      simpa [sub_zero] using hN n hn  -- |(x n - a) - 0| = |x n - a|
   have hprod2 : converge_to (fun n => b * (x n - a)) 0 := by  -- 用 2.12(ii)：常數倍保持收斂到 0
      simpa using (Theorem_2_12_ii (fun n => x n - a) b 0 hx0)
   have hsum0 : converge_to (fun n => x n * (y n - b) + b * (x n - a)) (0 + 0) :=  -- 用 2.12(i)：兩個 →0 的和仍 →0
      Theorem_2_12_i (fun n => x n * (y n - b)) (fun n => b * (x n - a)) 0 0 hprod1 hprod2
   have hsum0' : converge_to (fun n => x n * (y n - b) + b * (x n - a)) 0 := by  -- 0+0 = 0
      simpa using hsum0
   have hwrite : ∀ n, x n * y n - a * b = x n * (y n - b) + b * (x n - a) := by  -- 代數恆等式（每一項）
      intro n
      ring
   obtain ⟨N, hN⟩ := hsum0' ε hε  -- 對 ε 套用 hsum0'，得到存在 N 使得尾部 |...-0|<ε
   refine ⟨N, ?_⟩
   intro n hn  -- 任取 n ≥ N
   have hsmall : |x n * (y n - b) + b * (x n - a)| < ε := by  -- 從 |(...) - 0| < ε 化簡成 |...| < ε
      simpa [sub_zero] using hN n hn
   have hrew : x n * y n - a * b = x n * (y n - b) + b * (x n - a) := hwrite n  -- 取出第 n 項的改寫
   simpa [hrew] using hsmall  -- 用改寫把目標 |x n * y n - a * b| < ε 化成 hsmall

-- (iv) If, in addition, yₙ ≠ 0 and lim_{n → ∞} yₙ ≠ 0,
-- then lim_{n → ∞} x_n/y_n = lim_{n → ∞} x_n / lim_{n → ∞} y_n
theorem Theorem_2_12_iv (x y : ℕ → ℝ) (a b : ℝ)  -- 除法極限：xₙ/yₙ → a/b（分母極限非零）
   (hx : converge_to x a) (hy : converge_to y b)
   (hy_ne : ∀ n : ℕ, y n ≠ 0)(hb : b ≠ 0) :
   converge_to (fun n => x n / y n) (a / b) := by
   have hdiv : (fun n => x n / y n) = (fun n => x n * (y n)⁻¹) := by  -- 將除法改寫成乘以倒數
      funext n
      simp [div_eq_mul_inv]
   have hy_inv : converge_to (fun n => (y n)⁻¹) (b⁻¹) := by  -- 先證倒數收斂
      unfold converge_to
      intro ε hε
      have hbpos : 0 < |b| := abs_pos.mpr hb  -- b ≠ 0 ⇒ |b| > 0
      let δ : ℝ := min (|b| / 2) (ε * |b| * |b| / 2)  -- 兼顧遠離 0 與最終誤差的 δ
      have hδpos : 0 < δ := by  -- δ > 0
         have hb2 : 0 < |b| / 2 := by
            have : (0 : ℝ) < 2 := by norm_num
            exact div_pos hbpos this
         have hδ2 : 0 < ε * |b| * |b| / 2 := by
            have : (0 : ℝ) < 2 := by norm_num
            have h1 : 0 < ε * |b| := mul_pos hε hbpos
            have h2 : 0 < ε * |b| * |b| := mul_pos h1 hbpos
            exact div_pos h2 this
         exact lt_min hb2 hδ2
      obtain ⟨N, hN⟩ := hy δ hδpos  -- 由 yₙ → b 取得門檻 N
      refine ⟨N, ?_⟩
      intro n hn
      have hyb : |y n - b| < δ := hN n hn  -- |yₙ - b| < δ
      have hδ_le : δ ≤ |b| / 2 := by  -- δ ≤ |b|/2
         -- 用 simp 直接化簡 min 的左右界
         simpa [δ] using min_le_left (|b| / 2) (ε * |b| * |b| / 2)
      have hyb1 : |y n - b| < |b| / 2 := lt_of_lt_of_le hyb hδ_le  -- 進一步約束
      have hδ_le2 : δ ≤ ε * |b| * |b| / 2 := by  -- δ ≤ ε|b|²/2
         simpa [δ] using min_le_right (|b| / 2) (ε * |b| * |b| / 2)
      have hyb2 : |y n - b| < ε * |b| * |b| / 2 := lt_of_lt_of_le hyb hδ_le2  -- 分子控制

      -- 證明 |y n| ≥ |b|/2（用三角不等式）
      have hb_le : |b| ≤ |y n| + |b - y n| := by
         have : |b| = |y n + (b - y n)| := by ring
         simpa [this] using abs_add_le (y n) (b - y n)
      have hby : |b - y n| = |y n - b| := by simp [abs_sub_comm]
      have hy_abs_lb : |b| / 2 ≤ |y n| := by
         have : |b| ≤ |y n| + |y n - b| := by simpa [hby] using hb_le
         linarith
      have hypos : 0 < |y n| := lt_of_lt_of_le (by linarith [hbpos]) hy_abs_lb  -- |y n| > 0，保證可除

      -- 證明 |(y n)⁻¹ - b⁻¹| = |y n - b| / (|y n| * |b|)
      have hdiff : (y n)⁻¹ - b⁻¹ = (b - y n) / (y n * b) := by
         field_simp [hy_ne n, hb]
      have habs1 : |(y n)⁻¹ - b⁻¹| = |b - y n| / |y n * b| := by
         calc
           |(y n)⁻¹ - b⁻¹| = |(b - y n) / (y n * b)| := by simp [hdiff]
           _ = |b - y n| / |y n * b| := by simp [abs_div]
      have habs2 : |b - y n| = |y n - b| := by simp [abs_sub_comm]
      have habs3 : |y n * b| = |y n| * |b| := by simp [abs_mul]
      have habs : |(y n)⁻¹ - b⁻¹| = |y n - b| / (|y n| * |b|) := by
         simp [habs1, habs2, habs3]

      -- 最後：用 hyb2 和 |y n| ≥ |b|/2 推出 < ε
      have hdenpos : 0 < |y n| * |b| := mul_pos hypos hbpos  -- 分母正
      have hden_lb : (|b| * |b|) / 2 ≤ |y n| * |b| := by  -- 分母下界
         have : |b| / 2 ≤ |y n| := hy_abs_lb
         have hb0 : 0 ≤ |b| := abs_nonneg b
         have h1 : (|b| / 2) * |b| ≤ |y n| * |b| := mul_le_mul_of_nonneg_right this hb0
         have h2 : (|b| / 2) * |b| = (|b| * |b|) / 2 := by ring
         simpa [h2] using h1
      have hnum : |y n - b| < ε * |b| * |b| / 2 := hyb2  -- 分子界
      have hden : ε * ((|b| * |b|) / 2) ≤ ε * (|y n| * |b|) := by  -- 分母界乘 ε
         have hε0 : 0 ≤ ε := le_of_lt hε
         exact mul_le_mul_of_nonneg_left hden_lb hε0
      have hlt : |y n - b| < ε * (|y n| * |b|) := by  -- 分子 < ε·分母
         have : ε * |b| * |b| / 2 = ε * ((|b| * |b|) / 2) := by ring
         exact lt_of_lt_of_le (by simpa [this] using hnum) hden
      -- 從 |y n - b| < ε*(|y n|*|b|) 推出 |y n - b|/(|y n|*|b|) < ε（兩邊同除以正數）
      have : |y n - b| / (|y n| * |b|) < ε := by
         have hpos : 0 < |y n| * |b| := hdenpos
         have h := hlt
         have h1 :
             |y n - b| / (|y n| * |b|) <
               (ε * (|y n| * |b|)) / (|y n| * |b|) :=
           (div_lt_div_of_pos_right (a := |y n - b|) (b := ε * (|y n| * |b|)) (c := |y n| * |b|) h) hpos
         have h2 : (ε * (|y n| * |b|)) / (|y n| * |b|) = ε := by
            field_simp [ne_of_gt hpos]
         simpa [h2] using h1
      simpa [habs] using this  -- 得 |(y n)⁻¹ - b⁻¹| < ε
   have hmul : converge_to (fun n => x n * (y n)⁻¹) (a * b⁻¹) :=  -- 乘法極限
      Theorem_2_12_iii x (fun n => (y n)⁻¹) a (b⁻¹) hx hy_inv
   simpa [hdiv, div_eq_mul_inv] using hmul  -- 換回除法形式
end WadeAnalysis
