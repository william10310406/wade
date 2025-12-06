/-
# 分析學基礎 (An Introduction to Analysis)

基於 Wade 的《An Introduction to Analysis》第 4 版

這個檔案包含第一章：實數系統的基礎內容
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
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
-- 絕對值的三角不等式
-- 語法：`|a|` 是絕對值的記號，`≤` 是小於等於
-- 三角不等式：|a + b| ≤ |a| + |b|
-- `abs_add_le` 是三角不等式的定理

-- 絕對值的其他性質
-- 語法：`≥` 表示大於等於，等價於 `≤` 的反向
-- `abs_nonneg` 表示絕對值非負

-- 語法：`↔` 表示雙向蘊含（若且唯若，iff）
-- `abs_eq_zero` 表示：|a| = 0 若且唯若 a = 0

end WadeAnalysis
