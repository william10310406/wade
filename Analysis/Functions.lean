/-
# 函数 (Functions)

基于 Wade 第三章：R 上的函数
-/

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Real
import Mathlib.Tactic

namespace WadeAnalysis

/-
## 第三章：R 上的函数 (Chapter 3: Functions on ℝ)

### 3.1 双侧极限 (Two-Sided Limits)

函数在一点的极限
-/

-- 函数类型：ℝ → ℝ
#check (ℝ → ℝ)

-- 函数极限的定义
#check Filter.Tendsto

-- 一个例子：lim_{x → 0} sin(x)/x = 1
-- 这个在 Mathlib 中已经有证明

/-
### 3.2 单侧极限和无穷远处的极限

左极限、右极限和无穷远处的极限
-/

-- 右极限
#check Filter.Tendsto

-- 左极限
#check Filter.Tendsto

/-
### 3.3 连续性 (Continuity)

连续函数的定义和性质
-/

-- 连续性的定义
#check ContinuousAt
#check Continuous

-- 连续函数的例子
example : Continuous (fun x : ℝ => x^2) := by
  exact continuous_pow 2

-- 连续函数的复合
example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    Continuous (f ∘ g) :=
  Continuous.comp hf hg

/-
### 3.4 一致连续性 (Uniform Continuity)

一致连续性的定义
-/

#check UniformContinuous

end WadeAnalysis
