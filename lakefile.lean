import Lake
open Lake DSL

package «wade-analysis»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.25.0"

@[default_target]
lean_lib «WadeAnalysis» where
  -- 这里可以添加库的配置
