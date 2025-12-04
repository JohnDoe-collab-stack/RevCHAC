import Lake
open Lake DSL

package "RevCHAC" where
  -- Settings applied to both library and executables
  -- add any additional package configuration options here

require "mathlib" from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.26.0-rc2"

@[default_target]
lean_lib "RevCHAC" where
  srcDir := "RevCHAC"
