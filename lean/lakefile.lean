import Lake
open Lake DSL

package jsp314

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"

@[default_target]
lean_lib JSP314 where
  globs := #[.andSubmodules `JSP314]
