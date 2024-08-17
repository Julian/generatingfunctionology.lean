import Lake
open Lake DSL

package "Generatingfunctionology" where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
require "leanprover-community" / "mathlib"

@[default_target]
lean_lib Generatingfunctionology where
