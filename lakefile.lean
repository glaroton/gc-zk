import Lake
open Lake DSL

package «gc-zk» where
  version := v!"0.1.0"
  keywords := #["math", "cryptography"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.36.0-rc2"

/-
Development only. `checkdecls` checks that every declaration cited in the blueprint exists. It is
required only when Lake runs with `-Kenv=dev` (`lake -Kenv=dev exe checkdecls blueprint/lean_decls`),
so a project that depends on gc-zk inherits Mathlib and nothing else.
-/
meta if get_config? env = some "dev" then
require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

/-- The library. `GcZk.API` lists the declarations meant to be used by other projects. -/
@[default_target]
lean_lib GcZk where
  roots := #[`GcZk, `GcZk.API]
