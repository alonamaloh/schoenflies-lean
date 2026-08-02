/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.MeshCore
import Schoenflies.SkelCore

/-!
# The mesh chain, closed

The two core bridges are theorems — `Schoenflies.hasTwoConnectedMeshCores`
(`MeshCore.lean`) and `Schoenflies.hasTwoConnectedSkelCores` (`SkelCore.lean`) — and this
module is the one-line composition their modules deliberately left to the integrator, so that
the two stayed independent. Out of it, `Schoenflies.HasMeshSteps` holds with no hypothesis
beyond the combinatorial invariants of the base structure and `IsSeparating C`: the whole
target-mesh chain

`cores → HasTwoConnectedMeshOverlays → HasMeshOverlays → HasMeshTransfers → HasMeshSteps`

is unconditional.

## Blueprint

* `Schoenflies.hasMeshSteps'` — the target-mesh enlargement chooser of `prop:shrinking-stars`:
  `prop:anchored-square-mesh` overlaid with the stage skeleton and transferred back by
  `thm:finite-transfer`(b), with every link a theorem.
-/

open Set

namespace Schoenflies

variable {γ : Type*} [Infinite γ] {S₀ : CellStructure γ} {C : Set Plane}

/-- **The target-mesh chooser, unconditional.** Every link of the mesh chain is a theorem, so
`HasMeshSteps` needs nothing beyond the base structure's combinatorial invariants and the
Jordan separation of `C`. -/
theorem hasMeshSteps' (h₀ : S₀.CombInvariants) (hsep : IsSeparating C) :
    HasMeshSteps S₀ C :=
  hasMeshSteps_of_cores h₀ hsep
    (hasTwoConnectedCores_of (hasTwoConnectedMeshCores S₀ C) (hasTwoConnectedSkelCores S₀ C))

/-- Over the concrete base, the Phase 3 stage sequence now rests on the source-grid chooser
alone. -/
example {C : Set Plane} (hC : IsJordanCurve C) (hg : HasGridSteps initialStructure C) :
    Nonempty (StageSequence InitialCell initialStructure C) :=
  ⟨stageSequence_of_isJordanCurve hC hg
    (hasMeshSteps' combInvariants_initialStructure (jordan_curve_theorem hC))⟩

end Schoenflies
