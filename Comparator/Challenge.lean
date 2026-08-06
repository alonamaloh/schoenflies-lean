/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
import Schoenflies.BoundaryAnchors

/-!
# Trusted Comparator challenge

This file is the small trusted statement surface for the headline theorem.  It deliberately
does not import `Schoenflies.JordanSchoenflies`, where the proof lives.

The `sorry` is the challenge hole expected by `leanprover/comparator`; it is not part of the
`Schoenflies` library or its default build.  Comparator checks that the declaration supplied by
`Solution` has exactly this statement, is accepted by the Lean kernel, and uses only
the axioms permitted in `Comparator/schoenflies.json`.
-/

open Set

namespace Schoenflies

variable {C C' : Set Plane}

/-- Every homeomorphism between two Jordan curves extends to a self-homeomorphism of the
plane. -/
theorem jordan_schoenflies_of_homeomorph
    (hC : IsJordanCurve C) (hC' : IsJordanCurve C') (e : ↥C ≃ₜ ↥C') :
    ∃ F : Plane ≃ₜ Plane, ∀ z : ↥C, F z = e z := by
  sorry

end Schoenflies
