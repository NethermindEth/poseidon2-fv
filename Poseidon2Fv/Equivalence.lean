import Mathlib

import Poseidon2Fv.Spec
import Poseidon2Fv.Folding

lemma apply_m4_equiv
  [Fact P.Prime]
  (x0 x1 x2 x3: ZMod P) --mathlib zmod
  (state : Fin 16 → ZMod P)
  (h_state0 : state offset = x0)
  (h_state1 : state (offset + 1) = x1)
  (h_state2 : state (offset + 2) = x2)
  (h_state3 : state (offset + 3) = x3)
:
  (Poseidon2Spec.smallMatrixAction #[x0, x1, x2, x3]).size = 4 ∧
  ∀ idx: Fin 4,
  (Poseidon2Spec.smallMatrixAction #[x0, x1, x2, x3])[idx]? =
  .some ↑(Poseidon2.Folding.apply_m4 state offset idx)
:= by

  simp [
    Poseidon2Spec.smallMatrixAction,
    Poseidon2.Folding.apply_m4,
    Poseidon2Spec.matrix_action,
    Poseidon2Spec.add_array
  ]
  intro idx; fin_cases idx <;> {
    simp [
      h_state0,
      h_state1,
      h_state2,
      h_state3,
    ]
    grind
  }
