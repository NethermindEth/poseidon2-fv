import Mathlib

import Poseidon2Fv.Spec
import Poseidon2Fv.Folding

lemma apply_m4_equiv
  [Fact P.Prime]
  (x0 x1 x2 x3: ZMod P) --mathlib zmod
  (state : Fin 16 → ZMod P)
  (h_state0 : state idx = x0)
  (h_state1 : state (idx + 1) = x1)
  (h_state2 : state (idx + 2) = x2)
  (h_state3 : state (idx + 3) = x3)
:
  (Poseidon2Spec.smallMatrixAction #[x0, x1, x2, x3])[0]? =
  .some ↑(Poseidon2.Folding.apply_m4 state idx 0)
:= by
  simp [
    Poseidon2Spec.smallMatrixAction,
    Poseidon2.Folding.apply_m4,
    h_state0,
    h_state1,
    h_state2,
    h_state3,
    Poseidon2Spec.matrix_action,
    Poseidon2Spec.add_array
  ]
  grind
