import Mathlib

import Poseidon2Fv.Spec
import Poseidon2Fv.Folding

lemma smallMatrixAction_size
  (slice : Array (ZMod P))
  (h_slice : slice.size = 4)
:
  (Poseidon2Spec.smallMatrixAction slice).size = 4
:= by
  have : slice = #[slice[0], slice[1], slice[2], slice[3]] := by grind
  rewrite [this]; clear this
  simp [
    Poseidon2Spec.smallMatrixAction,
    Poseidon2Spec.matrix_action,
    Poseidon2Spec.add_array
  ]

lemma apply_m4_equiv
  [Fact P.Prime]
  (x0 x1 x2 x3: ZMod P) --mathlib zmod
  (state : Fin 16 → ZMod P)
  (h_state0 : state offset = x0)
  (h_state1 : state (offset + 1) = x1)
  (h_state2 : state (offset + 2) = x2)
  (h_state3 : state (offset + 3) = x3)
:
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

lemma external_linear_layer_equiv
  (round)
  (result_state)
  (x)
:
  Poseidon2Spec.externalLinearLayer profile context spec_state = ⟨x, ⟨round, result_state⟩⟩
:= by
  simp [
    Poseidon2Spec.externalLinearLayer,
    Poseidon2Spec.externalMatrixAction
  ]
  done
