import Mathlib

import Poseidon.Hash
import Poseidon2Fv.Folding

lemma smallMatrixAction_size
  (slice : Array (ZMod P))
  (h_slice : slice.size = 4)
:
  (Poseidon2.smallMatrixAction slice).size = 4
:= by
  have : slice = #[slice[0], slice[1], slice[2], slice[3]] := by grind
  rewrite [this]; clear this
  simp [
    Poseidon2.smallMatrixAction,
    Poseidon2.matrix_action,
    Poseidon2.add_array
  ]

lemma apply_m4_equiv
  [Fact P.Prime]
  (x0 x1 x2 x3: ZMod P)
  (state : Fin 24 → ZMod P)
  (h_state0 : state offset = x0)
  (h_state1 : state (offset + 1) = x1)
  (h_state2 : state (offset + 2) = x2)
  (h_state3 : state (offset + 3) = x3)
:
  ∀ idx: Fin 4,
  (Poseidon2.smallMatrixAction #[x0, x1, x2, x3])[idx]? =
  .some ↑(Poseidon2.Folding.apply_m4 state offset idx)
:= by
  simp [
    Poseidon2.smallMatrixAction,
    Poseidon2.Folding.apply_m4,
    Poseidon2.matrix_action,
    Poseidon2.add_array
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
  [Fact profile.p.Prime]
:
  Poseidon2.externalLinearLayer
    profile
    constants
    ⟨start_round, Array.ofFn fin_state⟩
  =
    ⟨PUnit.unit, ⟨start_round, Array.ofFn (Poseidon2.Folding.mds_light_permutation fin_state)⟩⟩
:= by
  simp [
    Poseidon2.externalLinearLayer,
    Poseidon2.externalMatrixAction,
    show Array.iota 3 = #[0, 1, 2, 3] by rfl
  ]
  unfold modify modifyGet instMonadStateOfMonadStateOf MonadStateOf.modifyGet instMonadStateOfOfMonadLift
  unfold monadLift instMonadLiftTOfMonadLift modifyGet
  dsimp
  unfold MonadLift.monadLift ReaderT.instMonadLift instMonadStateOfMonadStateOf
  dsimp
  unfold modifyGet instMonadStateOfMonadStateOf MonadStateOf.modifyGet instMonadStateOfStateTOfMonad StateT.modifyGet pure Id.instMonad Applicative.toPure Monad.toApplicative
  dsimp
  simp [
    Array.size_ofFn,
    show Array.iota 5 = #[0,1,2,3,4,5] by rfl,
    List.range',
    show (Array.ofFn fin_state).extract 0 4 = #[fin_state 0, fin_state 1, fin_state 2, fin_state 3] by apply Array.toList_inj.mp; simp,
    show (Array.ofFn fin_state).extract 4 8 = #[fin_state 4, fin_state 5, fin_state 6, fin_state 7] by apply Array.toList_inj.mp; simp,
    show (Array.ofFn fin_state).extract 8 12 = #[fin_state 8, fin_state 9, fin_state 10, fin_state 11] by apply Array.toList_inj.mp; simp,
    show (Array.ofFn fin_state).extract 12 16 = #[fin_state 12, fin_state 13, fin_state 14, fin_state 15] by apply Array.toList_inj.mp; simp,
    show (Array.ofFn fin_state).extract 16 20 = #[fin_state 16, fin_state 17, fin_state 18, fin_state 19] by apply Array.toList_inj.mp; simp,
    show (Array.ofFn fin_state).extract 20 24 = #[fin_state 20, fin_state 21, fin_state 22, fin_state 23] by apply Array.toList_inj.mp; simp,
    Poseidon2.smallMatrixAction,
    Poseidon2.matrix_action,
    Poseidon2.add_array,
    show Array.replicate 4 (0: ZMod profile.p) = #[0,0,0,0] by apply Array.toList_inj.mp; simp
  ]
  have (s1 s2: Array (ZMod profile.p)) (h: s1 = s2) :
    (PUnit.unit, { round := start_round, state := s1 : Poseidon.Hash.State profile}) =
    (PUnit.unit, { round := start_round, state := s2 : Poseidon.Hash.State profile})
  := by rw [h]
  apply this; clear this
  apply Array.toList_inj.mp
  simp
  have h2 (a: ZMod profile.p) : 2*a = a+a := by grind only
  have h3 (a: ZMod profile.p) : 3*a = a+a+a := by grind only
  split_ands
  all_goals (
    unfold Poseidon2.Folding.mds_light_permutation
    dsimp
    unfold Poseidon2.Folding.apply_m4_sums
    dsimp
    unfold Poseidon2.Folding.apply_m4_loop
    dsimp
    unfold Poseidon2.Folding.apply_m4
    dsimp
    ring
  )
