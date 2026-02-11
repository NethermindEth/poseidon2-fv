import Poseidon2Fv.Equivalence.FullRound
import Poseidon2Fv.Equivalence.PartialRound

lemma run_rounds_equiv
  (fin_state : Fin 16 → (ZMod P))
  [fact_prime: Fact P.Prime]
:
  let profile := ⟨⟨p1, p2, P, 7⟩, 8, 13⟩
  Poseidon2.runRounds
    profile
    ⟨internalMatrixDiag profile, full_round_constants, Array.ofFn Poseidon2.Folding.partial_round_constants⟩
    ⟨0, (Array.ofFn fin_state)⟩ =
  ⟨(), ⟨21, Array.ofFn (Poseidon2.Folding.permutation fin_state)⟩⟩
:= by
  simp [
    Poseidon2.runRounds,
    SeqRight.seqRight,
    StateT.bind,
    bind,
    Monad.repeatM
  ]

  rewrite [external_linear_layer_equiv]; simp
  have (state : Fin 16 → ZMod P) (start_round : Fin 4) := @beginning_full_round_equiv
    p1
    p2
    P
    (internalMatrixDiag { M := p1, t := p2, p := P, a := 7, fullRounds := 8, partRounds := 13 })
    (Array.ofFn Poseidon2.Folding.partial_round_constants)
    state
    start_round
    fact_prime
  have this := this (Poseidon2.Folding.mds_light_permutation fin_state) 0
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.beginning_full_round (Poseidon2.Folding.mds_light_permutation fin_state) 0
  have this := this state 1
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.beginning_full_round state 1
  have this := this state 2
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.beginning_full_round state 2
  have this := this state 3
  simp at this
  rewrite [this]; clear this; simp [pure, ReaderT.pure, StateT.pure]

  clear this

  set state := Poseidon2.Folding.beginning_full_round state 3
  have (state : Fin 16 → ZMod P) (partial_round : Fin 13) := @partial_round_equiv
    P
    partial_round
    p1
    p2
    state
    full_round_constants
    fact_prime
  have this := this state 0
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.partial_round state 0
  have this := this state 1
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.partial_round state 1
  have this := this state 2
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.partial_round state 2
  have this := this state 3
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.partial_round state 3
  have this := this state 4
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.partial_round state 4
  have this := this state 5
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.partial_round state 5
  have this := this state 6
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.partial_round state 6
  have this := this state 7
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.partial_round state 7
  have this := this state 8
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.partial_round state 8
  have this := this state 9
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.partial_round state 9
  have this := this state 10
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.partial_round state 10
  have this := this state 11
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.partial_round state 11
  have this := this state 12
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.partial_round state 12

  clear this

  have (state : Fin 16 → ZMod P) (ending_round : Fin 4) := @ending_full_round_equiv
    p1
    p2
    P
    (internalMatrixDiag { M := p1, t := p2, p := P, a := 7, fullRounds := 8, partRounds := 13 })
    (Array.ofFn Poseidon2.Folding.partial_round_constants)
    state
    ending_round
    fact_prime
  have this := this state 0
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.ending_full_round state 0
  have this := this state 1
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.ending_full_round state 1
  have this := this state 2
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.ending_full_round state 2
  have this := this state 3
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2.Folding.ending_full_round state 3

  rfl

lemma hash_equiv
  (fin_state : Fin 16 → (ZMod P))
  [fact_prime: Fact P.Prime]
:
  let profile := ⟨⟨p1, p2, P, 7⟩, 8, 13⟩
  Poseidon2.hash
    profile
    ⟨
      internalMatrixDiag profile,
      full_round_constants,
      Array.ofFn Poseidon2.Folding.partial_round_constants
    ⟩
    (Array.ofFn fin_state)
  =
  ⟨21, Array.ofFn (Poseidon2.Folding.permutation fin_state)⟩
:= by
  simp [
    Poseidon2.hash,
    StateT.run,
    ReaderT.run,
    Functor.map,
    Poseidon2.initialState
  ]
  rewrite [run_rounds_equiv]
  simp
