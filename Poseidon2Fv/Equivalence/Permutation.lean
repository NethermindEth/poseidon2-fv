import Poseidon2Fv.Field
import Poseidon2Fv.Equivalence.FullRound
import Poseidon2Fv.Equivalence.PartialRound
import Poseidon2Fv.EndingFullRounds

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

section constraints

  open Plonky3

  def all_beginning_full_round_constraints
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :=
    beginning_full_round_0_constraints c row ∧
    beginning_full_round_1_constraints c row ∧
    beginning_full_round_2_constraints c row ∧
    beginning_full_round_3_constraints c row

  def all_partial_round_constraints
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :=
    Poseidon2.Extraction.constraint_128 c row ∧
    Poseidon2.Extraction.constraint_129 c row ∧
    Poseidon2.Extraction.constraint_130 c row ∧
    Poseidon2.Extraction.constraint_131 c row ∧
    Poseidon2.Extraction.constraint_132 c row ∧
    Poseidon2.Extraction.constraint_133 c row ∧
    Poseidon2.Extraction.constraint_134 c row ∧
    Poseidon2.Extraction.constraint_135 c row ∧
    Poseidon2.Extraction.constraint_136 c row ∧
    Poseidon2.Extraction.constraint_137 c row ∧
    Poseidon2.Extraction.constraint_138 c row ∧
    Poseidon2.Extraction.constraint_139 c row ∧
    Poseidon2.Extraction.constraint_140 c row ∧
    Poseidon2.Extraction.constraint_141 c row ∧
    Poseidon2.Extraction.constraint_142 c row ∧
    Poseidon2.Extraction.constraint_143 c row ∧
    Poseidon2.Extraction.constraint_144 c row ∧
    Poseidon2.Extraction.constraint_145 c row ∧
    Poseidon2.Extraction.constraint_146 c row ∧
    Poseidon2.Extraction.constraint_147 c row ∧
    Poseidon2.Extraction.constraint_148 c row ∧
    Poseidon2.Extraction.constraint_149 c row ∧
    Poseidon2.Extraction.constraint_150 c row ∧
    Poseidon2.Extraction.constraint_151 c row ∧
    Poseidon2.Extraction.constraint_152 c row ∧
    Poseidon2.Extraction.constraint_153 c row

  def all_ending_full_round_constraints
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :=
    ending_full_round_0_constraints c row ∧
    ending_full_round_1_constraints c row ∧
    ending_full_round_2_constraints c row ∧
    ending_full_round_3_constraints c row

  def all_constraints
    [Field F] [Field ExtF] [Circuit F ExtF C]
    (c : C F ExtF) (row: ℕ)
  :=
    all_beginning_full_round_constraints c row ∧
    all_partial_round_constraints c row ∧
    all_ending_full_round_constraints c row

  lemma hash_equiv_of_constraints
    [Fact BabyBear_Prime.Prime]
    [Field ExtF] [Circuit (ZMod BabyBear_Prime) ExtF C]
    (c : C (ZMod BabyBear_Prime) ExtF) (row: ℕ)
    (h_constraints : all_constraints c row)
  :
    let profile := ⟨⟨p1, p2, BabyBear_Prime, 7⟩, 8, 13⟩
    Poseidon2.hash
      profile
      ⟨
        internalMatrixDiag profile,
        full_round_constants,
        Array.ofFn Poseidon2.Folding.partial_round_constants
      ⟩
      (Array.ofFn (Poseidon2.Folding.inputs c row))
    =
    ⟨21, Array.ofFn (Poseidon2.Folding.ending_full_rounds c row 3).post⟩
  := by
    rewrite [poseidon_permutation]
    . exact hash_equiv (Poseidon2.Folding.inputs c row)
    . exact babybear_halve
    . exact babybear_div_pow_2
    . exact babybear_div_pow_3
    . exact babybear_div_pow_4
    . exact babybear_div_pow_8
    . exact babybear_div_pow_27
    . exact h_constraints.1.1
    . exact h_constraints.1.2.1
    . exact h_constraints.1.2.2.1
    . exact h_constraints.1.2.2.2
    . exact h_constraints.2.1.1
    . exact h_constraints.2.1.2.1
    . exact h_constraints.2.1.2.2.1
    . exact h_constraints.2.1.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    . exact h_constraints.2.2.1
    . exact h_constraints.2.2.2.1
    . exact h_constraints.2.2.2.2.1
    . exact h_constraints.2.2.2.2.2



end constraints
