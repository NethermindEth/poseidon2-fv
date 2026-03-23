import Poseidon2Fv.Field
import Poseidon2Fv.Width24SBoxDeg11.Equivalence.FullRound
import Poseidon2Fv.Width24SBoxDeg11.Equivalence.PartialRound
import Poseidon2Fv.Width24SBoxDeg11.EndingFullRounds
import Poseidon.Parameters.BabyBear

open Field
open Poseidon2W24S11.BeginningFullRounds
open Poseidon2W24S11.InternalLinearLayer
open Poseidon2W24S11.PartialRound
open Poseidon2W24S11.FullRound
open Poseidon2W24S11.EndingFullRounds
open Poseidon2W24S11.ExternalLinearLayer

namespace Poseidon2W24S11.Permuation

lemma run_rounds_equiv
  (fin_state : Fin 24 → (ZMod P))
  [fact_prime: Fact P.Prime]
:
  let profile := ⟨⟨p1, p2, P, 11⟩, 8, 21⟩
  Poseidon2.runRounds
    profile
    ⟨internalMatrixDiag profile, full_round_constants, Array.ofFn Poseidon2W24S11.Folding.partial_round_constants⟩
    ⟨0, (Array.ofFn fin_state)⟩ =
  ⟨(), ⟨29, Array.ofFn (Poseidon2W24S11.Folding.permutation fin_state)⟩⟩
:= by
  simp [
    Poseidon2.runRounds,
    SeqRight.seqRight,
    StateT.bind,
    bind,
    Monad.repeatM
  ]

  rewrite [external_linear_layer_equiv]; simp
  have (state : Fin 24 → ZMod P) (start_round : Fin 4) := @beginning_full_round_equiv
    p1
    p2
    P
    (internalMatrixDiag { M := p1, t := p2, p := P, a := 11, fullRounds := 8, partRounds := 21 })
    (Array.ofFn Poseidon2W24S11.Folding.partial_round_constants)
    state
    start_round
    fact_prime
  have this := this (Poseidon2W24S11.Folding.mds_light_permutation fin_state) 0
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.beginning_full_round (Poseidon2W24S11.Folding.mds_light_permutation fin_state) 0
  have this := this state 1
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.beginning_full_round state 1
  have this := this state 2
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.beginning_full_round state 2
  have this := this state 3
  simp at this
  rewrite [this]; clear this; simp [pure, ReaderT.pure, StateT.pure]

  clear this

  set state := Poseidon2W24S11.Folding.beginning_full_round state 3
  have (state : Fin 24 → ZMod P) (partial_round : Fin 21) := @partial_round_equiv
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

  set state := Poseidon2W24S11.Folding.partial_round state 0
  have this := this state 1
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 1
  have this := this state 2
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 2
  have this := this state 3
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 3
  have this := this state 4
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 4
  have this := this state 5
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 5
  have this := this state 6
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 6
  have this := this state 7
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 7
  have this := this state 8
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 8
  have this := this state 9
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 9
  have this := this state 10
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 10
  have this := this state 11
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 11
  have this := this state 12
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 12
  have this := this state 13
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 13
  have this := this state 14
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 14
  have this := this state 15
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 15
  have this := this state 16
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 16
  have this := this state 17
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 17
  have this := this state 18
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 18
  have this := this state 19
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 19
  have this := this state 20
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.partial_round state 20

  clear this

  have (state : Fin 24 → ZMod P) (ending_round : Fin 4) := @ending_full_round_equiv
    p1
    p2
    P
    (internalMatrixDiag { M := p1, t := p2, p := P, a := 11, fullRounds := 8, partRounds := 21 })
    (Array.ofFn Poseidon2W24S11.Folding.partial_round_constants)
    state
    ending_round
    fact_prime
  have this := this state 0
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.ending_full_round state 0
  have this := this state 1
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.ending_full_round state 1
  have this := this state 2
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.ending_full_round state 2
  have this := this state 3
  simp at this
  rewrite [this]; clear this; simp

  set state := Poseidon2W24S11.Folding.ending_full_round state 3

  rfl

lemma hash_equiv
  (fin_state : Fin 24 → (ZMod P))
  [fact_prime: Fact P.Prime]
:
  let profile := ⟨⟨p1, p2, P, 11⟩, 8, 21⟩
  Poseidon2.hash
    profile
    ⟨
      internalMatrixDiag profile,
      full_round_constants,
      Array.ofFn Poseidon2W24S11.Folding.partial_round_constants
    ⟩
    (Array.ofFn fin_state)
  =
  ⟨29, Array.ofFn (Poseidon2W24S11.Folding.permutation fin_state)⟩
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
    Poseidon2W24S11.Extraction.constraint_288 c row ∧
    Poseidon2W24S11.Extraction.constraint_289 c row ∧
    Poseidon2W24S11.Extraction.constraint_290 c row ∧
    Poseidon2W24S11.Extraction.constraint_291 c row ∧
    Poseidon2W24S11.Extraction.constraint_292 c row ∧
    Poseidon2W24S11.Extraction.constraint_293 c row ∧
    Poseidon2W24S11.Extraction.constraint_294 c row ∧
    Poseidon2W24S11.Extraction.constraint_295 c row ∧
    Poseidon2W24S11.Extraction.constraint_296 c row ∧
    Poseidon2W24S11.Extraction.constraint_297 c row ∧
    Poseidon2W24S11.Extraction.constraint_298 c row ∧
    Poseidon2W24S11.Extraction.constraint_299 c row ∧
    Poseidon2W24S11.Extraction.constraint_300 c row ∧
    Poseidon2W24S11.Extraction.constraint_301 c row ∧
    Poseidon2W24S11.Extraction.constraint_302 c row ∧
    Poseidon2W24S11.Extraction.constraint_303 c row ∧
    Poseidon2W24S11.Extraction.constraint_304 c row ∧
    Poseidon2W24S11.Extraction.constraint_305 c row ∧
    Poseidon2W24S11.Extraction.constraint_306 c row ∧
    Poseidon2W24S11.Extraction.constraint_307 c row ∧
    Poseidon2W24S11.Extraction.constraint_308 c row ∧
    Poseidon2W24S11.Extraction.constraint_309 c row ∧
    Poseidon2W24S11.Extraction.constraint_310 c row ∧
    Poseidon2W24S11.Extraction.constraint_311 c row ∧
    Poseidon2W24S11.Extraction.constraint_312 c row ∧
    Poseidon2W24S11.Extraction.constraint_313 c row ∧
    Poseidon2W24S11.Extraction.constraint_314 c row ∧
    Poseidon2W24S11.Extraction.constraint_315 c row ∧
    Poseidon2W24S11.Extraction.constraint_316 c row ∧
    Poseidon2W24S11.Extraction.constraint_317 c row ∧
    Poseidon2W24S11.Extraction.constraint_318 c row ∧
    Poseidon2W24S11.Extraction.constraint_319 c row ∧
    Poseidon2W24S11.Extraction.constraint_320 c row ∧
    Poseidon2W24S11.Extraction.constraint_321 c row ∧
    Poseidon2W24S11.Extraction.constraint_322 c row ∧
    Poseidon2W24S11.Extraction.constraint_323 c row ∧
    Poseidon2W24S11.Extraction.constraint_324 c row ∧
    Poseidon2W24S11.Extraction.constraint_325 c row ∧
    Poseidon2W24S11.Extraction.constraint_326 c row ∧
    Poseidon2W24S11.Extraction.constraint_327 c row ∧
    Poseidon2W24S11.Extraction.constraint_328 c row ∧
    Poseidon2W24S11.Extraction.constraint_329 c row ∧
    Poseidon2W24S11.Extraction.constraint_330 c row ∧
    Poseidon2W24S11.Extraction.constraint_331 c row ∧
    Poseidon2W24S11.Extraction.constraint_332 c row ∧
    Poseidon2W24S11.Extraction.constraint_333 c row ∧
    Poseidon2W24S11.Extraction.constraint_334 c row ∧
    Poseidon2W24S11.Extraction.constraint_335 c row ∧
    Poseidon2W24S11.Extraction.constraint_336 c row ∧
    Poseidon2W24S11.Extraction.constraint_337 c row ∧
    Poseidon2W24S11.Extraction.constraint_338 c row ∧
    Poseidon2W24S11.Extraction.constraint_339 c row ∧
    Poseidon2W24S11.Extraction.constraint_340 c row ∧
    Poseidon2W24S11.Extraction.constraint_341 c row ∧
    Poseidon2W24S11.Extraction.constraint_342 c row ∧
    Poseidon2W24S11.Extraction.constraint_343 c row ∧
    Poseidon2W24S11.Extraction.constraint_344 c row ∧
    Poseidon2W24S11.Extraction.constraint_345 c row ∧
    Poseidon2W24S11.Extraction.constraint_346 c row ∧
    Poseidon2W24S11.Extraction.constraint_347 c row ∧
    Poseidon2W24S11.Extraction.constraint_348 c row ∧
    Poseidon2W24S11.Extraction.constraint_349 c row ∧
    Poseidon2W24S11.Extraction.constraint_350 c row

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
    let profile := ⟨⟨p1, p2, BabyBear_Prime, 11⟩, 8, 21⟩
    Poseidon2.hash
      profile
      ⟨
        internalMatrixDiag profile,
        full_round_constants,
        Array.ofFn Poseidon2W24S11.Folding.partial_round_constants
      ⟩
      (Array.ofFn (Poseidon2W24S11.Folding.inputs c row))
    =
    ⟨29, Array.ofFn (Poseidon2W24S11.Folding.ending_full_rounds c row 3).post⟩
  := by
    rewrite [poseidon_permutation]
    . exact hash_equiv (Poseidon2W24S11.Folding.inputs c row)
    . exact babybear_halve
    . exact babybear_div_pow_2
    . exact babybear_div_pow_3
    . exact babybear_div_pow_4
    . exact babybear_div_pow_5
    . exact babybear_div_pow_6
    . exact babybear_div_pow_7
    . exact babybear_div_pow_8
    . exact babybear_div_pow_9
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
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    . exact h_constraints.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    . exact h_constraints.2.2.1
    . exact h_constraints.2.2.2.1
    . exact h_constraints.2.2.2.2.1
    . exact h_constraints.2.2.2.2.2

  -- The following lemmas double-check that the above proof `hash_equiv_of_constraints` works with the parameters defined in the Poseidon.lean repository,
  --   which has been tested against other Poseidon 2 implementations.
  lemma equivalentBabyBearPrime : BabyBear_Prime = Poseidon2.BabyBear24.hashProfile.p := by
    unfold BabyBear_Prime
    unfold Poseidon2.BabyBear24.hashProfile
    unfold Poseidon2.BabyBear24.secProfile
    unfold Poseidon2.BabyBear.commonProfile
    unfold Poseidon2.BabyBear.p
    simp

  lemma equivalentProfile : ∃ p1 p2, ⟨⟨p1, p2, Poseidon2.BabyBear24.hashProfile.p, 11⟩, 8, 21⟩ = Poseidon2.BabyBear24.hashProfile := by
    exists 128
    exists 24

  instance : Fact Poseidon2.BabyBear24.hashProfile.p.Prime :=
    ⟨by unfold Poseidon2.BabyBear24.hashProfile
        unfold Poseidon2.BabyBear24.secProfile
        unfold Poseidon2.BabyBear.commonProfile
        unfold Poseidon2.BabyBear.p
        simp
        norm_num⟩

  lemma equivalentInternalMatrixDiag : (#[0 - 2, 1, 2, 1 / 2, 3, 4, 0 - 1 / 2, 0 - 3, 0 - 4, 1 / 256, 1 / 4, 1 / 8, 1 / 16, 1 / 128, 1 / 512, 1 / 134217728, 0 - 1 / 256, 0 - 1 / 4, 0 - 1 / 8, 0 - 1 / 16, 0 - 1 / 32, 0 - 1 / 64, 0 - 1 / 128, 0 - 1 / 134217728] : Array (ZMod BabyBear_Prime))
    = #[2013265919, 1, 2, 1006632961, 3, 4, 1006632960, 2013265918, 2013265917, 2005401601, 1509949441, 1761607681, 1887436801, 1997537281, 2009333761, 2013265906, 7864320, 503316480, 251658240, 125829120, 62914560, 31457280, 15728640, 15]
     := by decide

  lemma hash_equiv_of_constraints'
    [hInst₁ : Field ExtF] [hInst₂ : Circuit (ZMod BabyBear_Prime) ExtF C]
    (c : C (ZMod BabyBear_Prime) ExtF) (row: ℕ)
    (h_constraints : all_constraints c row)
  :
    Poseidon2.hash
      ⟨⟨p1, p2, BabyBear_Prime, 11⟩, 8, 21⟩
      ⟨
        Poseidon2.BabyBear24.internalMatrixDiag,
        Poseidon2.BabyBear24.fullRoundConstants,
        Poseidon2.BabyBear24.partialRoundConstants⟩
      (Array.ofFn (Poseidon2W24S11.Folding.inputs c row))
    =
    ⟨29, Array.ofFn (Poseidon2W24S11.Folding.ending_full_rounds c row 3).post⟩ := by

  have hEquiv := @hash_equiv_of_constraints ExtF C p1 p2 inferInstance hInst₁ hInst₂ c row h_constraints
  simp only [Fin.isValue] at hEquiv

  have hInternalMatrixDiag : internalMatrixDiag ⟨⟨p1, p2, BabyBear_Prime, 11⟩, 8, 21⟩ = Poseidon2.BabyBear24.internalMatrixDiag := by
    unfold Poseidon2.BabyBear24.internalMatrixDiag
    unfold internalMatrixDiag
    exact equivalentInternalMatrixDiag
  rw [hInternalMatrixDiag] at hEquiv

  have hFullRoundConstants : full_round_constants = Poseidon2.BabyBear24.fullRoundConstants := by
    decide
  rw [hFullRoundConstants] at hEquiv

  have hPartialRoundConstants : Array.ofFn Folding.partial_round_constants = Poseidon2.BabyBear24.partialRoundConstants := by
    decide
  rw [hPartialRoundConstants] at hEquiv

  exact hEquiv

  instance [Field ExtF] [c: Circuit (ZMod BabyBear_Prime) ExtF C] : Circuit (ZMod Poseidon2.BabyBear24.hashProfile.p) ExtF C := by aesop

  lemma hash_equiv_of_constraints''
    [hInst₁ : Field ExtF] [hInst₂ : Circuit (ZMod BabyBear_Prime) ExtF C]
    (c : C (ZMod BabyBear_Prime) ExtF) (row: ℕ)
    (h_constraints : all_constraints c row)
  :
    Poseidon2.hash
      Poseidon2.BabyBear24.hashProfile
      ⟨
        Poseidon2.BabyBear24.internalMatrixDiag,
        Poseidon2.BabyBear24.fullRoundConstants,
        Poseidon2.BabyBear24.partialRoundConstants⟩
      (Array.ofFn (Poseidon2W24S11.Folding.inputs c row))
    =
    ⟨29, Array.ofFn (Poseidon2W24S11.Folding.ending_full_rounds c row 3).post⟩ :=
  by
    apply hash_equiv_of_constraints'
    exact h_constraints


end constraints

end Poseidon2W24S11.Permuation
