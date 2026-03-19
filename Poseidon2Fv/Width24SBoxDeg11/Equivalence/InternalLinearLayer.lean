import Mathlib

import Poseidon.Hash
import Poseidon2Fv.Width24SBoxDeg11.Folding

def internalMatrixDiag (profile: Poseidon.HashProfile) [Fact profile.p.Prime] : Array (ZMod profile.p) := #[
  0-2,
  1,
  2,
  ((1: ZMod profile.p) / 2),
  3,
  4,
  0-((1: ZMod profile.p) / 2),
  0-3,
  0-4,
  ((1: ZMod profile.p) / 256),
  ((1: ZMod profile.p) / 4),
  ((1: ZMod profile.p) / 8),
  ((1: ZMod profile.p) / 16),
  ((1: ZMod profile.p) / 128),
  ((1: ZMod profile.p) / 512),
  ((1: ZMod profile.p) / 134217728),
  0-((1: ZMod profile.p) / 256),
  0-((1: ZMod profile.p) / 4),
  0-((1: ZMod profile.p) / 8),
  0-((1: ZMod profile.p) / 16),
  0-((1: ZMod profile.p) / 32),
  0-((1: ZMod profile.p) / 64),
  0-((1: ZMod profile.p) / 128),
  0-((1: ZMod profile.p) / 134217728),
]

lemma internal_linear_layer_equiv
  [Fact profile.p.Prime]
:
  Poseidon2.internalLinearLayer
    profile
    ⟨internalMatrixDiag profile, fullRoundConstants, partialRoundConstants⟩
    ⟨start_round, Array.ofFn fin_state⟩
  =
    ⟨
      PUnit.unit,
      ⟨start_round, Array.ofFn (Poseidon2W24S11.Folding.generic_internal_linear_layer fin_state)⟩
    ⟩
:= by
  -- Unfold the spec functions
  simp [
    Poseidon2.internalLinearLayer,
    bind,
    ReaderT.bind,
    StateT.bind,
    read, readThe, MonadReaderOf.read, ReaderT.read, pure, StateT.pure,
    Poseidon2.internalMatrixAction,
    internalMatrixDiag
  ]

  unfold modify modifyGet instMonadStateOfMonadStateOf MonadStateOf.modifyGet instMonadStateOfOfMonadLift modifyGet instMonadStateOfMonadStateOf MonadStateOf.modifyGet instMonadStateOfStateTOfMonad StateT.modifyGet pure Applicative.toPure Monad.toApplicative Id.instMonad monadLift instMonadLiftTOfMonadLift MonadLift.monadLift ReaderT.instMonadLift
  dsimp

  apply Prod.mk_inj.mpr
  simp
  apply Array.toList_inj.mp
  set sum := Array.foldl _ _ _ _ _
  have :
    sum =
    fin_state 0 +
    fin_state 1 +
    fin_state 2 +
    fin_state 3 +
    fin_state 4 +
    fin_state 5 +
    fin_state 6 +
    fin_state 7 +
    fin_state 8 +
    fin_state 9 +
    fin_state 10 +
    fin_state 11 +
    fin_state 12 +
    fin_state 13 +
    fin_state 14 +
    fin_state 15 +
    fin_state 16 +
    fin_state 17 +
    fin_state 18 +
    fin_state 19 +
    fin_state 20 +
    fin_state 21 +
    fin_state 22 +
    fin_state 23
  := by
    unfold sum
    rewrite [
      show Array.ofFn fin_state = #[
        fin_state 0,
        fin_state 1,
        fin_state 2,
        fin_state 3,
        fin_state 4,
        fin_state 5,
        fin_state 6,
        fin_state 7,
        fin_state 8,
        fin_state 9,
        fin_state 10,
        fin_state 11,
        fin_state 12,
        fin_state 13,
        fin_state 14,
        fin_state 15,
        fin_state 16,
        fin_state 17,
        fin_state 18,
        fin_state 19,
        fin_state 20,
        fin_state 21,
        fin_state 22,
        fin_state 23
      ] by {
        apply Array.toList_inj.mp
        simp
      }
    ]
    simp

  simp [this]; clear this sum
  split_ands
  all_goals simp [
    Poseidon2W24S11.Folding.generic_internal_linear_layer,
    Poseidon2W24S11.Folding.internal_layer_mat_mul,
    ←add_assoc,
    add_comm _ (fin_state 0)
  ]
  all_goals ring
