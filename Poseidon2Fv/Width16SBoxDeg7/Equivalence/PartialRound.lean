import Poseidon2Fv.Equivalence.InternalLinearLayer

lemma add_partial_round_constants_equiv
  (fin_state : Fin 16 → ZMod P)
  [Fact P.Prime]
:
  ((Array.ofFn fin_state).modify 0 fun x ↦ x + Poseidon2.Folding.partial_round_constants partial_round) =
  Array.ofFn (Poseidon2.Folding.add_partial_round_constant fin_state partial_round)
:= by
  apply Array.toList_inj.mp
  simp [Poseidon2.Folding.add_partial_round_constant]

lemma apply_partial_round_sbox_equiv
  (fin_state : Fin 16 → ZMod P)
  [Fact P.Prime]
:
  (Array.ofFn fin_state).modify 0 (Poseidon.HashProfile.sBox ⟨⟨a, b, P, 7⟩, full_rounds, partial_rounds⟩) =
  Array.ofFn (Poseidon2.Folding.apply_partial_round_sbox fin_state)
:= by
  apply Array.toList_inj.mp
  simp [Poseidon.HashProfile.sBox, Poseidon2.Folding.apply_partial_round_sbox]

lemma partial_round_equiv
  (fin_state : Fin 16 → (ZMod P))
  (full_round_constants : Array (Array (ZMod P)))
  [Fact P.Prime]
:
  let profile := ⟨⟨p1, p2, P, 7⟩, 8, 13⟩
  Poseidon2.partialRound
    profile
    ⟨internalMatrixDiag profile, full_round_constants, Array.ofFn Poseidon2.Folding.partial_round_constants⟩
    ⟨4 + partial_round.val, Array.ofFn fin_state⟩
  =
    ⟨
      PUnit.unit,
      ⟨
        4 + partial_round.val + 1,
        Array.ofFn (Poseidon2.Folding.partial_round fin_state partial_round)
      ⟩
    ⟩
:= by
  simp [
    Poseidon2.partialRound,
    SeqRight.seqRight,
    StateT.bind,
    bind,
    Poseidon2.addPartialConst,
    ReaderT.bind
  ]
  unfold get instMonadStateOfMonadStateOf getThe MonadStateOf.get instMonadStateOfOfMonadLift liftM monadLift instMonadLiftTOfMonadLift MonadLift.monadLift ReaderT.instMonadLift monadLift instMonadLiftT MonadStateOf.get instMonadStateOfStateTOfMonad StateT.get
  dsimp
  unfold read instMonadReaderOfMonadReaderOf readThe MonadReaderOf.read instMonadReaderOfReaderTOfMonad ReaderT.read pure Applicative.toPure Monad.toApplicative StateT.instMonad StateT.pure
  dsimp
  unfold modify modifyGet instMonadStateOfMonadStateOf MonadStateOf.modifyGet StateT.modifyGet
  dsimp

  simp [
    Poseidon2.getPartialRound,
    -Array.map_map,
    add_partial_round_constants_equiv
  ]
  rewrite [
    apply_partial_round_sbox_equiv,
    internal_linear_layer_equiv
  ]
  rfl
