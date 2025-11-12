Require Import cached_sum.
Require Import RISCVTiming.
Import RISCVNotations.
Require Import NEORV32.

Module Program_cached_sum <: ProgramInformation.
    Definition entry_addr : N := 0x210.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x250 => true
        | _ => false
    end | _ => false end.

    Definition binary := cached_sum.
End Program_cached_sum.

Module cpu := NEORV32Base Program_cached_sum.

Module RISCVTiming := RISCVTiming cpu Program_cached_sum.
Module cached_sumAuto := RISCVTimingAutomation RISCVTiming.
Import Program_cached_sum cached_sumAuto.

Definition sum (low high : N) (f : N -> N) : N :=
    let range := List.map N.of_nat (List.seq (N.to_nat low) (N.to_nat (high - low))) in
    List.fold_left (fun acc i => acc + f i) range 0.

Lemma sum_0_0 : forall f, sum 0 0 f = 0.
Proof. reflexivity. Qed.

Lemma sum_Sn : forall low high f,
    low <= high ->
    sum low (1 + high) f = sum low high f + f high.
Proof.
    intros. unfold sum at 1.
    rewrite <- N.add_sub_assoc, N.add_1_l, N2Nat.inj_succ.
    rewrite seq_S, map_app, fold_left_app. simpl.
    rewrite N2Nat.inj_sub at 2.
    rewrite Arith_base.le_plus_minus_r_stt by lia.
    rewrite N2Nat.id. reflexivity. assumption.
Qed.

Lemma sum_sub1 : forall low high body,
    low < high ->
    sum low (high - 1) (fun _ => body) + body = 
        sum low high (fun _ => body).
Proof.
    intros. unfold sum at 2.
    destruct (high - low) eqn:E using N.peano_ind.
    - lia.
    - clear IHn. rewrite N2Nat.inj_succ, seq_S, map_app, fold_left_app.
      simpl. unfold sum. now replace n with (high - 1 - low) by lia.
Qed.

Definition time_of_cached_sum (ra sp size : N) (arr : addr) (c c' : cache) (t : trace) :=
    cycle_count_of_trace t c = (
        taddi + tsw false (sp ⊖ 12) + taddi + taddi + tsw false (sp ⊖ 4) + 
            tsw false (sp ⊖ 8) + tjal false 0x1e4 +
        (* first call to sum *)
        (taddi + taddi + taddi + sum 0 size (fun i =>
                ttbne (0 <? i) 0x1f8 + tslli 0x2 +
                tadd + tlw false (arr ⊕ (i * 4)) + taddi + tadd +
                tjalr (0 <? i) 0x1f0
            )
        ) +
        taddi + taddi + taddi + tjal true 0x1e4 +
        (* second call to sum *)
        (taddi + taddi + taddi + sum 0 size (fun i =>
                ttbne true 0x1f8 + tslli 0x2 +
                tadd + tlw true (arr ⊕ (i * 4)) + taddi + tadd +
                tjalr true 0x1f0
            )
        ) +
        tlw true (sp ⊖ 4) + taddi + tlw true (sp ⊖ 8) + tlw true (sp ⊖ 12) +
        taddi + tjalr false ra
    , c').

Definition cached_sum_timing_invs
    (sp : N) (arr : addr) (c : cache) (t:trace) : option Prop :=
let size := 1000 in
match t with (Addr a, s) :: t' => match a with
| 0x210 => Some (s R_A0 = arr /\ s R_A1 = arr /\ s R_SP = sp /\
                    cycle_count_of_trace t' c = (0, c))
| 0x228 => Some (exists c1 c2,
                    s R_A0 = arr /\ s R_A1 = 1000 /\
                    s V_MEM32 Ⓓ[sp ⊖ 4] = s R_RA /\
                    cycle_count_of_trace t' c1 = 
                        (taddi + tsw false (sp ⊖ 12) + taddi + taddi + 
                        tsw false (sp ⊖ 4) + tsw false (sp ⊖ 8), c2))
| 0x250 => Some (exists c', time_of_cached_sum (s R_RA) sp size arr c c' t)
| _ => None end | _ => None end.

Theorem cached_sum_timing:
  forall s (t : trace) s' x' sp arr
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (SP: s R_SP = sp)
         (A0: s R_A0 = arr)
         (A1: s R_A1 = arr),
  satisfies_all 
    lifted_prog
    (cached_sum_timing_invs sp arr clear_cache)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.
    Local Ltac step := tstep r5_step.

    simpl. rewrite ENTRY. unfold entry_addr. step. 
    now repeat split.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL; 
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    destruct PRE as (A0 & A1 & SP & Cycles).
    - do 4 step. r5_step.

        Ltac generalize_timing_trace Heq TSI l a old_cache s t ::=
            idtac "generalize";
    let x := fresh "x" in
    let c := fresh "c" in
    remember ((Addr a, _) :: t) as l eqn:Heq;
    (* I promise this is necessary *)
    (* if instead eassert is used, it likes to try and *)
    (* fill in the hole on its own. *)
    evar (x : N);
    evar (c : cache);
    idtac "solving";
    assert (cycle_count_of_trace l old_cache = (x, c)) as TSI by (
        rewrite Heq, cycle_count_of_trace_cons; find_rewrites;
        cbv delta [cycle_count_of_trace];
        unfold_time_of_addr;
        psimpl; now subst x c
    ); subst x c.

    Ltac do_generalize ::=
    lazymatch goal with
    | [t: list (exit * store), 
        TSI: cycle_count_of_trace ?t ?old = (?x, ?c)
        |- nextinv _ _ _ _ (_ :: (Addr ?a, ?s) :: ?t)] =>
        idtac "hi";
        let Heq := fresh "Heq" in
        let H0 := fresh "TSI" in
        let l := fresh "tail" in
        generalize_timing_trace Heq H0 l a old s t;
        clear Heq TSI;
        try (clear t; rename l into t);
        rename H0 into TSI
    | _ => idtac
    end. do_generalize. cbv zeta in Cycles.
    r5_step. do_generalize.
        rewrite Heq, cycle_count_of_trace_cons.
        simpl. now subst x c.
        
Qed.

End TimingProof.
