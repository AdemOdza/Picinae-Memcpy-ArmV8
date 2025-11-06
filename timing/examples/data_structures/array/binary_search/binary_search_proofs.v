Require Import binary_search.
Require Import RISCVTiming.
Import RISCVNotations.

Module TimingProof (cpu : RVCPUTimingBehavior).

Module Program_binary_search <: ProgramInformation.
    Definition entry_addr : N := 0x1e4.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x1f8 => true
        | _ => false
    end | _ => false end.

    Definition binary := binary_search.
End Program_binary_search.

Module RISCVTiming := RISCVTiming cpu Program_binary_search.
Module binary_searchAuto := RISCVTimingAutomation RISCVTiming.
Import Program_binary_search binary_searchAuto.

Definition key_in_array (mem : memory) (arr : addr) (key : N) (len : N) : Prop :=
    exists i, i < len /\ mem Ⓓ[arr + (i << 2)] = key.

Lemma lt_impl_lt_or_eq : forall x y,
    x < 1 + y -> x = y \/ x < y.
Proof. lia. Qed.

Definition N_peano_ind_Set (P : N -> Set) := N.peano_rect P.

Fixpoint key_in_array_dec (mem : memory) (arr : addr) (key len : N)
        : {key_in_array mem arr key len} + {~ key_in_array mem arr key len}.
    induction len using N_peano_ind_Set.
    - right. intro. destruct H as (idx & Contra & _). lia.
    - destruct IHlen as [IN | NOT_IN].
        -- left. destruct IN as (idx & Lt & Eq). exists idx.
            split. lia. assumption.
        -- destruct (N.eq_dec (mem Ⓓ[arr + (len << 2)]) key).
            + left. exists len. split. lia. assumption.
            + right. intro. destruct H as (idx & Lt & Eq).
                assert (idx = len). {
                destruct (lt_impl_lt_or_eq idx len). lia.
                    subst. reflexivity.
                exfalso. apply NOT_IN. exists idx. now split.
                } subst. contradiction.
Qed.

Definition mid (n : N) : N :=
    (n - 1) / 2.

Require Import Program.
Program Fixpoint found_steps (n i : N) (H: 0 < n) (H0: i < n) {measure (N.to_nat n)} : N :=
    match i ?= mid n with
    | Eq => 1
    | Lt => 1 + found_steps (mid n) i H H0
    | Gt => 1 + found_steps (n - mid n - 1) (i - mid n - 1) H H0
    end.
Obligation 1.
    unfold mid in *. clear found_steps.
    destruct n using N.peano_ind. lia.
    destruct n using N.peano_ind. simpl in Heq_anonymous.
        exfalso. eapply N.compare_0_r. now rewrite Heq_anonymous.
    clear IHn IHn0.
    repeat rewrite <- N.add_1_l in *.
    replace (1 + (1 + n) - 1) with (1 + n) in * by lia.
    destruct n using N.peano_ind. simpl in Heq_anonymous.
        exfalso. eapply N.compare_0_r. now rewrite Heq_anonymous.
    clear IHn.
    rewrite <- N.add_1_l in *. psimpl.
    replace ((1 + (1 + n)) / 2) with (1 + n / 2) by lia.
    destruct (3 + n) eqn:E0, (1 + n / 2) eqn:E1; try lia.
    reflexivity.
Qed.
Obligation 2.
    rewrite <- Heq_anonymous. now apply N.compare_lt_iff.
Qed.
Obligation 3.
    unfold mid in *. lia.
Qed.
Obligation 4.
    unfold mid in *. clear found_steps.
    destruct n using N.peano_ind. lia.
    destruct n using N.peano_ind. simpl. simpl in Heq_anonymous.
        change (0 / 2) with 0 in Heq_anonymous.
        destruct (i ?= 0) eqn:E. discriminate.
    discriminate. replace i with 0 in * by lia. discriminate.
    clear IHn IHn0. repeat rewrite <- N.add_1_l in *.
    destruct (1 + (1 + n)) eqn:E. lia.
    destruct (N.pos p - (N.pos p - 1) / 2 - 1) eqn:E0.
    lia. reflexivity.
Qed.
Obligation 5.
    symmetry in Heq_anonymous.
    rewrite N.compare_gt_iff in Heq_anonymous.
    rewrite <- N.compare_lt_iff in H0. rewrite H0.
    rewrite N.compare_lt_iff in H0.
    symmetry. rewrite N.compare_lt_iff. unfold mid. lia.
Qed.
Obligation 6. lia. Qed.

Definition time_of_binary_search (len : N) (found_idx : option N) (t : trace) :=
    min <= cycle_count_of_trace t <= max
    cycle_count_of_trace t =
        taddi + taddi + taddi +
        (* full loop iterations *)
        (match found_idx with
         | None => 
         | Some idx => 
            
         end) * (

        ) +
        (* partial loop iteration *)
        match found_idx with
        | None => tfbge + taddi + tjalr
        | Some idx => ttbge + tsub + tsrai + tadd + tslli 0x2 + 
                      tadd + tlw + taddi + ttbeq
        end.


Definition timing_postcondition (mem : memory) (arr : addr)
        (key : N) (len : N) (t : trace) : Prop :=
    (exists i, i < len /\ mem Ⓓ[arr + (i << 2)] = key /\
        (* i is the first index where the key is found *)
        (forall j, j < i -> mem Ⓓ[arr + (j << 2)] <> key) /\
        time_of_binary_search len (Some i) t) \/
    ((~ exists i, i < len /\ mem Ⓓ[arr + (i << 2)] = key) /\
        time_of_binary_search len None t).

Definition tbgeu (rs1 rs2 : N) : N :=
    if negb (rs1 <? rs2) then ttbgeu else tfbgeu.

Definition binary_search_timing_invs (s : store) (base_mem : memory)
    (sp : N) (arr : addr) (key : N) (len : N) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x1e4 => Some (s V_MEM32 = base_mem /\ s R_A0 = arr /\ s R_A1 = key /\ 
            s R_A2 = len /\ 4 * len <= 2^32 - 1 /\
            cycle_count_of_trace t' = 0)
| 0x1e8 => Some (
    s R_A0 = arr /\ s R_A1 = key /\ s R_A2 = len /\
    4 * len <= 2^32 - 1 /\
    (* preservation *)
    (forall i, i < len ->
        (s V_MEM32) Ⓓ[arr + (i << 2)] = base_mem Ⓓ[arr + (i << 2)]) /\
    (* haven't found a match yet *)
    (forall i, i < (s R_A5) ->
        (s V_MEM32) Ⓓ[arr + (i << 2)] <> key) /\
    (s R_A5) <= len /\
    cycle_count_of_trace t' =
        (* pre-loop time *)
        taddi +
        (* loop counter stored in register a5 *)
        (s R_A5) *
        (* full loop body length - can't have broken out by this address *)
        (tfbgeu + tslli 2 + tadd + tlw + tfbeq + taddi + tjal)
    )
| 0x208 => Some (timing_postcondition base_mem arr key len t)
| _ => None end | _ => None end.

Theorem binary_search_timing:
  forall s (t : trace) s' x' base_mem sp arr key len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = base_mem)
         (SP: s R_SP = sp)
         (A0: s R_A0 = arr)
         (A1: s R_A1 = key)
         (A2: s R_A2 = len)
         (* length must fit inside the address space, arr is 4-byte integers *)
         (LEN_VALID: 4 * len <= 2^32 - 1),
  satisfies_all 
    lifted_prog
    (binary_search_timing_invs s base_mem sp arr key len)
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

    (* 0x101b0 -> 0x101e0 *)
    destruct PRE as (Mem & A0 & A1 & A2 & LEN_VALID & Cycles).
    repeat step.
        repeat eexists; auto.
        (* preservation *) intros; now rewrite Mem.
        (* key not found yet *) intros; lia.
        (* idx <= len *) psimpl; lia.
        (* cycles *) hammer.

    destruct PRE as (A0 & A1 & A2 & LEN_VALID & Preserved &
        NotFound & A5_LEN & Cycles).
    destruct (key_in_array_dec (s' V_MEM32) arr key len) as [IN | NOT_IN].
    (* There is a matching element in the array *) {
        step. repeat step.
        (* postcondition, match found *)
            left. exists (s' R_A5). split.
                now apply N.ltb_lt. 
            split.
                rewrite <- Preserved. now apply N.eqb_eq in BC0.
                now apply N.ltb_lt in BC. 
            split.
                intros. rewrite <- Preserved by lia. now apply NotFound.
            unfold time_of_binary_search.
            hammer.
        (* loop invariant after going around *)
            apply N.ltb_lt in BC. apply N.eqb_neq in BC0.
            repeat split; auto.
            (* key not found *)
            intros.
                rewrite N.mod_small in H by lia.
                apply lt_impl_lt_or_eq in H. destruct H.
                    now subst.
                    now apply NotFound.
            (* 1 + a5 <= len *)
            rewrite N.mod_small by lia. lia.
            (* cycles *)
            rewrite (N.mod_small (1 + s' R_A5)). hammer.
                apply N.le_lt_trans with len; lia.
        (* iterated len times - contradiction *)
        exfalso. destruct IN as (idx & IDX_LEN & IN).
            apply (NotFound idx). apply N.ltb_ge in BC. lia.
            assumption.
    }

    (* There is not a matching element in the array *) {
        step.
        do 4 step.
        (* contradiction - BC0 says a match has been found *)
            exfalso. apply NOT_IN. exists (s' R_A5). 
            split. now apply N.ltb_lt.
            apply N.eqb_eq in BC0.
            assumption.
        (* a match has not been found, continue *)
        repeat step.
        (* postcondition, match found *)
            apply N.ltb_lt in BC. apply N.eqb_neq in BC0.
            repeat split; auto.
            (* key not found *)
            intros.
                rewrite N.mod_small in H by lia.
                apply lt_impl_lt_or_eq in H. destruct H.
                    now subst.
                    now apply NotFound.
            (* 1 + a5 <= len *)
            rewrite N.mod_small by lia. lia.
            (* cycles *)
            rewrite (N.mod_small (1 + s' R_A5)). hammer.
            apply N.le_lt_trans with len; lia.
        (* a match has not been found, break and return *)
        repeat step.
            unfold time_of_binary_search. right.
            split. intro. apply NOT_IN. destruct H as (idx & IDX_LEN & IN).
            exists idx. split. assumption. now rewrite Preserved.
            replace (s' R_A5) with len in * by
                (rewrite N.ltb_ge in BC; lia).
            hammer.
    }
Qed.

End TimingProof.
