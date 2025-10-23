Require Import RTOSDemo.
Require Import RISCVTiming.
Import RISCVNotations.
Require Import TimingAutomation.
Require Import Arith.

Module TimingProof (cpu: CPUTimingBehavior).

Module Program_vListInsert <: ProgramInformation.
    Definition entry_addr : N := 0x800023f0.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x80002428 => true
        | _ => false
    end | _ => false end.

    Definition binary := RTOSDemo.
End Program_vListInsert.

Module RISCVTiming := RISCVTiming cpu Program_vListInsert.
Module vListInsert := RISCVTimingAutomation RISCVTiming.
Import Program_vListInsert vListInsert.

Module p <: LinkedListParams.
  Definition w := 32.
  Definition e := LittleE.
  Definition dw := 4.
  Definition pw := 4.
  Global Transparent w e dw pw.
End p.
Module LL := Theory_RISCV.LinkedLists p.
Import LL.
Ltac psimpl_hook ::= psimpl.
Ltac gdep x := generalize dependent x.
Global Ltac Zify.zify_pre_hook ::= idtac.

Definition portMAX_DELAY := 2^32 - 1.

Definition time_of_vListInsert (mem : memory)
    (pxNewListItem : addr) (le_index : N) (t : trace) :=
  cycle_count_of_trace t =
    tlw + taddi + taddi +
    (if mem Ⓓ[pxNewListItem] =? portMAX_DELAY then (
      tfbne + tlw
    ) else (
      ttbne + le_index * (
        taddi + tlw + tlw + ttbgeu
      ) + taddi + tlw + tlw + tfbgeu + tjal
    )) + (
      tlw + 4 * tsw + tlw + tsw + taddi + tsw + tjalr
    ).

Definition insertion_index mem l le_node le_dist le_val new_val len :=
    exists gt_node gt_val,
    node_distance mem l le_node le_dist /\
    list_node_value mem le_node = Some le_val /\
    list_node_next mem le_node = Some gt_node /\
    list_node_value mem gt_node = Some gt_val /\
    gt_node <> NULL /\
    le_val <= new_val < gt_val /\
    gt_val <= portMAX_DELAY /\
    (le_dist < len)%nat /\
    (* all nodes below le_dist satisfy n.val <= new_val *)
    forall n d v,
        node_distance mem l n d ->
        list_node_value mem n = Some v ->
        ((d <= le_dist)%nat <-> v <= new_val).

Definition vListInsert_timing_invs (base_mem : memory)
    (pxList pxListHead pxNewListItem le_node sentry : addr) 
    (new_val le_val : N)
    (le_dist len : nat) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x800023f0 => Some (
    insertion_index base_mem pxListHead le_node le_dist le_val new_val len /\
    node_distance (s V_MEM32) pxListHead sentry (len - 1) /\
    list_node_value (s V_MEM32) sentry = Some portMAX_DELAY /\
    list_node_next (s V_MEM32) sentry = Some pxListHead /\
    s R_A0 = pxList /\ s R_A1 = pxNewListItem /\ s V_MEM32 = base_mem /\
    s V_MEM32 Ⓓ[pxNewListItem] = new_val /\
    pxList ⊕ 8 = sentry /\
    pxListHead <> NULL /\ len <> 0%nat /\
    sentry <> NULL /\
    cycle_count_of_trace t' = 0
  )
| 0x8000242c => Some (exists ctr nxt,
    insertion_index base_mem pxListHead le_node le_dist le_val new_val len /\
    node_distance (s V_MEM32) pxListHead sentry (len - 1) /\
    list_node_value (s V_MEM32) sentry = Some portMAX_DELAY /\
    (base_mem Ⓓ[pxNewListItem] =? portMAX_DELAY) = false /\
    pxListHead <> NULL /\ s V_MEM32 = base_mem /\
    s R_A1 = pxNewListItem /\ s R_A3 = new_val /\
    len <> 0%nat /\
    (ctr <= le_dist)%nat /\
    list_node_next (s V_MEM32) (s R_A4) = Some nxt /\
    node_distance base_mem pxListHead nxt ctr /\
    sentry <> NULL /\
    cycle_count_of_trace t' =
      tlw + taddi + taddi +
      ttbne + (N.of_nat ctr) * (
        taddi + tlw + tlw + ttbgeu
      )
  )
| 0x80002428 => Some (time_of_vListInsert base_mem
                    pxNewListItem (N.of_nat le_dist) t)
| _ => None end | _ => None end.

Lemma le_cases : forall n m,
    (n <= m -> n < m \/ n = m)%nat.
Proof. lia. Qed.

Lemma not_at_end_next : forall mem head len a dist,
    node_distance mem head NULL len ->
    node_distance mem head a dist ->
    (dist < len)%nat ->
    exists val, list_node_next mem a = Some val.
Proof.
    intros. unfold list_node_next. destruct a.
    - pose proof (node_distance_uniq _ _ _ _ _ H H0).
        subst. lia.
    - eexists. reflexivity.
Qed.

Lemma not_at_end_next' : forall mem head len a1 dist1 a2 dist2,
    node_distance mem head NULL len ->
    node_distance mem head a1 dist1 ->
    node_distance mem head a2 dist2 ->
    (dist2 < dist1 <= len)%nat ->
    exists val2, list_node_next mem a2 = Some val2.
Proof.
    intros. unfold list_node_next. destruct a2.
    - pose proof (node_distance_uniq _ _ _ _ _ H H1).
        subst. lia.
    - eexists. reflexivity.
Qed.

Lemma head_nonnull_impl_len_nonzero : forall mem head len,
    node_distance mem head NULL len ->
    head <> NULL ->
    len <> 0%nat.
Proof.
    intros. destruct len.
    - inversion H. contradiction.
    - discriminate.
Qed.

Lemma at_end_lens : forall mem head len a dst,
    head <> NULL ->
    node_distance mem head NULL len ->
    node_distance mem head a dst ->
    list_node_next mem a = Some NULL ->
    S dst = len.
Proof.
    intros. destruct a.
    - inversion H2.
    - pose proof (node_distance_len_nonzero _ _ _ H0).
        change NULL with LL.NULL in *.
        apply N.eqb_neq in H. rewrite H in H3.
        specialize (H3 ltac:(reflexivity)).
        pose proof distance_last_node.
        unfold LL.NULL in H4.
        specialize (H4 mem head (N.pos p) dst ltac:(lia) H1 H2).
        pose proof (node_distance_uniq _ _ _ _ _ H0 H4).
        now symmetry.
Qed.

Lemma Some_inv : forall (X : Type) (x y : X),
    Some x = Some y -> x = y.
Proof. intros. now inversion H. Qed.

Theorem node_dist_tri:
  forall mem a m z lenam lenaz, 
    (lenam <= lenaz)%nat ->
    node_distance mem a m lenam ->
    node_distance mem a z lenaz ->
  node_distance mem m z (lenaz-lenam)%nat.
Proof.
  intros. gdep lenam; gdep m. induction H1; intros.
    destruct lenam. inversion H0; simpl; now subst. lia.
    rename next into b, src into a, dst into z, len into lenbz.
    inversion H1; subst.
      destruct lenam. inversion H0; subst. simpl. econstructor; try eassumption.
        destruct lenam; try lia. inversion H0; subst. inversion LEN; subst. rewrite NEXT0 in NEXT; inversion NEXT; subst m. simpl; constructor.
      rename next into c; move b before mem; move c before b; move len before z; move lenam before len.
      move NEQ0 before NEQ; move m before z; move NEXT0 before NEXT.
      rename IHnode_distance into IH.
      inversion H0; subst.
        simpl. econstructor; eassumption.
        rewrite NEXT in NEXT1; inversion NEXT1; subst next; clear NEXT1; rename len0 into lenbm.
        assert (Help: (lenbm <= S len)%nat) by lia.
        specialize (IH _ _ Help LEN0).
        simpl in *. assumption.
Qed.

Theorem exist_node_le_dist:
  forall m src z len
    (D: node_distance m src z (S len)),
  forall l (H: (l <= S len)%nat), exists n, node_distance m src n l.
Proof.
  intros m src z len; gdep m; gdep src; gdep z; induction len; intros.
    destruct l;[exists src; econstructor|inversion D; subst]. destruct l; try lia; inversion LEN; subst; exists z; assumption.
    inversion D; subst. rename IHlen into IH; specialize (IH _ _ _ LEN).
    set (Nat.pred l) as predl. assert (Help: (predl <= S len)%nat) by lia.
    specialize (IH _ Help). destruct IH as [n D']. 
    destruct l;[exists src; econstructor| exists n].
    eapply DstSn; try eassumption. intro H0; subst n. simpl in predl; subst predl; move z before src; move l before len.
    enough (Help2:node_distance m src z (S len - l)%nat).
    pose proof (node_distance_uniq _ _ _ _ _ D Help2); lia.
    rename src into a, next into b.
    pose proof (node_dist_tri _ _ _ _ _ _ Help D' LEN).
    pose proof (node_distance_uniq _ _ _ _ _ H0 D).
    lia.
Qed.

Theorem node_dist_cycle_bound:
  forall m src last len innode inlen,
    node_distance m src last len ->
    list_node_next m last = Some src ->
    node_distance m src innode inlen ->
    (inlen <= len)%nat.
Proof.
  intros. destruct (Nat.le_ge_cases inlen len) as [Le | Ge]; try assumption.
  destruct (N.eq_dec last innode).
    subst innode. rewrite (node_distance_uniq _ _ _ _ _ H H1) in *. lia.
    pose proof (node_dist_tri _ _ _ _ _ _ Ge H H1).
    assert (node_distance m last innode (S inlen)).
      eapply DstSn; try eassumption.
      pose proof (node_distance_uniq _ _ _ _ _ H2 H3); lia.
Qed.

Lemma no_dist_from_null:
    forall mem node len, 
        node <> NULL ->
        ~ node_distance mem NULL node len.
Proof.
    intros. intro Contra. inversion Contra; subst.
        contradiction.
    inversion NEXT.
Qed.

Theorem next_node_inc_dist_or_same:
  forall len mem src dst n
    (D:node_distance mem src dst len)
    (NEXT: list_node_next mem dst = Some n),
  node_distance mem src n (S len) \/ src = n.
Proof.
    intros. induction D.
    - destruct (N.eq_dec node n). now right.
        left. econstructor. eassumption. assumption. constructor.
    - destruct (N.eq_dec src n). now right.
        left. econstructor; eauto. admit.
Admitted.

(* TODO: Charles, use this to prove the inductive loop invariant where the distance from head to the next node (a4?) 
   is S ctr. *)
Theorem node_dist_inc_nwf:
  forall m src dst dst' sentry len slen
    (LSD: node_distance m src dst len)
    (DST': list_node_next m dst = Some dst')
    (LSSen: node_distance m src sentry slen)
    (LT: (len < slen)%nat),
  node_distance m src dst' (S len).
Proof.
  intros. Check node_dist_tri.
  destruct (next_node_inc_dist_or_same _ _ _ _ _ LSD DST'); try assumption.
  subst dst'; exfalso.
  pose proof (node_dist_cycle_bound _ _ _ _ _ _ LSD DST' LSSen).
  lia.
Qed.

Theorem vListInsert_timing:
  forall s t s' x' base_mem len pxList pxListHead pxNewListItem le_node le_dist le_val sentry new_val
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models rvtypctx s)
         (* bindings *)
         (MEM: s V_MEM32 = base_mem)
         (A0: s R_A0 = pxList)
         (A1: s R_A1 = pxNewListItem)
         (* contents of pxNewListItem *)
         (VAL: s V_MEM32 Ⓓ[pxNewListItem] = new_val)
         (* pxListHead is non-null *)
         (L_NN: pxListHead <> NULL)
         (LEN: (0 < len)%nat)
         (* there is a sentry node *)
         (HD: 8 ⊕ pxList = sentry)
         (SENTRY: node_distance (s V_MEM32) pxListHead sentry (len - 1))
         (SENTRY_VAL: list_node_value (s V_MEM32) sentry = Some portMAX_DELAY)
         (SENTRY_NEXT: list_node_next (s V_MEM32) sentry = Some pxListHead)
         (SENTRY_NN: sentry <> NULL)
         (* there is an index to insert at *)
         (IDX: insertion_index base_mem pxListHead le_node le_dist le_val new_val len),
  satisfies_all
    lifted_prog
    (vListInsert_timing_invs base_mem pxList pxListHead pxNewListItem le_node sentry new_val le_val le_dist len)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    Local Ltac step := tstep r5_step.
    simpl. rewrite ENTRY. unfold entry_addr. repeat step.
    split. assumption. repeat split; auto. lia.

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply lift_riscv_welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 32 PRE.

    - destruct PRE as (IDX & SENTRY & SENTRY_VAL & SENTRY_NEXT & A0 & A1 & MEM & 
        NewVal & PXLH & NonNull & Len_Nz & SENTRY_NN & Cycles).
        do 4 step.
        -- exists 0%nat, pxListHead. split. assumption.
            repeat split; auto; try now rewrite <- MEM.
            unfold portMAX_DELAY. lia. lia.
            rewrite N.add_comm, PXLH, <- MEM. assumption.
            apply Dst0.
            hammer.
        -- repeat step. unfold portMAX_DELAY. hammer.
    - destruct PRE as (ctr & nxt & IDX & SENTRY & SENTRY_VAL & ValueValid & PXLH_NN & 
            MEM & A1 & A3 & Len_Nz & CtrMax & Nxt & CtrDist & S_NN & Cycles).
        repeat step.
        -- hammer.  replace ctr with le_dist. lia.
            destruct (le_cases ctr le_dist CtrMax); try lia.
            clear - IDX MEM Len_Nz Nxt CtrDist S_NN BC H.
            destruct IDX as (gt_node & gt_val & LeDist & LeVal & LeNextGt & GtVal & _ & Vals & _ & Lens & Sorted).
            exfalso.
            specialize (Sorted nxt ctr).
            unfold list_node_next in Nxt. destruct (s' R_A4). inversion Nxt.
            unfold p.w, p.e, p.pw, p.dw in Nxt. apply Some_inv in Nxt.
            rewrite MEM in Nxt.
            assert (exists v, list_node_value base_mem nxt = Some v) by admit.
            destruct H0 as (v & H0).
            specialize (Sorted v CtrDist H0).
            destruct Sorted. unfold list_node_value in H0.
            rewrite Nxt in BC. destruct nxt. inversion H0.
            apply Some_inv in H0. unfold p.w, p.e, p.dw in H0.
            subst v. specialize (H1 ltac:(lia)). lia.
        -- exists (S ctr). 
            assert (exists nxt', list_node_next base_mem nxt = Some nxt') by admit.
            destruct H as (nxt' & H). exists nxt'.
            split. assumption.
            destruct IDX as (gt_node & gt_val & LeDist & LeVal & LeNextGt & GtVal & GtNN & Vals & MaxVal & Lens & Sorted).
            repeat split; auto; try lia; try now rewrite <- MEM.
            destruct (le_cases ctr le_dist CtrMax). lia.
            rewrite N.ltb_ge in BC.
            remember (base_mem Ⓓ[ base_mem Ⓓ[ 4 + s' R_A4 ]]) as nxt'val.
            assert (Help1: node_distance base_mem pxListHead nxt' (S ctr)). {
                eapply node_dist_inc_nwf. eassumption. assumption.
                rewrite <- MEM. apply SENTRY. subst.
                admit. (* true but unsure how to prove *)
            }
            assert (Help2: list_node_value base_mem nxt' = Some nxt'val) by admit.
            specialize (Sorted _ _ _ Help1 Help2).
            subst le_dist. apply Sorted. assumption.
            rewrite MEM in *; clear MEM.
            destruct (s' R_A4). inversion Nxt. unfold list_node_next in Nxt.
                apply Some_inv in Nxt. unfold p.w, p.e, p.pw, p.dw in Nxt.
                rewrite Nxt. assumption.
            eapply node_dist_inc_nwf.
                eassumption. assumption. rewrite <- MEM. apply SENTRY.
                admit. (* same as above *)
            hammer.
Admitted.
