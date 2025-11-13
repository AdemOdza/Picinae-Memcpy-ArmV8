Require Import find_in_list_lifted.
Require Import AMD64Timing.
Import X64Notations.
Require Import TimingAutomation.
Require Import Arith.


(** Eliminate the store by rewriting the expressions stored in registers and
    inferring their bounds from the type context. *)
Global Ltac elimstore :=
  repeat lazymatch goal with
  | [ H: ?s ?v = _, MDL: models ?typs ?s |- _] =>
      let Hyp := fresh "SBound" in
      pose proof (Hyp:=models_var v MDL); cbv -[N.lt N.pow] in Hyp;
      (** Keep limit if bitwidth is small; if it is large lia will hang. *)
      match type of Hyp with
      | _ < 2 ^ ?w => assert (temp:(w <=? 256) = true) by reflexivity; clear temp
      | _ => clear Hyp
      end;
  try rewrite H in *; clear H; try clear s MDL
  end.

Module TimingProof (cpu : amd64CPUTimingBehavior).
Import cpu.

Module Program_find_in_list <: ProgramInformation.
  Definition entry_addr : N := 0x0.

    Definition exits (t:trace) : bool :=
        match t with (Addr a,_)::_ => match a with
        | 0x1f => true
        | 0x23 => true
        | _ => false
  end | _ => false end.

    Definition lifted_prog := linked_list_find_in_list_amd64.

    Definition time_of_addr (s : store) (a : addr) : N :=
        match a with
          | 0x0 => jmp_addr
          (* fix lift *)
          (*         16: CMP ESI,dword ptr [RDI] *)
          | 0x10 => cmp_r64_m64
          (*         18: JZ 0x00101330 *)
          | 0x12 => jz_addr
          (*         20: MOV RDI,qword ptr [RDI + 0x8] *)
          | 0x14 => mov_r64_m64
          (*          0: TEST RDI,RDI *)
          | 0x18 => test_r64_r64
          (*          3: JNZ 0x00101320 *)
          | 0x1B => jnz_addr
          (*          5: XOR EAX,EAX *)
          | 0x1D => xor_r32_r32
          (*          7: RET *)
          | 0x1F => ret
          (*          8: MOV RAX,RDI *)
          | 0x20 => mov_r64_r64
          (*         11: RET *)
          | 0x23 => ret
          | _ => time_inf
        end.

End Program_find_in_list.

Module AMD64Timing := AMD64Timing cpu Program_find_in_list.
Module find_in_list := AMD64TimingAutomation AMD64Timing.
Import Program_find_in_list find_in_list.

Module p <: LinkedListParams.
  Definition w := 64.
  Definition e := LittleE.
  Definition dw := 4.
  Definition dwb := 4.
  Definition pw := 8.
  Global Transparent w e dw pw.
End p.
Module LL := Theory_amd64.LinkedLists p.
Import LL.
Ltac psimpl_hook ::= psimpl.
Ltac gdep x := generalize dependent x.
Global Ltac Zify.zify_pre_hook ::= elimstore; unfold msub in *; llunfold.

Definition time_of_find_in_linked_list
        (len : nat) (found_idx : option nat) (t : trace) :=
    cycle_count_of_trace t =
    jmp_addr + test_r64_r64 + jnz_addr +
        match found_idx with
        | None =>
            N.of_nat len
        | Some idx =>
            N.of_nat idx
        end * (
        test_r64_r64 + jnz_addr + cmp_r64_m64 + jz_addr + mov_r64_m64
        ) + (match found_idx with
            | None =>
                xor_r32_r32
            | Some _ =>
                mov_r64_r64 + cmp_r64_m64 + jz_addr
            end) + ret.

Definition timing_postcondition (mem : memory) 
    (head : addr) (key : N) (len : nat) (t : trace) : Prop :=
  (exists loc, 
    key_in_linked_list mem head key loc /\ 
    time_of_find_in_linked_list len (Some loc) t)
  \/
  ((~ exists loc, (loc < len)%nat /\
    key_in_linked_list mem head key loc) /\ 
    time_of_find_in_linked_list len None t).

Definition find_in_linked_list_timing_invs (s : store)
    (sp : N) (head : addr) (key : N) (len : nat) (t:trace) : option Prop :=
match t with (Addr a, s) :: t' => match a with
| 0x0 => Some (exists mem, 
    s V_MEM64 = mem /\ s R_RDI = head /\
    s R_RSI mod 2 ^ 32 = key /\
    node_distance mem head NULL len /\
    cycle_count_of_trace t' = 0
  )
| 0x1b => Some (exists ctr mem curr,
    s V_MEM64 = mem /\ s R_RDI = curr /\
    (if s R_ZF =? 1 then s R_RDI = 0 else s R_RDI <> NULL) /\
    s R_RSI mod 2 ^ 32 = key /\
    (curr =? 0) =(s R_ZF =? 1)/\
    node_distance mem head curr ctr /\
    node_distance mem head NULL len /\
    (ctr <= len)%nat /\
    (forall i, (i < ctr)%nat -> ~ key_in_linked_list mem head key i) /\
    (forall fuel, key_in_linked_list mem head key fuel -> (ctr <= fuel)%nat) /\
    (cycle_count_of_trace t' = 
        jmp_addr + test_r64_r64 +
        N.of_nat ctr  * (
        cmp_r64_m64 + test_r64_r64 + jnz_addr + jz_addr + mov_r64_m64
        )
    )
  )
(* ret *)
| 0x1f => Some (timing_postcondition (s V_MEM64) head key len t)
(* ret *)
| 0x23 => Some (timing_postcondition (s V_MEM64) head key len t)
| _ => None end | _ => None end.

Lemma node_distance_same_len : forall mem h p1 p2 len,
  node_distance mem h p1 len ->
  node_distance mem h p2 len ->
  p1 = p2.
Proof.
  intros. induction H.
  - now inversion H0.
  - inversion H0; subst; clear H0.
    rewrite NEXT0 in NEXT. inversion NEXT; subst; clear NEXT.
    apply IHnode_distance, LEN.
Qed.

Lemma le_cases : forall n m,
    (n <= m -> n < m \/ n = m)%nat.
Proof. lia. Qed.

(*
Lemma curr_not_in : forall mem head curr ctr key,
  node_distance mem head curr ctr ->
  (curr =? 0) = false ->
  (mem Ⓓ[curr] =? key) = false ->
  ~ key_in_linked_list mem head key ctr.
Proof.
  intros. destruct (key_in_linked_list_dec mem head key ctr).
    pose proof (key_in_linked_list_value_equal _ _ _ _ _
                  k H).
    unfold list_node_value in H2.
    destruct curr. inversion H0.
    inversion H2; subst.
      rewrite N.eqb_refl in H1. inversion H1.
    assumption.
Qed.
 *)

Theorem find_in_linked_list_timing:
  forall s t s' x' sp head key len
         (* boilerplate *)
         (ENTRY: startof t (x',s') = (Addr entry_addr, s))
         (MDL: models x64typctx s)
         (* bindings *)
         (P0: s R_RDI = head)
         (P1: s R_RSI mod 2 ^ 32 = key)
         (* list length is finite *)
         (LEN: node_distance (s V_MEM64) head NULL len),
  satisfies_all
    lifted_prog
    (find_in_linked_list_timing_invs s sp head key len)
    exits
  ((x',s')::t).
Proof using.
    intros.
    apply prove_invs.

    Local Ltac step := tstep x64_step.
    simpl. rewrite ENTRY. unfold entry_addr. step.
    repeat (reflexivity || eexists || eassumption || split).

    intros.
    eapply startof_prefix in ENTRY; try eassumption.
    eapply preservation_exec_prog in MDL;
        try eassumption; [idtac|apply welltyped].
    clear - ENTRY PRE MDL. rename t1 into t. rename s1 into s'.

    destruct_inv 64 PRE.

    destruct PRE as (mem & MEM & Head & DstCurr & Len & Cycles).

    step. step. exists O; repeat (eexists || eassumption || reflexivity || split || hammer).
    destruct head; simpl; (reflexivity || intro; discriminate).
    destruct head; reflexivity.
    constructor.

    destruct PRE as (ctr & mem & curr & MEM & CURR & ZFRDI & P1 & ZF & DstCurr & Len &
                      CtrLen & NotIn & In & Cycles).
    step. 
    1-2: pose proof (H:=models_var R_ZF MDL); cbv [archtyps x64typctx] in H;
      destruct (s' R_ZF); try replace p with xH in * by lia; try discriminate; simpl in ZF;
      try rewrite N.eqb_eq in ZF; try rewrite N.eqb_neq in ZF. simpl in ZFRDI.

    simpl in BC. step; cycle 1. { right.
      (* Address 31 (0x1F): return NULL because the key is missing. *)
    clear H p; simpl in ZF; symmetry in ZF; subst curr.
    elimstore. rewrite (node_distance_uniq DstCurr Len) in *; clear CtrLen.
    { inversion Len; subst. split.
      intros H; destruct H as (loc & H2 & H3). lia.
      unfold time_of_find_in_linked_list. hammer.
      split. intro. destruct H as (loc & B & InLoc). apply (NotIn loc); assumption.
      unfold time_of_find_in_linked_list. hammer.
    }
    }
    simpl in ZFRDI.

    step. step. step. {
      (* Addr 35 (0x23): found key. *)
      left. exists ctr. repeat (eassumption || split).
      Search key_in_linked_list.
      rewrite P1 in *.
      intros. eapply key_at_ctr; try eassumption. destruct curr; simpl; try contradiction.
      rewrite N.eqb_eq in BC0; rewrite BC0. Unset Printing Notations. unfold p.w, p.e, p.dw. reflexivity.
      unfold time_of_find_in_linked_list; hammer.
    }

    step. step. {
      (* Addr 24 (0x18): inductive loop case *)
      exists (S ctr); repeat (eexists || eassumption || reflexivity || split).
      destruct (getmem _ _ _ _ (8+curr)) eqn:Eq. reflexivity. simpl. intro; discriminate.
      destruct (getmem _ _ _ _ (8+curr)) eqn:Eq. reflexivity. simpl. reflexivity.
      apply node_distance_next_S_len with (dst:=curr).
      destruct curr; try contradiction; unfold list_node_next, p.w, p.e, p.pw, p.dw, p.dwb. reflexivity.
      eapply distance_null_imp_well_formed; eassumption.
      eassumption.
      simpl in ZFRDI.
      Check ctr_le_len_step.
      eapply ctr_le_len_step; eassumption.
      intros; destruct (Nat.lt_trichotomy i ctr) as [Lt | [Eq | Gt]]; (lia || (now apply NotIn) || subst i).
      intro. (* TODO: make a theorem for this typical case? *)
      pose proof (Help:=key_in_linked_list_value_equal _ _ _ _ _ H1 DstCurr). destruct curr; try contradiction; injection Help; intros.
      rewrite P1, H2, N.eqb_neq in BC0. contradiction.
      intros. rewrite CURR, P1 in *; clear MEM CURR P1. rewrite N.eqb_neq in BC0.
      destruct (Nat.lt_trichotomy ctr fuel) as [Lt | [Eq | Gt]]; try lia; try subst fuel.
      pose proof (Help:=key_in_linked_list_value_equal _ _ _ _ _ H0 DstCurr). destruct curr; try contradiction; injection Help; intros. rewrite H1 in BC0. contradiction.
      specialize (NotIn _ Gt). contradiction.
      hammer.
    }

    rewrite CURR in *. replace p0 with xH in * by lia; clear H. simpl in BC. discriminate.
Qed.
End TimingProof.

Require Import i5_7300u.
Module i5_7300u_llfind := TimingProof i5_7300u.

Goal forall (len : nat) (found_idx : option nat) (t : trace),
    i5_7300u_llfind.time_of_find_in_linked_list len found_idx t =
    (i5_7300u_llfind.find_in_list.cycle_count_of_trace t =
      47 +
      match found_idx with
      | Some idx => N.of_nat idx
      | None => N.of_nat len
      end * 99 + match found_idx with
                    | Some _ => 47
                    | None => 1
                    end).
    intros.
    unfold i5_7300u_llfind.time_of_find_in_linked_list. simpl.
    unfold i5_7300u.ret, i5_7300u.mov_m64_r64, i5_7300u.xor_r32_r32.
    psimpl. reflexivity.
Qed.
