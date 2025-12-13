Require Import Utf8.
Require Import FunctionalExtensionality.
Require Import Arith.
Require Import NArith.
Require Import ZArith.
Require Import Lia.
Require Import Bool.
Require Import Picinae_armv8_pcode.
Require Import memcpy_lo_memcpy_armv8.

Import ARM8Notations.
Open Scope N.
Open Scope bool.

Theorem memcpy_nwc: 
	forall s2 s1, memcpy_lo_memcpy_armv8 s1 = memcpy_lo_memcpy_armv8 s2.
Proof.
	reflexivity.
Qed.

Theorem memcpy_welltyped: 
	welltyped_prog arm8typctx memcpy_lo_memcpy_armv8.
Proof.
  Picinae_typecheck.
Qed.

Definition program_exit (t:trace) :=
  match t with
  | (Addr a, _) :: _ =>
      match a with
      | 0x100188 
      | 0x1000f8 
      | 0x100088 
      | 0x100064 
      | 0x100048 
      | 0x100030 
      | 0x1000b8 => true   (* ret instructions *)
      | _ => false
      end
  | _ => false
end.

Definition filled m dest src len :=
  N.recursion m (fun i m' => m'[Ⓑ dest + i := m Ⓑ[src + i]]) len.
  
Section Invariants.
  Variable mem : memory    (* initial memory state *).

  Variable dest : N        (* memcpy: 1st pointer arg (R_X0), destination address *).
  Variable src : N        (* memcpy: 2nd pointer arg (R_X1), source address *).
  Variable len : N        (* memcpy: 2nd pointer arg (R_X2), byte count *).
  
  (* Registers state after copying k bytes *)
  Definition memcpy_regs (s : store) k :=
    s V_MEM64 = filled mem dest src k /\
    s R_X0 = dest /\
    s R_X1 = src /\
    s R_X2 = (len - k).

  (* Loop invariant: k bytes copied so far *)
  Definition memcpy_inv (s : store) (k : N)  :=
    k <= len /\
    memcpy_regs s k.

  Definition bounds_safe :=
    dest + len < 2^64 /\ src + len < 2^64 /\ len < 2^64.

Definition memcpy_invset' (t : trace) : option Prop :=
  match t with
  | (Addr a, s) :: _ =>
      match a with

      (* Entry point *)
      | 0x100000 => Some (memcpy_regs s 0)

      (* Loop 1 (1-byte writes to word boundary) *)
      | 0x100130 => Some (exists mem k, s V_MEM64 = filled mem dest src k)

      (* post-condition: *)
      | 0x100188 
      | 0x1000f8 
      | 0x100088 
      | 0x100064 
      | 0x100048 
      | 0x100030 
      | 0x1000b8 => Some (exists mem, s V_MEM64 = filled mem dest src len)

      | _ => None
      end
  | _ => None
  end.


End Invariants.


Lemma filled0: ∀ m p c, filled m p c 0 = m.
Proof.
  intros. reflexivity.
Qed.

 
Lemma filled_succ:
  ∀ m dest source k, (filled m dest source k)[Ⓑdest+k:= m Ⓑ[source + k]] = filled m dest source (N.succ k).
Proof.
  intros. unfold filled. rewrite N.recursion_succ; try reflexivity.
   intros i j H m1 m2 H'. subst. reflexivity.
Qed.

Lemma filled_mod : ∀ m dest src len,
  filled m dest src len = 
  N.recursion m (fun i m' => m'[Ⓑ dest + i := m Ⓑ[src + i]]) len.
Proof.
  intros m dest src len.
  unfold filled.
  reflexivity.
Qed.

Lemma filled_add : ∀ n m dest src k,
  filled m dest src (k + n) =
  N.recursion (filled m dest src k)
    (fun i m' => m'[Ⓑ dest + k + i := m Ⓑ[src + k + i]]) n.
Proof.
  intros n m dest src k.
  induction n using N.peano_ind; simpl.
  - rewrite N.add_0_r. reflexivity.
  - 
    rewrite N.add_succ_r.
    rewrite <- (filled_succ m dest src (k + n)).
    rewrite IHn.
    repeat rewrite N.add_assoc.
    rewrite N.recursion_succ; try reflexivity.
    intros i j H m1 m2 H'. subst. reflexivity.
Qed.

Lemma filled4:
  ∀ m dest src k,
    filled m dest src (k + 4) =
    N.recursion (filled m dest src k)
      (fun i m' => m'[Ⓑ dest + k + i := m Ⓑ[src + k + i]]) 4.
Proof.
  intros. 
  apply (filled_add 4 m dest src k).
Qed.

Lemma filled8:
  ∀ m dest src k,
    filled m dest src (k + 8) =
    N.recursion (filled m dest src k)
      (fun i m' => m'[Ⓑ dest + k + i := m Ⓑ[src + k + i]]) 8.
Proof.
  intros. 
  apply (filled_add 8 m dest src k).
Qed.

Lemma filled16 :
  ∀ m dest src k,
    filled m dest src (k + 16) =
    N.recursion (filled m dest src k)
      (fun i m' => m'[Ⓑ dest + k + i := m Ⓑ[src + k + i]]) 16.
Proof.
  intros. apply (filled_add 16 m dest src k).
Qed.

Lemma filled3:
  ∀ m dest src,
    filled m dest src 3 =
    m[Ⓑ dest := m Ⓑ[src]][Ⓑ dest + 1 := m Ⓑ[src + 1]][Ⓑ dest + 2 := m Ⓑ[src + 2]].
Proof.
  intros.
  replace 3 with (0 + 3) by reflexivity.
  rewrite (filled_add 3 m dest src 0).
  rewrite filled0.
  unfold N.recursion.
  simpl.
  repeat rewrite N.add_0_l.
  repeat rewrite N.add_0_r.
  reflexivity.
Qed.

Lemma filled3_pattern:
  ∀ m dest src len,
    len = 3 ->
    filled m dest src len =
    m[Ⓑ dest := m Ⓑ[src]][Ⓑ dest + (len >> 1) := m Ⓑ[src + (len >> 1)]][Ⓑ dest ⊖ 1 + len := m Ⓑ[src ⊖ 1 + len]].
Proof.
  intros m dest src len Hlen.
  subst len.
  rewrite filled3.
  psimpl.
  reflexivity.
Qed.
Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Lia.


Lemma four_bytes_to_dword:
  ∀ m dest src,
    m[Ⓑ dest := m Ⓑ[src]][Ⓑ dest + 1 := m Ⓑ[src + 1]][Ⓑ dest + 2 := m Ⓑ[src + 2]][Ⓑ dest + 3 := m Ⓑ[src + 3]] =
    m[Ⓓ dest := m Ⓓ[src]].
Proof.
  intros.
  rewrite (setmem_merge 64 LittleE 1 1).
  rewrite (setmem_merge 64 LittleE 2 1).  
  rewrite (setmem_merge 64 LittleE 3 1).
  f_equal.
  replace 4 with (1+1+1+1) by reflexivity.
  rewrite (getmem_split 64 LittleE 1 3).
  rewrite (getmem_split 64 LittleE 1 2).
  rewrite (getmem_split 64 LittleE 1 1).
  simpl.
  (* how cbits constructions match ???*)

Admitted.

Lemma filled_4_to_dword:
  ∀ m dest src,
    m[Ⓑ dest := m Ⓑ[src]][Ⓑ dest + 1 := m Ⓑ[src + 1]][Ⓑ dest + 2 := m Ⓑ[src + 2]][Ⓑ dest + 3 := m Ⓑ[src + 3]] = 
    m[Ⓓ dest := m Ⓓ[src]][Ⓓ dest := m Ⓓ[src]].
Proof.
  intros.
  rewrite <- four_bytes_to_dword.
  psimpl.
  rewrite (N.add_comm 1 dest).
  rewrite (N.add_comm 2 dest).
  rewrite (N.add_comm 3 dest).
  rewrite (N.add_comm 1 src).
  rewrite (N.add_comm 2 src).
  rewrite (N.add_comm 3 src).
  apply four_bytes_to_dword.
Qed.

Lemma filled_5_to_dword:
  ∀ m dest src,
    m[Ⓑ dest := m Ⓑ[src]][Ⓑ dest + 1 := m Ⓑ[src + 1]][Ⓑ dest + 2 := m Ⓑ[src + 2]][Ⓑ dest + 3 := m Ⓑ[src + 3]][Ⓑ dest + 4 := m Ⓑ[src + 4]] = 
    m[Ⓓ dest := m Ⓓ[src]][Ⓓ dest + 1 := m Ⓓ[src + 1]].
Proof.
  intros.
  (* 5 consecutive byte writes at dest..dest+4 equal:
     1 dword write at dest (covers dest..dest+3)
     1 dword write at dest+1 (covers dest+1..dest+4)
     The overlapping bytes at dest+1..dest+3 are overwritten by the second dword. *)
Admitted.

Lemma filled_6_to_dword:
  ∀ m dest src,
    m[Ⓑ dest := m Ⓑ[src]][Ⓑ dest + 1 := m Ⓑ[src + 1]][Ⓑ dest + 2 := m Ⓑ[src + 2]][Ⓑ dest + 3 := m Ⓑ[src + 3]][Ⓑ dest + 4 := m Ⓑ[src + 4]][Ⓑ dest + 5 := m Ⓑ[src + 5]] = 
    m[Ⓓ dest := m Ⓓ[src]][Ⓓ dest + 2 := m Ⓓ[src + 2]].
Proof.
  intros.
  (* 6 consecutive byte writes at dest..dest+5 equal:
     1 dword write at dest (covers dest..dest+3)
     1 dword write at dest+2 (covers dest+2..dest+5)
     The overlapping bytes at dest+2..dest+3 are overwritten by the second dword. *)
Admitted.

Lemma filled_7_to_dword:
  ∀ m dest src,
    m[Ⓑ dest := m Ⓑ[src]][Ⓑ dest + 1 := m Ⓑ[src + 1]][Ⓑ dest + 2 := m Ⓑ[src + 2]][Ⓑ dest + 3 := m Ⓑ[src + 3]][Ⓑ dest + 4 := m Ⓑ[src + 4]][Ⓑ dest + 5 := m Ⓑ[src + 5]][Ⓑ dest + 6 := m Ⓑ[src + 6]] = 
    m[Ⓓ dest := m Ⓓ[src]][Ⓓ dest + 3 := m Ⓓ[src + 3]].
Proof.
  intros.
  (* 7 consecutive byte writes at dest..dest+6 equal:
     1 dword write at dest (covers dest..dest+3)
     1 dword write at dest+3 (covers dest+3..dest+6)
     The overlapping byte at dest+3 is overwritten by the second dword. *)
Admitted.


Lemma filled_overlap_4bytes:
  ∀ m dest src len,
    4 <= len < 8 ->
    filled m dest src len =
    m[Ⓓ dest := m Ⓓ[src]][Ⓓ dest ⊖ 4 + len := m Ⓓ[src ⊖ 4 + len]].
Proof.
  intros m dest src len [Hge Hlt].
  assert (len = 4 \/ len = 5 \/ len = 6 \/ len = 7) as Hcases by lia.
  destruct Hcases as [H4|[H5|[H6|H7]]]; subst len.
  - (* len = 4 *)
    replace 4 with (0 + 4) at 1 by reflexivity.
    rewrite (filled_add 4 m dest src 0).
    rewrite filled0.
    unfold N.recursion. simpl.
    repeat rewrite N.add_0_l. repeat rewrite N.add_0_r.
    rewrite <- four_bytes_to_dword.
    psimpl.
    rewrite (N.add_comm 1 dest).
    rewrite (N.add_comm 2 dest).
    rewrite (N.add_comm 3 dest).
    rewrite (N.add_comm 1 src).
    rewrite (N.add_comm 2 src).
    rewrite (N.add_comm 3 src).
    apply four_bytes_to_dword.
  - (* len = 5 *)
    replace 5 with (0 + 5) at 1 by reflexivity.
    rewrite (filled_add 5 m dest src 0).
    rewrite filled0.
    unfold N.recursion. simpl.
    repeat rewrite N.add_0_l. repeat rewrite N.add_0_r.
    psimpl.
    repeat rewrite (N.add_comm _ dest).
    repeat rewrite (N.add_comm _ src).
    apply filled_5_to_dword.
  - (* len = 6 *)
    replace 6 with (0 + 6) at 1 by reflexivity.
    rewrite (filled_add 6 m dest src 0).
    rewrite filled0.
    unfold N.recursion. simpl.
    repeat rewrite N.add_0_l. repeat rewrite N.add_0_r.
    psimpl.
    repeat rewrite (N.add_comm _ dest).
    repeat rewrite (N.add_comm _ src).
    apply filled_6_to_dword.
  - (* len = 7 *)
    replace 7 with (0 + 7) at 1 by reflexivity.
    rewrite (filled_add 7 m dest src 0).
    rewrite filled0.
    unfold N.recursion. simpl.
    repeat rewrite N.add_0_l. repeat rewrite N.add_0_r.
    psimpl.
    repeat rewrite (N.add_comm _ dest).
    repeat rewrite (N.add_comm _ src).
    apply filled_7_to_dword.
  Qed.
(*
Lemma inv_1byte_init :
  forall dest src len s m,
    len < 4 ->
    common_inv  0 dest src len s m 0->
    inv_1byte 0 dest src len s m.
Proof.
  intros. unfold inv_1byte. auto.
Qed.
*)

(*Lemma checked_add_true:
  ∀ n k len (KLEN: k <= len) (LEN32: len < 2^32) (BC: (n <=? len ⊖ k) = true),
  k + n <= len.
Proof.
  intros.
  rewrite N.add_comm. rewrite <- (N.sub_add _ _ KLEN). apply N.add_le_mono_r.
  rewrite <- (N.mod_small _ _ LEN32). rewrite <- (N.mod_small k (2^32)).
    rewrite <- msub_nowrap.
      apply N.leb_le, BC.
      rewrite (N.mod_small _ _ LEN32). etransitivity. apply mp2_mod_le. apply KLEN.
    eapply N.le_lt_trans; eassumption.
Qed.*)
Require Import NArith.


Theorem memcpy_partial_correctness:
  forall s dest src len mem t s' x' k
    (ENTRY: startof t (x', s') = (Addr 0x100000,s))
    (MDL: models arm8typctx s)
    (MEM: s V_MEM64 = mem)
    (R0: s R_X0 = dest)
    (R1: s R_X1 = src)
    (R2: s R_X2 = len)
    (BOUNDS_DEST: dest + len < 2^64)
    (BOUNDS_SRC : src + len < 2^64)
    (DIST: (dest + len < src) \/ (src + len < dest))
    (K_lim: 0 <= k <= len),
    satisfies_all memcpy_lo_memcpy_armv8
    (memcpy_invset' mem dest src len)
    program_exit
    ((x', s')::t).
Proof.

  Local Ltac step := time arm8_step.
  
  intros. apply prove_invs.
  (* Base case: entry invariant *)
  simpl. rewrite ENTRY. step.
  repeat split; try assumption.
  intros. 
  
  destruct_inv 64 PRE.
  erewrite startof_prefix in ENTRY; try eassumption. 
  destruct PRE as [MEM' [R0' [R1' R2']]].
  step. step. step. step.
  step. step. step. step.
  step. step. step. step.
  
  - rewrite filled0 in MEM'.
  rewrite filled0. exists mem. symmetry. rewrite <- (N.sub_add 8 len) at 1.
  rewrite filled8. admit.
  (*solve for length being greater than 8*)
  apply N.leb_le in BC1. lia.
  - step. step. step. apply N.eqb_eq in BC4. exists mem. rewrite BC4. exact MEM'.
  step. step. step. step. step. step. step. 
  exists mem. symmetry.
  assert (len = 3) as Hlen by admit.
  rewrite filled3_pattern by exact Hlen.
  reflexivity.
  
  step. step. step. step. 
  exists mem. rewrite filled0.
  symmetry.
  apply filled_overlap_4bytes.
  admit.
  
  - step. step. step. step. step. step. step. step. step. step.  admit.
  step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. admit.
  step. step. step. step. step. step. admit.
  
  - step. step. step. step. step. step. step. step. step. step. step. step. admit.
  step. step. step. step. step. step. step. step. step. step. step. step. admit.
  
  - step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. admit.
  admit.
 
   
Admitted.
 
  