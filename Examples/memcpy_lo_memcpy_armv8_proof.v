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

Lemma filled_8_to_qword:
  ∀ m dest src,
    m[Ⓑ dest := m Ⓑ[src]] [Ⓑ dest + 1 := m Ⓑ[src + 1]]
     [Ⓑ dest + 2 := m Ⓑ[src + 2]] [Ⓑ dest + 3 := m Ⓑ[src + 3]]
     [Ⓑ dest + 4 := m Ⓑ[src + 4]] [Ⓑ dest + 5 := m Ⓑ[src + 5]]
     [Ⓑ dest + 6 := m Ⓑ[src + 6]] [Ⓑ dest + 7 := m Ⓑ[src + 7]] =
    m[Ⓠ dest := m Ⓠ[src]].
Proof.
  intros.
  (*combine consecutive byte writes into a quadword *)
  rewrite (setmem_merge 64 LittleE 1 1).
  rewrite (setmem_merge 64 LittleE 2 1).
  rewrite (setmem_merge 64 LittleE 3 1).
  rewrite (setmem_merge 64 LittleE 4 1).
  rewrite (setmem_merge 64 LittleE 5 1).
  rewrite (setmem_merge 64 LittleE 6 1).
  rewrite (setmem_merge 64 LittleE 7 1).
  f_equal.
(* 8 bytes is equivalent to one quad:
unfold Ⓠ to its getmem definition, and then unfold that, but its opaque?*)

Admitted.

Lemma filled_16_to_2qwords:
  ∀ m dest src,
    filled m dest src 16 =
    m[Ⓠ dest := m Ⓠ[src]]
     [Ⓠ 8 + dest := m Ⓠ[8 + src]].
Proof.
  intros.
  (* Use filled_add to split*)
  replace 16 with (8 + 8) by reflexivity. rewrite (filled_add 8 m dest src 8).
  
  (* Convert first 8 bytes to qword *)
  assert (filled m dest src 8 = m[Ⓠ dest := m Ⓠ[src]]) as H_first_8.
  {
    replace 8 with (0 + 8) at 1 by reflexivity. rewrite (filled_add 8 m dest src 0).
    rewrite filled0. unfold N.recursion. simpl. repeat rewrite N.add_0_l. repeat rewrite N.add_0_r. apply filled_8_to_qword.
  }
  rewrite H_first_8. clear H_first_8. remember (m[Ⓠ dest := m Ⓠ[src]]) as m'.
  (* Expand the recursion*)
  unfold N.recursion at 1. simpl. repeat rewrite N.add_0_l. repeat rewrite N.add_0_r.
  replace (dest + 8) with (8 + dest) by lia. replace (dest + 8 + 1) with (9 + dest) by lia.
  replace (dest + 8 + 2) with (10 + dest) by lia. replace (dest + 8 + 3) with (11 + dest) by lia.
  replace (dest + 8 + 4) with (12 + dest) by lia. replace (dest + 8 + 5) with (13 + dest) by lia. 
  replace (dest + 8 + 6) with (14 + dest) by lia. replace (dest + 8 + 7) with (15 + dest) by lia.
  
  replace (src + 8) with (8 + src) by lia. replace (src + 8 + 1) with (9 + src) by lia.
  replace (src + 8 + 2) with (10 + src) by lia. replace (src + 8 + 3) with (11 + src) by lia.
  replace (src + 8 + 4) with (12 + src) by lia. replace (src + 8 + 5) with (13 + src) by lia.
  replace (src + 8 + 6) with (14 + src) by lia. replace (src + 8 + 7) with (15 + src) by lia.
  (*set merge pattern *)
  replace (9 + dest) with ((8 + dest) + 1) by lia. replace (10 + dest) with ((8 + dest) + 2) by lia.
  replace (11 + dest) with ((8 + dest) + 3) by lia. replace (12 + dest) with ((8 + dest) + 4) by lia.
  replace (13 + dest) with ((8 + dest) + 5) by lia. replace (14 + dest) with ((8 + dest) + 6) by lia.
  replace (15 + dest) with ((8 + dest) + 7) by lia. replace (9 + src) with ((8 + src) + 1) by lia.
  replace (10 + src) with ((8 + src) + 2) by lia. replace (11 + src) with ((8 + src) + 3) by lia.
  replace (12 + src) with ((8 + src) + 4) by lia. replace (13 + src) with ((8 + src) + 5) by lia.
  replace (14 + src) with ((8 + src) + 6) by lia. replace (15 + src) with ((8 + src) + 7) by lia.
  
  (* Apply setmem_merge *)
  rewrite (setmem_merge 64 LittleE 1 1).
  rewrite (setmem_merge 64 LittleE 2 1).
  rewrite (setmem_merge 64 LittleE 3 1).
  rewrite (setmem_merge 64 LittleE 4 1).
  rewrite (setmem_merge 64 LittleE 5 1).
  rewrite (setmem_merge 64 LittleE 6 1).
  rewrite (setmem_merge 64 LittleE 7 1).
  f_equal;admit.
  (*first goal: dest + 8 = dest +8 at a binary level.
    second goal: getmem equality of bytes and quad-> cant unfold getmem opaque*)
Admitted.

Lemma two_qword_writes_to_filled:
  ∀ m dest src,
    m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]] = filled m dest src 16.
Proof.
  intros.
  symmetry.
  apply filled_16_to_2qwords.
Qed.
Lemma qword_subsumes_bytes_tail: ∀ m dest src n,
  n < 8 →
  N.recursion (m [Ⓠ dest := m Ⓠ[ src ]])
    (fun i m' => m' [Ⓑ dest + 8 + i := m Ⓑ[ src + 8 + i ]]) n =
  m [Ⓠ dest := m Ⓠ[ src ]] [Ⓠ dest + n := m Ⓠ[ src + n ]].
Proof.
  (*qword(8bytes) at dest plus n bytes after it is the same as qword at dest 
   and qword at dest+n. In other words, overlapping copy works  *)
  admit.
Admitted.

Lemma filled_overlap_8bytes:
  ∀ m dest src len,
    8 <= len < 16 ->
    filled m dest src len =
    let base := filled m dest src 0 in
    base
    [Ⓠ dest := base Ⓠ[ src ]]
    [Ⓠ dest ⊖ 8 + len := base Ⓠ[ src ⊖ 8 + len ]].
Proof.
   intros m dest src len Hlen.
  assert (exists n, len = 8 + n /\ n < 8) as [n [Hlen_eq Hn]].
  { exists (len - 8). split; lia. }
  rewrite Hlen_eq.
  erewrite filled_add.
  assert (filled m dest src 8 = m[Ⓠ dest := m Ⓠ[src]]) as H8.
  {
    replace 8 with (0 + 8) by reflexivity.
    rewrite (filled_add 8 m dest src 0).
    rewrite filled0.
    unfold N.recursion. simpl.
    repeat rewrite N.add_0_l. repeat rewrite N.add_0_r.
    apply filled_8_to_qword.
  }
  rewrite H8. 
  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7) as Hcases by lia.
  destruct Hcases as [H0|[H1|[H2|[H3|[H4|[H5|[H6|H7]]]]]]]; subst n.
  
  - simpl. unfold N.recursion. simpl. psimpl. reflexivity.  
  - erewrite qword_subsumes_bytes_tail by lia. simpl. psimpl. reflexivity.
  - erewrite qword_subsumes_bytes_tail by lia. simpl. psimpl. reflexivity.
  - erewrite qword_subsumes_bytes_tail by lia. simpl. psimpl. reflexivity.
  - erewrite qword_subsumes_bytes_tail by lia. simpl. psimpl. reflexivity.
  - erewrite qword_subsumes_bytes_tail by lia. simpl. psimpl. reflexivity.
  - erewrite qword_subsumes_bytes_tail by lia. simpl. psimpl. reflexivity.
  - erewrite qword_subsumes_bytes_tail by lia. simpl. psimpl. reflexivity.
Qed.
    

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
  
Lemma filled_32_to_4qwords:
  ∀ m dest src,
    filled m dest src 32 =
    m[Ⓠ dest := m Ⓠ[src]]
     [Ⓠ 8 + dest := m Ⓠ[8 + src]]
     [Ⓠ 16 + dest := m Ⓠ[16 + src]]
     [Ⓠ 24 + dest := m Ⓠ[24 + src]].
Proof.
  intros.
  replace 32 with (0 + 32) by reflexivity.
  rewrite (filled_add 32 m dest src 0).
  rewrite filled0.
  unfold N.recursion. simpl.
  repeat rewrite N.add_0_l. repeat rewrite N.add_0_r.
  (* Convert consecutive byte writes to qword writes *)
  admit.
Admitted.

Lemma qwords_subsume_bytes_tail_32: ∀ m dest src n,
  0 < n <= 32 →
  N.recursion (m [Ⓠ dest := m Ⓠ[ src ]]
                  [Ⓠ 8 + dest := m Ⓠ[ 8 + src ]]
                  [Ⓠ 16 + dest := m Ⓠ[ 16 + src ]]
                  [Ⓠ 24 + dest := m Ⓠ[ 24 + src ]])
    (fun i m' => m' [Ⓑ dest + 32 + i := m Ⓑ[ src + 32 + i ]]) n =
  m [Ⓠ dest := m Ⓠ[ src ]]
    [Ⓠ 8 + dest := m Ⓠ[ 8 + src ]]
    [Ⓠ 16 + dest := m Ⓠ[ 16 + src ]]
    [Ⓠ 24 + dest := m Ⓠ[ 24 + src ]]
    [Ⓠ dest ⊖ 32 + (32 + n) := m Ⓠ[ src ⊖ 32 + (32 + n) ]]
    [Ⓠ dest ⊖ 24 + (32 + n) := m Ⓠ[ src ⊖ 24 + (32 + n) ]]
    [Ⓠ dest ⊖ 16 + (32 + n) := m Ⓠ[ src ⊖ 16 + (32 + n) ]]
    [Ⓠ dest ⊖ 8 + (32 + n) := m Ⓠ[ src ⊖ 8 + (32 + n) ]].
Proof.
  (* The remaining n bytes after the first 32 are covered by 4 overlapping qword writes from the end *)
  admit.
Admitted.

Lemma filled_overlap_32bytes:
  ∀ m dest src len,
    32 < len <= 64 ->
    filled m dest src len =
    m[Ⓠ dest := m Ⓠ[src]]
     [Ⓠ 8 + dest := m Ⓠ[8 + src]]
     [Ⓠ 16 + dest := m Ⓠ[16 + src]]
     [Ⓠ 24 + dest := m Ⓠ[24 + src]]
     [Ⓠ dest ⊖ 32 + len := m Ⓠ[src ⊖ 32 + len]]
     [Ⓠ dest ⊖ 24 + len := m Ⓠ[src ⊖ 24 + len]]
     [Ⓠ dest ⊖ 16 + len := m Ⓠ[src ⊖ 16 + len]]
     [Ⓠ dest ⊖ 8 + len := m Ⓠ[src ⊖ 8 + len]].
Proof.
  intros m dest src len Hlen.
  assert (exists n, len = 32 + n /\ 0 < n <= 32) as [n [Hlen_eq Hn]].
  { exists (len - 32). split; lia. }
  rewrite Hlen_eq.
  erewrite filled_add.
  assert (filled m dest src 32 = 
          m[Ⓠ dest := m Ⓠ[src]]
           [Ⓠ 8 + dest := m Ⓠ[8 + src]]
           [Ⓠ 16 + dest := m Ⓠ[16 + src]]
           [Ⓠ 24 + dest := m Ⓠ[24 + src]]) as H32.
  { apply filled_32_to_4qwords. } rewrite H32.
  erewrite qwords_subsume_bytes_tail_32 by lia.
  replace (32 + n) with len by lia.
  reflexivity.
Qed.


Lemma qword_subsumes_bytes_tail_16: ∀ m dest src n,
  n <= 16 →
  N.recursion (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]])
    (fun i m' => m'[Ⓑ dest + 16 + i := m Ⓑ[src + 16 + i]]) n =
  m[Ⓠ dest := m Ⓠ[src]]
   [Ⓠ 8 + dest := m Ⓠ[8 + src]]
   [Ⓠ dest ⊖ 16 + (16 + n) := m Ⓠ[src ⊖ 16 + (16 + n)]]
   [Ⓠ dest ⊖ 8 + (16 + n) := m Ⓠ[src ⊖ 8 + (16 + n)]].
Proof.
 admit.
 (*The remaining n bytes  at positions 16 -> 16+n-1 can be covered by 2 overlapping qword writes*)
Admitted.

Lemma filled_overlap_16to32bytes:
  ∀ m dest src len,
    16 <= len <= 32 ->
    filled m dest src len =
    m[Ⓠ dest := m Ⓠ[src]]
     [Ⓠ 8 + dest := m Ⓠ[8 + src]]
     [Ⓠ dest ⊖ 16 + len := m Ⓠ[src ⊖ 16 + len]]
     [Ⓠ dest ⊖ 8 + len := m Ⓠ[src ⊖ 8 + len]].
Proof.
  intros m dest src len [Hge Hle].
  assert (exists n, len = 16 + n /\ n <= 16) as [n [Hlen_eq Hn]].
  { exists (len - 16). split; lia. }
  rewrite Hlen_eq.
  erewrite filled_add.
  rewrite filled_16_to_2qwords.
  erewrite qword_subsumes_bytes_tail_16 by lia.
  psimpl.
  reflexivity.
Qed.

Lemma filled_64_to_8qwords:
  ∀ m dest src,
    filled m dest src 64 =
    m[Ⓠ dest := m Ⓠ[src]]
     [Ⓠ 8 + dest := m Ⓠ[8 + src]]
     [Ⓠ 16 + dest := m Ⓠ[16 + src]]
     [Ⓠ 24 + dest := m Ⓠ[24 + src]]
     [Ⓠ 32 + dest := m Ⓠ[32 + src]]
     [Ⓠ 40 + dest := m Ⓠ[40 + src]]
     [Ⓠ 48 + dest := m Ⓠ[48 + src]]
     [Ⓠ 56 + dest := m Ⓠ[56 + src]].
Proof.
  intros.
  replace 64 with (0 + 64) by reflexivity.
  rewrite (filled_add 64 m dest src 0).
  rewrite filled0.
  unfold N.recursion. simpl.
  repeat rewrite N.add_0_l. repeat rewrite N.add_0_r.
  (* Convert 64 consecutive byte writes to 8 qword writes *)
  admit.
Admitted.

Lemma qwords_subsume_bytes_tail_64_small: ∀ m dest src n,
  0 < n <= 32 →
  N.recursion (m [Ⓠ dest := m Ⓠ[ src ]]
                  [Ⓠ 8 + dest := m Ⓠ[ 8 + src ]]
                  [Ⓠ 16 + dest := m Ⓠ[ 16 + src ]]
                  [Ⓠ 24 + dest := m Ⓠ[ 24 + src ]]
                  [Ⓠ 32 + dest := m Ⓠ[ 32 + src ]]
                  [Ⓠ 40 + dest := m Ⓠ[ 40 + src ]]
                  [Ⓠ 48 + dest := m Ⓠ[ 48 + src ]]
                  [Ⓠ 56 + dest := m Ⓠ[ 56 + src ]])
    (fun i m' => m' [Ⓑ dest + 64 + i := m Ⓑ[ src + 64 + i ]]) n =
  m [Ⓠ dest := m Ⓠ[ src ]]
    [Ⓠ 8 + dest := m Ⓠ[ 8 + src ]]
    [Ⓠ 16 + dest := m Ⓠ[ 16 + src ]]
    [Ⓠ 24 + dest := m Ⓠ[ 24 + src ]]
    [Ⓠ 32 + dest := m Ⓠ[ 32 + src ]]
    [Ⓠ 40 + dest := m Ⓠ[ 40 + src ]]
    [Ⓠ 48 + dest := m Ⓠ[ 48 + src ]]
    [Ⓠ 56 + dest := m Ⓠ[ 56 + src ]]
    [Ⓠ dest ⊖ 32 + (64 + n) := m Ⓠ[ src ⊖ 32 + (64 + n) ]]
    [Ⓠ dest ⊖ 24 + (64 + n) := m Ⓠ[ src ⊖ 24 + (64 + n) ]]
    [Ⓠ dest ⊖ 16 + (64 + n) := m Ⓠ[ src ⊖ 16 + (64 + n) ]]
    [Ⓠ dest ⊖ 8 + (64 + n) := m Ⓠ[ src ⊖ 8 + (64 + n) ]].
Proof.
  (* The remaining n bytes (where n <= 32) after the first 64 are covered by 4 overlapping tail qwords *)
  admit.
Admitted.

Lemma filled_overlap_64bytes_small:
  ∀ m dest src len,
    64 < len <= 96 ->
    filled m dest src len =
    m[Ⓠ dest := m Ⓠ[src]]
     [Ⓠ 8 + dest := m Ⓠ[8 + src]]
     [Ⓠ 16 + dest := m Ⓠ[16 + src]]
     [Ⓠ 24 + dest := m Ⓠ[24 + src]]
     [Ⓠ 32 + dest := m Ⓠ[32 + src]]
     [Ⓠ 40 + dest := m Ⓠ[40 + src]]
     [Ⓠ 48 + dest := m Ⓠ[48 + src]]
     [Ⓠ 56 + dest := m Ⓠ[56 + src]]
     [Ⓠ dest ⊖ 32 + len := m Ⓠ[src ⊖ 32 + len]]
     [Ⓠ dest ⊖ 24 + len := m Ⓠ[src ⊖ 24 + len]]
     [Ⓠ dest ⊖ 16 + len := m Ⓠ[src ⊖ 16 + len]]
     [Ⓠ dest ⊖ 8 + len := m Ⓠ[src ⊖ 8 + len]].
Proof.
  intros m dest src len Hlen.
  assert (exists n, len = 64 + n /\ 0 < n <= 32) as [n [Hlen_eq Hn]].
  { exists (len - 64). split; lia. }
  rewrite Hlen_eq.
  erewrite filled_add.
  assert (filled m dest src 64 = 
          m[Ⓠ dest := m Ⓠ[src]]
           [Ⓠ 8 + dest := m Ⓠ[8 + src]]
           [Ⓠ 16 + dest := m Ⓠ[16 + src]]
           [Ⓠ 24 + dest := m Ⓠ[24 + src]]
           [Ⓠ 32 + dest := m Ⓠ[32 + src]]
           [Ⓠ 40 + dest := m Ⓠ[40 + src]]
           [Ⓠ 48 + dest := m Ⓠ[48 + src]]
           [Ⓠ 56 + dest := m Ⓠ[56 + src]]) as H64.
  {
    apply filled_64_to_8qwords.
  }
  rewrite H64.
  erewrite qwords_subsume_bytes_tail_64_small by lia.
  replace (64 + n) with len by lia.
  reflexivity.
Qed.

Lemma qwords_subsume_bytes_tail_64: ∀ m dest src n,
  0 < n <= 64 →
  N.recursion (m [Ⓠ dest := m Ⓠ[ src ]]
                  [Ⓠ 8 + dest := m Ⓠ[ 8 + src ]]
                  [Ⓠ 16 + dest := m Ⓠ[ 16 + src ]]
                  [Ⓠ 24 + dest := m Ⓠ[ 24 + src ]]
                  [Ⓠ 32 + dest := m Ⓠ[ 32 + src ]]
                  [Ⓠ 40 + dest := m Ⓠ[ 40 + src ]]
                  [Ⓠ 48 + dest := m Ⓠ[ 48 + src ]]
                  [Ⓠ 56 + dest := m Ⓠ[ 56 + src ]])
    (fun i m' => m' [Ⓑ dest + 64 + i := m Ⓑ[ src + 64 + i ]]) n =
  m [Ⓠ dest ⊖ 64 + (64 + n) := m Ⓠ[ src ⊖ 64 + (64 + n) ]]
    [Ⓠ dest ⊖ 56 + (64 + n) := m Ⓠ[ src ⊖ 56 + (64 + n) ]]
    [Ⓠ dest ⊖ 48 + (64 + n) := m Ⓠ[ src ⊖ 48 + (64 + n) ]]
    [Ⓠ dest ⊖ 40 + (64 + n) := m Ⓠ[ src ⊖ 40 + (64 + n) ]]
    [Ⓠ dest := m Ⓠ[ src ]]
    [Ⓠ 8 + dest := m Ⓠ[ 8 + src ]]
    [Ⓠ 16 + dest := m Ⓠ[ 16 + src ]]
    [Ⓠ 24 + dest := m Ⓠ[ 24 + src ]]
    [Ⓠ 32 + dest := m Ⓠ[ 32 + src ]]
    [Ⓠ 40 + dest := m Ⓠ[ 40 + src ]]
    [Ⓠ 48 + dest := m Ⓠ[ 48 + src ]]
    [Ⓠ 56 + dest := m Ⓠ[ 56 + src ]]
    [Ⓠ dest ⊖ 32 + (64 + n) := m Ⓠ[ src ⊖ 32 + (64 + n) ]]
    [Ⓠ dest ⊖ 24 + (64 + n) := m Ⓠ[ src ⊖ 24 + (64 + n) ]]
    [Ⓠ dest ⊖ 16 + (64 + n) := m Ⓠ[ src ⊖ 16 + (64 + n) ]]
    [Ⓠ dest ⊖ 8 + (64 + n) := m Ⓠ[ src ⊖ 8 + (64 + n) ]].
Proof.
  (* The remaining n bytes after the first 64 are covered by 8 overlapping qword writes:
     4 from the very end, 8 in the middle, and 4 more overlapping from end *)
  admit.
Admitted.

Lemma filled_overlap_64bytes:
  ∀ m dest src len,
    64 < len <= 128 ->
    filled m dest src len =
    m[Ⓠ dest ⊖ 64 + len := m Ⓠ[src ⊖ 64 + len]]
     [Ⓠ dest ⊖ 56 + len := m Ⓠ[src ⊖ 56 + len]]
     [Ⓠ dest ⊖ 48 + len := m Ⓠ[src ⊖ 48 + len]]
     [Ⓠ dest ⊖ 40 + len := m Ⓠ[src ⊖ 40 + len]]
     [Ⓠ dest := m Ⓠ[src]]
     [Ⓠ 8 + dest := m Ⓠ[8 + src]]
     [Ⓠ 16 + dest := m Ⓠ[16 + src]]
     [Ⓠ 24 + dest := m Ⓠ[24 + src]]
     [Ⓠ 32 + dest := m Ⓠ[32 + src]]
     [Ⓠ 40 + dest := m Ⓠ[40 + src]]
     [Ⓠ 48 + dest := m Ⓠ[48 + src]]
     [Ⓠ 56 + dest := m Ⓠ[56 + src]]
     [Ⓠ dest ⊖ 32 + len := m Ⓠ[src ⊖ 32 + len]]
     [Ⓠ dest ⊖ 24 + len := m Ⓠ[src ⊖ 24 + len]]
     [Ⓠ dest ⊖ 16 + len := m Ⓠ[src ⊖ 16 + len]]
     [Ⓠ dest ⊖ 8 + len := m Ⓠ[src ⊖ 8 + len]].
Proof.
  intros m dest src len Hlen.
  assert (exists n, len = 64 + n /\ 0 < n <= 64) as [n [Hlen_eq Hn]].
  { exists (len - 64). split; lia. }
  rewrite Hlen_eq.
  erewrite filled_add.
  assert (filled m dest src 64 = 
          m[Ⓠ dest := m Ⓠ[src]]
           [Ⓠ 8 + dest := m Ⓠ[8 + src]]
           [Ⓠ 16 + dest := m Ⓠ[16 + src]]
           [Ⓠ 24 + dest := m Ⓠ[24 + src]]
           [Ⓠ 32 + dest := m Ⓠ[32 + src]]
           [Ⓠ 40 + dest := m Ⓠ[40 + src]]
           [Ⓠ 48 + dest := m Ⓠ[48 + src]]
           [Ⓠ 56 + dest := m Ⓠ[56 + src]]) as H64.
  { apply filled_64_to_8qwords. }
  rewrite H64.
  erewrite qwords_subsume_bytes_tail_64 by lia.
  replace (64 + n) with len by lia.
  reflexivity.
Qed.



Lemma unaligned_qword_writes_eq_filled: ∀ m dest src len,
  let m1 := m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]] in
  let m2 := m1[Ⓠ 16 + (dest .& 18446744073709551600) := m Ⓠ[16 + src ⊖ dest mod 16]]
               [Ⓠ 24 + (dest .& 18446744073709551600) := m Ⓠ[24 + src ⊖ dest mod 16]] in
  let m3 := m2[Ⓠ 32 + (dest .& 18446744073709551600) := m1 Ⓠ[32 + src ⊖ dest mod 16]]
               [Ⓠ 40 + (dest .& 18446744073709551600) := m1 Ⓠ[40 + src ⊖ dest mod 16]] in
  let m4 := m3[Ⓠ 48 + (dest .& 18446744073709551600) := m1 Ⓠ[48 + src ⊖ dest mod 16]]
               [Ⓠ 56 + (dest .& 18446744073709551600) := m1 Ⓠ[56 + src ⊖ dest mod 16]] in
  m1[Ⓠ 16 + (dest .& 18446744073709551600) := m Ⓠ[16 + src ⊖ dest mod 16]]
    [Ⓠ 24 + (dest .& 18446744073709551600) := m Ⓠ[24 + src ⊖ dest mod 16]]
    [Ⓠ 32 + (dest .& 18446744073709551600) := m1 Ⓠ[32 + src ⊖ dest mod 16]]
    [Ⓠ 40 + (dest .& 18446744073709551600) := m1 Ⓠ[40 + src ⊖ dest mod 16]]
    [Ⓠ 48 + (dest .& 18446744073709551600) := m1 Ⓠ[48 + src ⊖ dest mod 16]]
    [Ⓠ 56 + (dest .& 18446744073709551600) := m1 Ⓠ[56 + src ⊖ dest mod 16]]
    [Ⓠ 64 + (dest .& 18446744073709551600) := m1 Ⓠ[64 + src ⊖ dest mod 16]]
    [Ⓠ 72 + (dest .& 18446744073709551600) := m1 Ⓠ[72 + src ⊖ dest mod 16]]
    [Ⓠ dest ⊖ 64 + len := m1 Ⓠ[src ⊖ 64 + len]]
    [Ⓠ dest ⊖ 56 + len := m1 Ⓠ[src ⊖ 56 + len]]
    [Ⓠ dest ⊖ 48 + len := m2 Ⓠ[src ⊖ 48 + len]]
    [Ⓠ dest ⊖ 40 + len := m2 Ⓠ[src ⊖ 40 + len]]
    [Ⓠ dest ⊖ 32 + len := m3 Ⓠ[src ⊖ 32 + len]]
    [Ⓠ dest ⊖ 24 + len := m3 Ⓠ[src ⊖ 24 + len]]
    [Ⓠ dest ⊖ 16 + len := m4 Ⓠ[src ⊖ 16 + len]]
    [Ⓠ dest ⊖ 8 + len := m4 Ⓠ[src ⊖ 8 + len]] = 
  filled m dest src len.
Proof.
  intros.
  (* lemma states that for unaligned large copies, a specific pattern of 
     aligned qword writes (with overlapping tail writes) correctly implements
     the byte-by-byte filled operation. *)
  admit.
Admitted.

Lemma filled_unaligned_large: ∀ m dest src len,
  filled m dest src len =
  m[Ⓠ dest := m Ⓠ[src]]
   [Ⓠ 8 + dest := m Ⓠ[8 + src]]
   [Ⓠ 16 + (dest .& 18446744073709551600) := m Ⓠ[16 + src ⊖ dest mod 16]]
   [Ⓠ 24 + (dest .& 18446744073709551600) := m Ⓠ[24 + src ⊖ dest mod 16]]
   [Ⓠ 32 + (dest .& 18446744073709551600) 
    := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[32 + src ⊖ dest mod 16]]
   [Ⓠ 40 + (dest .& 18446744073709551600)
    := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[40 + src ⊖ dest mod 16]]
   [Ⓠ 48 + (dest .& 18446744073709551600)
    := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[48 + src ⊖ dest mod 16]]
   [Ⓠ 56 + (dest .& 18446744073709551600)
    := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[56 + src ⊖ dest mod 16]]
   [Ⓠ 64 + (dest .& 18446744073709551600)
    := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[64 + src ⊖ dest mod 16]]
   [Ⓠ 72 + (dest .& 18446744073709551600)
    := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[72 + src ⊖ dest mod 16]]
   [Ⓠ dest ⊖ 64 + len := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[src ⊖ 64 + len]]
   [Ⓠ dest ⊖ 56 + len := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[src ⊖ 56 + len]]
   [Ⓠ dest ⊖ 48 + len 
    := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]
         [Ⓠ 16 + (dest .& 18446744073709551600) := m Ⓠ[16 + src ⊖ dest mod 16]]
         [Ⓠ 24 + (dest .& 18446744073709551600) := m Ⓠ[24 + src ⊖ dest mod 16]]) Ⓠ[src ⊖ 48 + len]]
   [Ⓠ dest ⊖ 40 + len
    := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]
         [Ⓠ 16 + (dest .& 18446744073709551600) := m Ⓠ[16 + src ⊖ dest mod 16]]
         [Ⓠ 24 + (dest .& 18446744073709551600) := m Ⓠ[24 + src ⊖ dest mod 16]]) Ⓠ[src ⊖ 40 + len]]
   [Ⓠ dest ⊖ 32 + len
    := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]
         [Ⓠ 16 + (dest .& 18446744073709551600) := m Ⓠ[16 + src ⊖ dest mod 16]]
         [Ⓠ 24 + (dest .& 18446744073709551600) := m Ⓠ[24 + src ⊖ dest mod 16]]
         [Ⓠ 32 + (dest .& 18446744073709551600)
          := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[32 + src ⊖ dest mod 16]]
         [Ⓠ 40 + (dest .& 18446744073709551600)
          := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[40 + src ⊖ dest mod 16]]) Ⓠ[src ⊖ 32 + len]]
   [Ⓠ dest ⊖ 24 + len
    := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]
         [Ⓠ 16 + (dest .& 18446744073709551600) := m Ⓠ[16 + src ⊖ dest mod 16]]
         [Ⓠ 24 + (dest .& 18446744073709551600) := m Ⓠ[24 + src ⊖ dest mod 16]]
         [Ⓠ 32 + (dest .& 18446744073709551600)
          := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[32 + src ⊖ dest mod 16]]
         [Ⓠ 40 + (dest .& 18446744073709551600)
          := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[40 + src ⊖ dest mod 16]]) Ⓠ[src ⊖ 24 + len]]
   [Ⓠ dest ⊖ 16 + len
    := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]
         [Ⓠ 16 + (dest .& 18446744073709551600) := m Ⓠ[16 + src ⊖ dest mod 16]]
         [Ⓠ 24 + (dest .& 18446744073709551600) := m Ⓠ[24 + src ⊖ dest mod 16]]
         [Ⓠ 32 + (dest .& 18446744073709551600)
          := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[32 + src ⊖ dest mod 16]]
         [Ⓠ 40 + (dest .& 18446744073709551600)
          := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[40 + src ⊖ dest mod 16]]
         [Ⓠ 48 + (dest .& 18446744073709551600)
          := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[48 + src ⊖ dest mod 16]]
         [Ⓠ 56 + (dest .& 18446744073709551600)
          := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[56 + src ⊖ dest mod 16]]) Ⓠ[src ⊖ 16 + len]]
   [Ⓠ dest ⊖ 8 + len
    := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]
         [Ⓠ 16 + (dest .& 18446744073709551600) := m Ⓠ[16 + src ⊖ dest mod 16]]
         [Ⓠ 24 + (dest .& 18446744073709551600) := m Ⓠ[24 + src ⊖ dest mod 16]]
         [Ⓠ 32 + (dest .& 18446744073709551600)
          := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[32 + src ⊖ dest mod 16]]
         [Ⓠ 40 + (dest .& 18446744073709551600)
          := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[40 + src ⊖ dest mod 16]]
         [Ⓠ 48 + (dest .& 18446744073709551600)
          := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[48 + src ⊖ dest mod 16]]
         [Ⓠ 56 + (dest .& 18446744073709551600)
          := (m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]) Ⓠ[56 + src ⊖ dest mod 16]]) Ⓠ[src ⊖ 8 + len]].
Proof.
  intros.
  
  set (m1 := m[Ⓠ dest := m Ⓠ[src]][Ⓠ 8 + dest := m Ⓠ[8 + src]]).
  set (m2 := m1[Ⓠ 16 + (dest .& 18446744073709551600) := m Ⓠ[16 + src ⊖ dest mod 16]]
                [Ⓠ 24 + (dest .& 18446744073709551600) := m Ⓠ[24 + src ⊖ dest mod 16]]).
  set (m3 := m2[Ⓠ 32 + (dest .& 18446744073709551600) := m1 Ⓠ[32 + src ⊖ dest mod 16]]
                [Ⓠ 40 + (dest .& 18446744073709551600) := m1 Ⓠ[40 + src ⊖ dest mod 16]]).
  set (m4 := m3[Ⓠ 48 + (dest .& 18446744073709551600) := m1 Ⓠ[48 + src ⊖ dest mod 16]]
                [Ⓠ 56 + (dest .& 18446744073709551600) := m1 Ⓠ[56 + src ⊖ dest mod 16]]).
  set (m5 := m4[Ⓠ 64 + (dest .& 18446744073709551600) := m1 Ⓠ[64 + src ⊖ dest mod 16]]
                [Ⓠ 72 + (dest .& 18446744073709551600) := m1 Ⓠ[72 + src ⊖ dest mod 16]]).
  
  assert (RHS: 
    m1[Ⓠ 16 + (dest .& 18446744073709551600) := m Ⓠ[16 + src ⊖ dest mod 16]]
      [Ⓠ 24 + (dest .& 18446744073709551600) := m Ⓠ[24 + src ⊖ dest mod 16]]
      [Ⓠ 32 + (dest .& 18446744073709551600) := m1 Ⓠ[32 + src ⊖ dest mod 16]]
      [Ⓠ 40 + (dest .& 18446744073709551600) := m1 Ⓠ[40 + src ⊖ dest mod 16]]
      [Ⓠ 48 + (dest .& 18446744073709551600) := m1 Ⓠ[48 + src ⊖ dest mod 16]]
      [Ⓠ 56 + (dest .& 18446744073709551600) := m1 Ⓠ[56 + src ⊖ dest mod 16]]
      [Ⓠ 64 + (dest .& 18446744073709551600) := m1 Ⓠ[64 + src ⊖ dest mod 16]]
      [Ⓠ 72 + (dest .& 18446744073709551600) := m1 Ⓠ[72 + src ⊖ dest mod 16]]
      [Ⓠ dest ⊖ 64 + len := m1 Ⓠ[src ⊖ 64 + len]]
      [Ⓠ dest ⊖ 56 + len := m1 Ⓠ[src ⊖ 56 + len]]
      [Ⓠ dest ⊖ 48 + len := m2 Ⓠ[src ⊖ 48 + len]]
      [Ⓠ dest ⊖ 40 + len := m2 Ⓠ[src ⊖ 40 + len]]
      [Ⓠ dest ⊖ 32 + len := m3 Ⓠ[src ⊖ 32 + len]]
      [Ⓠ dest ⊖ 24 + len := m3 Ⓠ[src ⊖ 24 + len]]
      [Ⓠ dest ⊖ 16 + len := m4 Ⓠ[src ⊖ 16 + len]]
      [Ⓠ dest ⊖ 8 + len := m4 Ⓠ[src ⊖ 8 + len]] = 
    filled m dest src len).
  {
    unfold m1, m2, m3, m4.
    apply unaligned_qword_writes_eq_filled.
  }
  rewrite <- RHS.
  unfold m1, m2, m3, m4, m5.
  psimpl.
  reflexivity.
Qed.

Lemma filled1 :
  forall m dest src,
    filled m dest src 1 =
    m[Ⓑ dest := m Ⓑ[src]].
Proof.
  intros.
  replace 1 with (0 + 1) by reflexivity.
  rewrite (filled_add 1 m dest src 0).
  rewrite filled0.
  unfold N.recursion; cbn.
  repeat rewrite N.add_0_l.
  repeat rewrite N.add_0_r.
  reflexivity.
Qed.

Lemma filled2 :
  forall m dest src,
    filled m dest src 2 =
    m[Ⓑ dest := m Ⓑ[src]]
     [Ⓑ dest + 1 := m Ⓑ[src + 1]].
Proof.
  intros.
  replace 2 with (0 + 2) by reflexivity.
  rewrite (filled_add 2 m dest src 0).
  rewrite filled0.
  unfold N.recursion; cbn.
  repeat rewrite N.add_0_l.
  repeat rewrite N.add_0_r.
  reflexivity.
Qed.

Lemma filled_lt4 :
  forall m dest src len,
    0 < len < 4 ->
    filled m dest src len =
    filled m dest src 0
      [Ⓑ dest := filled m dest src 0 Ⓑ[ src ] ]
      [Ⓑ dest + (len >> 1) := filled m dest src 0 Ⓑ[ src + (len >> 1) ] ]
      [Ⓑ dest ⊖ 1 + len := filled m dest src 0 Ⓑ[ src ⊖ 1 + len ] ].
Proof.
  intros m dest src len H.
  destruct H as [Hgt0 Hlt4].
  assert (len = 1 \/ len = 2 \/ len = 3) as Hcases by lia.
  destruct Hcases as [H1 | [H2 | H3]]; subst len.
  - rewrite filled0.
    rewrite filled1.
    psimpl.
    reflexivity.
  - rewrite filled0.
    rewrite filled2.
    psimpl.
    reflexivity.
  - rewrite filled0.
    apply (filled3_pattern m dest src 3).
    reflexivity.
Qed.
	  
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
  rewrite filled0. exists mem. symmetry. apply filled_overlap_16to32bytes.
  (* 16 < len <= 32 *)
  split.
    -- (*16 <= len *)
      apply N.leb_le in BC1. 
      exact BC1.
    -- (*len <= 32*)
      destruct (32 <=? len) eqn:H32 in BC0.
      + apply N.leb_le in H32.
        destruct (len =? 32) eqn:H32eq in BC0.
        * apply N.eqb_eq in H32eq. lia.
        * discriminate BC0.
      + apply N.leb_gt in H32. lia.
  - step. step. step. apply N.eqb_eq in BC4. exists mem. rewrite BC4. exact MEM'.
  step. step. step. step. step. step. step. 
  (* size < 4 byte copy *)
  exists mem. symmetry. rewrite filled0.
  apply filled_lt4.
  assert (Hgt0 : 0 < len).
  {
    apply N.eqb_neq in BC4. lia.
  }
  split.
  exact Hgt0.
  (* prove len < 4 *)
    assert (Hlt16 : len < 16).
    { apply N.leb_gt. exact BC1. }
  apply N.eqb_eq in BC3.
  assert (len = 0 \/ len = 1 \/ len = 2 \/ len = 3 \/
          len = 4 \/ len = 5 \/ len = 6 \/ len = 7 \/
          len = 8 \/ len = 9 \/ len = 10 \/ len = 11 \/
          len = 12 \/ len = 13 \/ len = 14 \/ len = 15) as Hcases by lia.
   destruct Hcases as
    [H0 | [H1 | [H2 | [H3 |
     [H4 | [H5 | [H6 | [H7 |
      [H8 | [H9 | [H10 | [H11 |
       [H12 | [H13 | [H14 | H15]]]]]]]]]]]]]]];
       subst len; cbn in BC3; cbn in BC2; try lia.
  exfalso.
  apply N.eqb_neq in BC4.
  rewrite H4 in BC3. 
  cbn in BC3.
  discriminate.
  Ltac solve_len_lt4_branch :=
  lazymatch goal with
  | H : (?st R_X2) = ?n |- (?st R_X2) < 4 =>
      first
        [ (* good cases: n = 1,2,3 *)
          rewrite H; lia
        | (* bad cases: contradict the ">>2 mod2 = 0" fact *)
          exfalso;
          lazymatch goal with
          | B3 : N.div2 (N.div2 (?st R_X2)) mod 2 = 0 |- _ =>
              rewrite H in B3; vm_compute in B3; discriminate
          end
        | (* if the >>2 fact doesn't contradict (e.g., n=8..11), use the ">>3 mod2 = 0" eqb fact *)
          exfalso;
          lazymatch goal with
          | B2 : (N.div2 (N.div2 (N.div2 (?st R_X2))) mod 2 =? 0) = true |- _ =>
              rewrite H in B2; vm_compute in B2; discriminate
          end
        ]
  end.
  all: try solve_len_lt4_branch.
  step. step. step. step. 
  (* 4-8 byte copy *)
  exists mem. rewrite filled0.
  symmetry.
  apply filled_overlap_4bytes.
  (*len >= 4*)
  split.
  apply N.leb_gt in BC1. apply N.eqb_neq in BC3.
  rewrite N.shiftr_div_pow2 in BC3.
  assert (2^2 = 4) as Hpow by reflexivity. rewrite Hpow in BC3. 
  assert (len / 4 <> 0) by (intro; rewrite H in BC3; compute in BC3; congruence).
  (*proving base length*)
  assert (len / 4 >= 1) as Hdiv4_ge1.
    { destruct (len / 4) eqn:E. contradiction. lia. }
  assert (4 * (len / 4) <= len) as Hmul. { apply N.mul_div_le. lia. }
  assert (4 * 1 <= 4 * (len / 4)) by lia.
  lia.
  (*len < 8*)
  apply N.leb_gt in BC1.
  apply N.eqb_eq in BC2.
  rewrite N.shiftr_div_pow2 in BC2 by reflexivity.
  assert (2^3 = 8) as Hpow8 by reflexivity.
  rewrite Hpow8 in BC2.
  (*len < 8*)
  assert (len / 8 <= 1) as Hdiv8_le1.
  {
    destruct (len / 8) eqn:Ediv.
    - lia.
    - destruct p.
      + assert (N.pos (xI p) >= 3) by lia.
        assert (8 * (len / 8) <= len) by (apply N.mul_div_le; lia).
        rewrite Ediv in H0.
        lia.
      + assert (N.pos (xO p) >= 2) by lia.
        assert (8 * (len / 8) <= len) by (apply N.mul_div_le; lia).
        rewrite Ediv in H0.
        lia.
      + lia.
  }
  destruct (len / 8) eqn:Hdiv8.
  apply N.div_small_iff in Hdiv8; lia.
  assert (N.pos p = 1) by lia.
  rewrite H in BC2.
  simpl in BC2.
  discriminate.
  
  step. step. step. step. 
  exists mem.
  rewrite filled0 in MEM'.
  rewrite filled0.
  symmetry.
  apply filled_overlap_8bytes.
  split.
  (*prove that lenth is >= 8*)
  -- apply N.leb_gt in BC1. apply N.eqb_neq in BC2.
  rewrite N.shiftr_div_pow2 in BC2.
  (* 2^3 is 8 *)
  assert (2^3 = 8) as Hpow by reflexivity. rewrite Hpow in BC2. 
  assert (len / 8 <> 0) by (intro; rewrite H in BC2; compute in BC2; congruence).
  assert (len / 8 < 2) by (apply N.div_lt_upper_bound; lia).
  assert (0 < len / 8). { apply N.neq_0_lt_0; lia. }
  assert (len / 8 = 1) by lia.
  assert (8 * (len / 8) <= len) by (apply N.mul_div_le; lia). lia.
  (*prove that length is less than 16-easier just braching conditions*)
  -- apply N.leb_gt in BC1.
  assumption.
  
  (* 8-16 byte copy *)
  
  - step. step. step. step. step. step. step. step. step. step.
  (* 32 byte copy *)
  exists mem.
  rewrite filled0.
  symmetry.
  apply filled_overlap_32bytes.
  split.
  + 
    destruct (32 <=? len) eqn:H32 in BC0.
    * apply N.leb_le in H32.
      destruct (len =? 32) eqn:H32eq in BC0.
      -- apply N.eqb_eq in H32eq. subst len.
         simpl in BC0. discriminate BC0.
      -- apply N.eqb_neq in H32eq. lia.
    * simpl in BC0. discriminate BC0.
  + 
    destruct (64 <=? len) eqn:H64 in BC1.
     * apply N.leb_le in H64.
      destruct (len =? 64) eqn:H64eq in BC1.
      -- apply N.eqb_eq in H64eq. lia.
      -- discriminate BC1.
    * apply N.leb_gt in H64. lia.
  + step. step. step. step. step. step. step. step. step. step. step. step. step. step.
  (* 64+ byte copy *)
  exists mem.
  rewrite filled0.
  symmetry.
  apply filled_overlap_64bytes.
  split.
  * (* Prove 64 < len *)
    destruct (64 <=? len) eqn:H64 in BC1.
    -- apply N.leb_le in H64.
       destruct (len =? 64) eqn:H64eq in BC1.
       ++ apply N.eqb_eq in H64eq. subst len.
          simpl in BC1. discriminate BC1.
       ++ apply N.eqb_neq in H64eq. lia.
    -- simpl in BC1. discriminate BC1.
  * (* Prove len < 128 *)
    destruct (2 ^ 7 <=? len) eqn:H128 in BC.
     -- apply N.leb_le in H128.
       destruct (len =? 2 ^ 7) eqn:H128eq in BC.
       ++ apply N.eqb_eq in H128eq. lia.
       ++ discriminate BC.
     -- apply N.leb_gt in H128. lia.
    
  * step. step. step. step. step. step. 
  (* 64 < len < 96 *)
  exists mem.
  rewrite filled0.
  symmetry.
  apply filled_overlap_64bytes_small.
  split.
  -- 
    destruct (64 <=? len) eqn:H64 in BC1.
    ++ apply N.leb_le in H64.
       destruct (len =? 64) eqn:H64eq in BC1.
       ** apply N.eqb_eq in H64eq. subst len.
          simpl in BC1. discriminate BC1.
       ** apply N.eqb_neq in H64eq. lia.
    ++ simpl in BC1. discriminate BC1.
  -- 
  (* len <= 96 *) 
  destruct (96 <=? len) eqn:H96 in BC2.
  ++ apply N.leb_le in H96.
     destruct (len =? 96) eqn:H96eq in BC2.
     ** apply N.eqb_eq in H96eq. lia.
     ** discriminate BC2.
  ++ apply N.leb_gt in H96. lia.
  
  - step. step. step. step. step. step. step. step. step. step. step. step.
  (* invarient 0x100130 64 byte copy loop *)
    exists mem. 
  rewrite filled0.
  exists 16.
  apply two_qword_writes_to_filled.

  step. step. step. step. step. step. step. step. step. step. step. step. 
  (* size < 144 bytes *)
  exists mem.
  rewrite filled0.
  symmetry.
  apply filled_unaligned_large.
  
  - step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. admit.
  admit.
 
   
Admitted.
 
  
