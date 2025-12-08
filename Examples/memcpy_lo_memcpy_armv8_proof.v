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
      | 0x100130 => Some (exists mem k, memcpy_regs s k /\ s V_MEM64 = filled mem dest src k)

      (* post-condition: *)
      | 0x100188 
      | 0x1000f8 
      | 0x100088 
      | 0x100064 
      | 0x100048 
      | 0x100030 
      | 0x1000b8 => Some (exists mem, memcpy_regs s len /\ s V_MEM64 = filled mem dest src len)

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


Require Import Coq.NArith.NArith.
Require Import Coq.ZArith.ZArith.
Require Import Lia.

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
  repeat step. rewrite filled0 in MEM'. 
  erewrite filled0. repeat eexists; psimpl; try (eassumption || reflexivity).
  
  
  
  assert (LEN64 := models_var R_X2 MDL). rewrite R2 in LEN64. unfold arm8typctx in LEN64.
  auto. psimpl.
  
Admitted.
 
  