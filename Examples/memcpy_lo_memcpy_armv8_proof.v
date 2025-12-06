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
      | 0x100188 => true   (* final ret instruction *)
      | _ => false
      end
  | _ => false
end.

      Definition filled m dest src len :=
        N.recursion m (fun i m' => m'[Ⓑ dest + i := m Ⓑ[src + i]]) len.
  
Section Invariants.
    
    Variable sp : N          (* initial stack pointer *).
    Variable mem : memory    (* initial memory state *).
    Variable raddr : N       (* return address (R_X30) *).

    Variable dest : N        (* memcpy: 1st pointer arg (R_X0), destination address *).
    Variable src : N        (* memcpy: 2nd pointer arg (R_X1), source address *).
    Variable len : N        (* memcpy: 2nd pointer arg (R_X2), byte count *).


  
  (* Registers state after copying k bytes *)
  Definition memcpy_regs (s : store) (k : N) :=
    s V_MEM64 = filled mem dest src len /\
    s R_X0 = dest /\
    s R_X1 = src /\
    s R_X2 = len - k /\
    s R_X30 = raddr.

  (* Loop invariant: k bytes copied so far *)
  Definition memcpy_inv (s : store) (k : N) :=
    k <= len /\
    memcpy_regs s k.

  Definition bounds_safe (dest src len : N) :=
    dest + len < 2^64 /\ src + len < 2^64 /\ len < 2^64.


  Definition align_inv (s : store) :=
    s R_X14 = dest mod 16 /\
    s R_X3 = dest - (dest mod 16).



  (* Postcondition: all bytes copied correctly  *)
    Definition postcondition (s : store) :=
      s R_X0 = dest /\
      s V_MEM64 = filled mem dest src len.

Definition memcpy_invset (t : trace) :=
  match t with
  | (Addr a, s) :: _ =>
      if a =? 0x100000 then Some (s R_X0 = dest /\ s R_X1 = src /\ s R_X2 = len /\ s R_X30 = raddr /\ dest + len < 2 ^ 64 /\ src + len < 2 ^ 64 /\  s V_MEM64 = mem)
(*
      (* 16 byte copy *) else if a =? 0x100020 then Some (16 <= len /\ s R_X0 = dest /\ s R_X1 = src /\ s R_X2 = len /\ s R_X4 = src + len /\ s R_X5 = dest + len) 
      (* Small byte copy *) else if a =? 1048628 then Some (∃ k, memcpy_inv s k) *)
      else if a =? 0x100130 then Some (exists k : N, k <= len /\ s V_MEM64 = filled mem dest src k /\ s R_X0 = dest /\ s R_X1 = src /\ s R_X2 = len - k /\ s R_X30 = raddr)
      else if a =? 0x100030 then Some (postcondition s)
      else if a =? 0x100088 then Some (postcondition s)
      else if a =? 0x100064 then Some (postcondition s)
      else if a =? 0x100048 then Some (postcondition s)
      else if a =? 0x1000B8 then Some (postcondition s)
      else if a =? 0x1000F8 then Some (postcondition s)
      else None
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

Lemma mod_sub_rotate : forall a b k n : N,
  n <> 0 ->
  k <= n ->
  k <= a + b ->
  (a + (n - k) + b) mod n = (a + b - k) mod n.
Proof.
  intros a b k n Hn0 Hkn Hkab.

  (* Step 1: Rewrite the LHS using arithmetic only *)
  assert (H : a + (n - k) + b = (a + b - k) + n).
  {
    (* Convert everything into linear arithmetic *)
    lia.
  }
  rewrite H.

  (* Step 2: Reduce modulo *)
  rewrite N.add_mod by exact Hn0.
  rewrite N.mod_same by exact Hn0.
  rewrite N.add_0_r.

  (* Step 3: Remove double mod *)
  rewrite N.mod_mod by exact Hn0.
  reflexivity.
Qed.



Require Import NArith.
Require Import Coq.Logic.FunctionalExtensionality.

(* Lemma: filled preserves memory bounds *)
Lemma filled_memsize_bound:
  forall w m dest src len,
    m < memsize w ->
    filled m dest src len < memsize w.
Proof.
  intros w m dest src len H_bound.
  unfold filled.
  
  (* Prove by induction on len using N.peano_ind *)
  induction len using N.peano_ind.
  
  - (* Base case: len = 0 *)
    rewrite N.recursion_0.
    exact H_bound.

  - (* Inductive case: len = N.succ len' *)
    rewrite N.recursion_succ; try reflexivity.
    (* Let m_rec be the memory after performing the first len byte-updates *)
    set (m_rec := N.recursion m (fun i m' => m' [Ⓑ dest + i := m Ⓑ[ src + i ] ]) len).
    (* Apply setmem_welltyped to the recursion result: notation [Ⓑ .. := ..] expands to
       setmem 64 LittleE 1, so use those concrete arguments. *)
    admit.
Admitted.

(* Corollary: filled produces canonical memory *)
Lemma filled_canonical:
  forall w m dest src len,
    m < memsize w ->
    filled m dest src len = (filled m dest src len) mod memsize w.
Proof.
  intros.
  symmetry.
  apply N.mod_small.
  apply filled_memsize_bound.
  assumption.
Qed.

Theorem memcpy_partial_correctness:
  forall s dest src len mem t s' x'
    (ENTRY: startof t (x', s') = (Addr 0x100000,s))
    (MDL: models arm8typctx s)
    (MEM: s V_MEM64 = mem)
    (R0: s R_X0 = dest)
    (R1: s R_X1 = src)
    (R2: s R_X2 = len)
    (BOUNDS_DEST: dest + len < 2^64)
    (BOUNDS_SRC : src + len < 2^64),
    satisfies_all memcpy_lo_memcpy_armv8
    (fun t0 => memcpy_invset mem (s R_X30) dest src len t0)
    program_exit
    ((x', s')::t).
Proof.

  Local Ltac step := time arm8_step.
  
  intros. apply prove_invs.
  
  (* Base case: entry invariant *)
  simpl. rewrite ENTRY. step.
  repeat split; try assumption.

    
  (* Inductive case *)
  - intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  assert (LEN64 := models_var R_X2 MDL). rewrite R2 in LEN64. unfold arm8typctx in LEN64.
  eapply models_at_invariant; try eassumption. apply memcpy_welltyped. intro MDL1.
  clear - PRE MDL1 LEN64 BOUNDS_DEST BOUNDS_SRC.
  rename t1 into t. rename s1 into s1'. rename MDL1 into MDL.
  
  destruct_inv 32 PRE.

  (* start --> 16 byte copy --> ~ --> ret 1048624 *)
  destruct PRE as [HX0 [HX1 [HX2 [HX30 [Hdest [Hsrc HMEM]]]]]].

  step. step. step. step. step. step. step. step. step. step. step. step.
  
  split. auto.



(* 1. Setup: Convert boolean comparison to logical fact *)
apply N.leb_le in BC1.

(* 2. Start the main extensionality proof *)
assert (H_eq_mod: 
  (s1' V_MEM64 [Ⓠ dest := s1' V_MEM64 Ⓠ[ src ] ] 
               [Ⓠ 8 + dest := s1' V_MEM64 Ⓠ[ 8 + src ] ] 
               [Ⓠ dest ⊖ 16 + len := s1' V_MEM64 Ⓠ[ src ⊖ 16 + len ] ] 
               [Ⓠ dest ⊖ 8 + len := s1' V_MEM64 Ⓠ[ src ⊖ 8 + len ] ]) mod memsize 64 
  = (filled mem dest src len) mod memsize 64).
{
  apply byte_equivalent with (w:=64).
  intro a.
  
  assert (H_addr_norm: forall m v k,
    k <= 16 -> 
    setmem 64 LittleE 8 m (dest ⊖ k ⊕ len) v = 
    setmem 64 LittleE 8 m (dest + len - k) v).
    {
      intros m0 v0 k Hk.
      rewrite <- (setmem_mod_l 64 LittleE 8 m0 (dest ⊖ k ⊕ len)).
      rewrite <- (setmem_mod_l 64 LittleE 8 m0 (dest + len - k)).
      f_equal.
      
      unfold msub, "⊖", "⊕".
      repeat change (snd (N.div_eucl ?a ?b)) with (N.modulo a b).
      try unfold "⊕".
      replace (k mod 2 ^ 64) with k. 
      2: {
      symmetry.
      apply N.mod_small.
      apply N.le_lt_trans with (m := 16).
      exact Hk.
      vm_compute. reflexivity.
      }
  repeat change (snd (N.div_eucl ?a ?b)) with (N.modulo a b).
  replace (k mod 2 ^ 64) with k.
2: { 
  symmetry.
  apply N.mod_small. 
  apply N.le_lt_trans with 16%N.
  exact Hk.
  vm_compute. reflexivity.
}

try unfold "⊕".
replace (dest + (2 ^ 64 - k) + len) 
   with ((dest + len - k) + 1 * 2 ^ 64).
   2: {
   assert (k <= 2^64) by (transitivity 16; [exact Hk | vm_compute; discriminate]).
   assert (k <= dest + len). { transitivity 16; [exact Hk | transitivity len; [exact BC1 | apply N.le_add_l]]. }
   lia.
   
   }
   
   repeat change (snd (N.div_eucl ?a ?b)) with (N.modulo a b).

rewrite N.mod_mod.
rewrite N.add_mod_idemp_l.

replace (dest + (2 ^ 64 - k) + len) 
   with (2 ^ 64 + (dest + len - k)).
2: {
assert (k <= 2^64) by (transitivity 16; [exact Hk | vm_compute; discriminate]).
assert (k <= dest + len).
{
 transitivity 16.
 exact Hk.
 transitivity len.
 exact BC1.
 lia.
}
lia.
}

try unfold "⊕".  rewrite N.add_comm.  replace (2 ^ 64) with (1 * 2 ^ 64) at 1 by lia.
repeat change (snd (N.div_eucl ?a ?b)) with (N.modulo a b).
rewrite N.mod_add.
reflexivity.
vm_compute; discriminate.
vm_compute; discriminate.
vm_compute; discriminate. 

   }

rewrite <- (getbyte_mod_mem (filled mem dest src len) a 64).
   admit.
}
assert (H_L_canon: 
  s1' V_MEM64 [Ⓠ dest := s1' V_MEM64 Ⓠ[ src ] ] 
              [Ⓠ 8 + dest := s1' V_MEM64 Ⓠ[ 8 + src ] ] 
              [Ⓠ dest ⊖ 16 + len := s1' V_MEM64 Ⓠ[ src ⊖ 16 + len ] ] 
              [Ⓠ dest ⊖ 8 + len := s1' V_MEM64 Ⓠ[ src ⊖ 8 + len ] ] 
  = (s1' V_MEM64 [Ⓠ dest := s1' V_MEM64 Ⓠ[ src ] ] 
                 [Ⓠ 8 + dest := s1' V_MEM64 Ⓠ[ 8 + src ] ] 
                 [Ⓠ dest ⊖ 16 + len := s1' V_MEM64 Ⓠ[ src ⊖ 16 + len ] ] 
                 [Ⓠ dest ⊖ 8 + len := s1' V_MEM64 Ⓠ[ src ⊖ 8 + len ] ]) mod memsize 64).
{
  (* Use N.mod_small: m = m mod n when m < n *)
  symmetry.
  apply N.mod_small.
  
  (* Need to prove: memory < memsize 64 *)
  (* Use setmem_welltyped repeatedly: each setmem preserves bounds *)
  
  (* Step 1: s1' V_MEM64 < memsize 64 (from models) *)
  assert (H_base: s1' V_MEM64 < memsize 64).
  {
    (* Use models_var to get the bound from the type context *)
    assert (MEM64 := models_var V_MEM64 MDL). 
    unfold arm8typctx in MEM64.
    (* MEM64 : s1' V_MEM64 < 2^(8*2^64) *)
    (* We need to show this equals memsize 64 *)
    (* Since memsize is opaque, there should be a definitional equality or lemma *)
    exact MEM64. (* This should follow from the definition that memsize 64 = 2^(8*2^64) *)
  }
  
  (* Step 2: Apply setmem_welltyped for each operation *)
  apply setmem_welltyped.
  apply setmem_welltyped. 
  apply setmem_welltyped.
  apply setmem_welltyped.
  exact H_base.
}

(* 2. Assert that the RHS is canonical *)
assert (H_R_canon: 
  filled mem dest src len = (filled mem dest src len) mod memsize 64).
 
{
  (* Use the filled_canonical lemma *)
apply filled_canonical.
assert (MEM64_orig := models_var V_MEM64 MDL).
unfold arm8typctx in MEM64_orig.
rewrite HMEM in MEM64_orig.
exact MEM64_orig.

}

assert (H_setmem_eq: 
  mem [Ⓠ dest := mem Ⓠ[ src ] ] [Ⓠ 8 + dest := mem Ⓠ[ 8 + src ] ] 
      [Ⓠ dest ⊖ 16 + len := mem Ⓠ[ src ⊖ 16 + len ] ] 
      [Ⓠ dest ⊖ 8 + len := mem Ⓠ[ src ⊖ 8 + len ] ] =
  s1' V_MEM64 [Ⓠ dest := s1' V_MEM64 Ⓠ[ src ] ] [Ⓠ 8 + dest := s1' V_MEM64 Ⓠ[ 8 + src ] ] 
              [Ⓠ dest ⊖ 16 + len := s1' V_MEM64 Ⓠ[ src ⊖ 16 + len ] ] 
              [Ⓠ dest ⊖ 8 + len := s1' V_MEM64 Ⓠ[ src ⊖ 8 + len ] ]).
{
  repeat rewrite <- HMEM.
  reflexivity.
}

rewrite H_setmem_eq.
rewrite H_L_canon.
rewrite H_R_canon.
exact H_eq_mod.

  
  (* small byte  --> 4 byte --> 1 byte: count = 0 --> ret 1048712*) 
  step. step. step. admit. 

  (* 1 byte: count ≠ 0 --> ~ -->  ret 1048712*)
  step. step. step. step. step. step. step. admit. 
  
  (* 4 byte --> ~ --> ret 1048676 *)
  step. step. step. step. admit.  
  
  (* 8 byte --> ~ --> ret 1048648 *)
  step. step. step. step. admit. 
  
  (* Medium Copy (count <= 64) --> ~ --> ret 1048760 *)
  step. step. step. step. step. step. step. step. step. step. admit. 
  
  (* Large copy: count > 96 --> ret 1048824 *)
  step. step. step. step. step. step. step. step. step. step. step. step. step. step. admit. 
  
  (* Store 64-byte chunk in loop --> ~ --> ret 1048824 *)
  step. step. step. step. step. step. admit.
  
  (* max size loop --> postcondition proof? ret *)
  step. step. step. step. step. step. step. step. step. step. step. step.  admit. 
  
  (* Cleanup -> ret 1048968 (Goal: False) this takes too long*)
  step. step. step. step. step. step. step. step. step. step. step. step. admit. 
  
  (* 1048880 --> ~ --> ret ??? *)
  step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.  admit. 
  
  (* Loop body 64 bytes per iteration count = 0 so end loop and continue --> Cleanup --> ret 1048968 FALSE?? *)
  step. step. step. step. step. step. step. step. step. step. step. step. 
  step. step. step. step. step. step. step. step. step. step. admit. 

  admit. (* some proof *)
Admitted.

