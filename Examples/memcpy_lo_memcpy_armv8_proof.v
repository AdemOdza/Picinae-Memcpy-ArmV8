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


Section Invariants.
    
    Variable sp : N          (* initial stack pointer *).
    Variable mem : memory    (* initial memory state *).
    Variable raddr : N       (* return address (R_X30) *).

    Variable r0 : N        (* memcpy: 1st pointer arg (R_X0), destination address *).
    Variable r1 : N        (* memcpy: 2nd pointer arg (R_X1), source address *).
    Variable r2 : N        (* memcpy: 2nd pointer arg (R_X2), byte count *).

    Definition mem' fbytes := setmem 64 LittleE 40 mem (sp ⊖ 48) fbytes.
(* 
    Definition filled m p c len :=
        N.recursion m (fun i m' => m'[Ⓑ p+i := c]) len. *)

		(*should it be m' or m for source+i??*)
			(*Note: need to keep the same header format for all*)
    Definition filled m dest source len :=
        N.recursion m (fun i m' => m'[Ⓑ dest+i := m Ⓑ[source + i]]) len.
(*
    Definition regs (s:store) m source dest len r0 r1 r2:=
        s V_MEM64 = filled m source dest len 
        /\ s R_X0 = r0 
        /\ s R_X1 = r1 
        /\ s R_X2 = r2.
*)
	
	(*Would this not be better? we can distinguish between the total length needed to be copied (len) and the 
		 length we've copied so far (k)*)
    Definition regs (s : store) (m : memory) (dest : N) (src : N) (len : N)
                    (dst_ptr : N) (src_ptr : N) (remaining : N) :=
        s V_MEM64 = filled m dst_ptr src_ptr (len - remaining)
        /\ s R_X0 = dst_ptr
        /\ s R_X1 = src_ptr
        /\ s R_X2 = remaining.

				(*Working on it...*)
    Definition common_inv (dest : N) (src : N) (len : N) (s : store) (m : memory)
                          (k : N) :=
        regs s m dest src len (dest + k) (src + k) (len - k)
        /\ k <= len
        /\ s R_X30 = raddr.
Definition bounds_safe (dest src len : N) :=
  dest + len < 2^64 /\ src + len < 2^64 /\ len < 2^64.

(* Entry invariants *)
    Definition entry_inv (dest : N) (src : N) (len : N) (s : store) (m : memory) :=
        s R_X0 = dest
        /\ s R_X1 = src
        /\ s R_X2 = len
        /\ s R_X30 = raddr
        /\ bounds_safe dest src len.

    (* Endpoint calculation invariant (after 0x100000-0x100004) *)
    Definition endpoints_inv (dest : N) (src : N) (len : N) (s : store) :=
        s R_X4 = src + len       (* source endpoint *)
        /\ s R_X5 = dest + len.  (* destination endpoint *)

    (* Alignment tracking for large copies *)
    Definition align_inv (dest : N) (s : store) :=
        s R_X14 = dest mod 16    (* alignment offset *)
        /\ s R_X3 = dest - (dest mod 16).  (* 16-byte aligned base *)
        
        
(* Path 1: 16-byte copy (16 <= len < 32) *)
    Definition inv_16byte (dest : N) (src : N) (len : N) (s : store) (m : memory) :=
        16 <= len /\ len < 32
        /\ common_inv dest src len s m 0.  (* k=0, no copy yet *)

    (* Path 2: 8-byte copy (8 <= len < 16) *)
    Definition inv_8byte (dest : N) (src : N) (len : N) (s : store) (m : memory) :=
        8 <= len /\ len < 16
        /\ common_inv dest src len s m 0.

    (* Path 3: 4-byte copy (4 <= len < 8) *)
    Definition inv_4byte (dest : N) (src : N) (len : N) (s : store) (m : memory) :=
        4 <= len /\ len < 8
        /\ common_inv dest src len s m 0.

    (* Path 4: Byte-by-byte copy (len < 4) *)
    Definition inv_1byte (dest : N) (src : N) (len : N) (s : store) (m : memory) :=
        len < 4
        /\ common_inv dest src len s m 0.

    (* Path 5: Medium copy (32 <= len < 128) *)
    Definition inv_medium (dest : N) (src : N) (len : N) (s : store) (m : memory) :=
        32 <= len /\ len < 128
        /\ common_inv dest src len s m 0.

    (* Path 6: Large copy (len >= 128) with loop *)
    Definition inv_large_entry (dest : N) (src : N) (len : N) (s : store) (m : memory) :=
        128 <= len
        /\ align_inv dest s
        /\ common_inv dest src len s m 0.

    (* Loop invariant for 64-byte chunking *)
    Definition inv_large_loop (dest : N) (src : N) (len : N) (s : store) (m : memory)
                              (k : N) :=
        128 <= len
        /\ align_inv dest s
        /\ common_inv dest src len s m k
        /\ k mod 64 = 0    (* k is multiple of 64 *)
        /\ k <= len.     
        
 (* After first comparison: cmp x2, #0x80 *)
    Definition inv_after_cmp128 (dest : N) (src : N) (len : N) (s : store)
                                (m : memory) :=
        endpoints_inv dest src len s
        /\ ((len > 128 /\ s R_PC = 0x100100)   (* jump to large *)
            \/ (len <= 128 /\ s R_PC  = 0x100010)). (* continue *)

    (* After second comparison: cmp x2, #0x20 *)
    Definition inv_after_cmp32 (dest : N) (src : N) (len : N) (s : store)
                               (m : memory) :=
        endpoints_inv dest src len s
        /\ ((len > 32 /\ s R_PC  = 0x100090)    (* jump to medium *)
            \/ (len <= 32 /\ s R_PC  = 0x100018)). (* continue *)

    (* After third comparison: cmp x2, #0x10 *)
    Definition inv_after_cmp16 (dest : N) (src : N) (len : N) (s : store)
                               (m : memory) :=
        endpoints_inv dest src len s
        /\ ((len >= 16 /\ s R_PC  = 0x100020)   (* 16-byte path *)
            \/ (len < 16 /\ s R_PC  = 0x100034)). (* bit test *)


    (* Correctness specification:  memcpy yields a memory state identical to
    starting memory m except with addresses p..p+len-1 filled with the corresponding byte in address source..source+len-1.
    It also returns p in register r0. *)
    Definition postcondition m dest source len s :=
    s R_X0 = dest /\ s V_MEM64 = filled m dest source len.

        Definition memcpy_invset (dest src len : N) (t : trace) :=
        match t with (Addr a, s) :: _ => match a with

        (* Entry point: 0x100000 *)
        | 0x100000 => Some (entry_inv dest src len s mem)

        (* After endpoints calculation: 0x100008 *)
        | 0x100008 => Some (endpoints_inv dest src len s 
                           /\ entry_inv dest src len s mem)

        (* First comparison: 0x100008 *)
        | 0x10000c => Some (inv_after_cmp128 dest src len s mem)

        (* 16-byte path: 0x100020 *)
        | 0x100020 => Some (inv_16byte dest src len s mem)

        (* 8-byte path: 0x100038 *)
        | 0x100038 => Some (inv_8byte dest src len s mem)

        (* 4-byte path: 0x100054 *)
        | 0x100054 => Some (inv_4byte dest src len s mem)

        (* 1-byte path: 0x100070 *)
        | 0x100070 => Some (inv_1byte dest src len s mem)

        (* Medium path entry: 0x100090 *)
        | 0x100090 => Some (inv_medium dest src len s mem)

        (* Large path entry: 0x100100 *)
        | 0x100100 => Some (inv_large_entry dest src len s mem)

        (* Loop header: 0x100128 *)
        | 0x100128 => Some (∃ k, inv_large_loop dest src len s mem k)

        (* Loop body: 0x100130 *)
        | 0x100130 => Some (∃ k, inv_large_loop dest src len s mem k
                           /\ k < len)

        (* Loop back test: 0x100154 *)
        | 0x100154 => Some (∃ k, inv_large_loop dest src len s mem k
                           /\ (k < len))

        (* Cleanup: 0x100158 *)
        | 0x100158 => Some (∃ k, inv_large_loop dest src len s mem k
                           /\ k >= len - 64)

        (* Exit: 0x100188 *)
        | 0x100188 => Some (postcondition mem dest src len s)

        | _ => None
        end
        | _ => None end.
    (*
    POSTCONDITIONS: 
    Return value is a valid pointer or null. 
    Return pointer should match dest.
    Memory at dest of size count should match memory at src of size count.
    *)
    
    
    

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

Notation "0x x" := (N.of_nat x) (at level 0, format "0x x").

(* Optional: helper to make Addr literals easier *)
Notation "'ADDR' x" := (addr x) (at level 0).

Theorem memcpy_functional_correctness :
  ∀ s dest src len mem t s' x'
    (ENTRY: startof t (x',s') = (Addr 0x100000, s))
    (MDL: models arm8typctx s)
    (MEM: s V_MEM64 = mem)
    (R0: s R_X0 = dest)
    (R1: s R_X1 = src)
    (R2: s R_X2 = len)
    (BOUNDS : bounds_safe dest src len),
  satisfies_all memcpy_lo_memcpy_armv8
    (fun t0 => memcpy_invset mem (s R_X30) dest src len t0)
    program_exit
    ((x',s')::t).
Proof.
  Local Ltac step := time arm8_step.
  
  intros. apply prove_invs.  
  simpl. rewrite ENTRY. step.
  repeat split; try exact R0; try exact R1; try exact R2; try lia.
  destruct BOUNDS as [Hdest Hsrc]. assumption.
  destruct BOUNDS as [_ [Hsrc_bound Hlen]]. assumption. 
  destruct BOUNDS as [_ [Hsrc_bound Hlen]]. assumption. 
  
  intros.
  erewrite startof_prefix in ENTRY; try eassumption.
  assert (LEN := models_var R_X2 MDL). rewrite R2 in LEN. unfold arm8typctx in LEN.
  eapply models_at_invariant; try eassumption.
  apply memcpy_welltyped.  
  intro Hinv.
  
  clear - Hinv PRE LEN.
  rename t1 into t. rename s1 into s1_rest. rename Hinv into Hinv_entry.
  destruct_inv 32 PRE. 
  (* entry invarient 0x100000  *)
  destruct PRE as [H1 [H2 [H3 [H4 [H5 H6]]]]].
  step. step. constructor. unfold endpoints_inv. unfold entry_inv.
  constructor. cbn.  apply N.mod_small. lia. cbn. apply N.mod_small. lia. 
  unfold entry_inv; cbn. repeat split; try reflexivity; try assumption. lia.

   
