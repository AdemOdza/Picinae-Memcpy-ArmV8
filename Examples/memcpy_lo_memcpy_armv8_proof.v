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
        N.recursion m (fun i m' => m'[Ⓑ dest+i := m' Ⓑ[source + i]]) len.
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

(* Entry invariants *)
    Definition entry_inv (dest : N) (src : N) (len : N) (s : store) (m : memory) :=
        s R_X0 = dest
        /\ s R_X1 = src
        /\ s R_X2 = len
        /\ s R_X30 = raddr
        /\ dest + len < 2^64    (* no overflow *)
        /\ src + len < 2^64.

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
        /\ ((len > 128 /\ next_addr = 0x100100)   (* jump to large *)
            \/ (len <= 128 /\ next_addr = 0x100010)). (* continue *)

    (* After second comparison: cmp x2, #0x20 *)
    Definition inv_after_cmp32 (dest : N) (src : N) (len : N) (s : store)
                               (m : memory) :=
        endpoints_inv dest src len s
        /\ ((len > 32 /\ next_addr = 0x100090)    (* jump to medium *)
            \/ (len <= 32 /\ next_addr = 0x100018)). (* continue *)

    (* After third comparison: cmp x2, #0x10 *)
    Definition inv_after_cmp16 (dest : N) (src : N) (len : N) (s : store)
                               (m : memory) :=
        endpoints_inv dest src len s
        /\ ((len >= 16 /\ next_addr = 0x100020)   (* 16-byte path *)
            \/ (len < 16 /\ next_addr = 0x100034)). (* bit test *)
    (* Correctness specification:  memcpy yields a memory state identical to
    starting memory m except with addresses p..p+len-1 filled with the corresponding byte in address source..source+len-1.
    It also returns p in register r0. *)
    Definition postcondition m dest source len s :=
    s R_X0 = dest /\ s V_MEM64 = filled m dest source len.

    (*
    POSTCONDITIONS: 
    Return value is a valid pointer or null. 
    Return pointer should match dest.
    Memory at dest of size count should match memory at src of size count.
    *)

    Definition memcpy_invariants m source dest len (t := trace) := 
        match t with (Addr a, s)::_ => 
            match a with
			| 1048576 => _ (* Entrypoint *) Some (regs s m source dest 0)
			| 1048880 => _ (* Loop entrypoint *) 
            (* | 1048920 => _ (* Exited loop *) *)
            | 1048968 => _ (* Return *)
            | _ => None
            end 
        | _ => None
    end. 
End Invariants.

Lemma filled0: ∀ m p c, filled m p c 0 = m.
Proof.
  intros. reflexivity.
Qed.
