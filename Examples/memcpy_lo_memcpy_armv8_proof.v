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

    Definition regs (s:store) m source dest len r0 r1 r2:=
        s V_MEM64 = filled m source dest len 
        /\ s R_X0 = r0 
        /\ s R_X1 = r1 
        /\ s R_X2 = r2.

	
	(*Would this not be better? we can distinguish between the total length needed to be copied (len) and the 
		 length we've copied so far (k)*)
	Definition regs (s:store) m source dest k len : Prop :=
	  	s V_MEM64 = filled m source dest k 
		/\ s R_X0 = dest
	  	/\ s R_X1 = source ⊕ k 
	  	/\ s R_X2 = len ⊖ k.

				(*Working on it...*)
	Definition common_inv source dest len s m r1 k :=
		regs s m sourse dest k source r1 (len ⊖ k) (*OR regs s m sourse dest (len ⊖ k) len*)
		/\ s R_R3 = source ⊕ k /\ k <= len.


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
