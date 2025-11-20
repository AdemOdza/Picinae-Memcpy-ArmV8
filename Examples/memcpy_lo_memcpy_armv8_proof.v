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

    Definition mem' fbytes := setmem 64 LittleE 40 mem (sp ⊖ 48) fbytes.

    Definition postcondition (s:store) := exists n k fb,
        (* s V_MEM64 = mem' fb /\ *)
        s R_X0 = n /\
        (* strcaseeq (mem' fb) arg1 arg2 k /\ *)
        (n=0 -> (mem' fb) Ⓑ[arg1+k] = 0).


    (* Correctness specification:  memset yields a memory state identical to
    starting memory m except with addresses p..p+len-1 filled with byte c.
    It also returns p in register r0. *)
    (*TODO, The definition has not been changed for memcpy yet*)
    Definition filled m p c len :=
    N.recursion m (fun i m' => m'[Ⓑ p+i := c]) len.


    (*TODO, The definition has not been changed for memcpy yet*)
    Definition postcondition m dest c len s :=
    s R_R0 = dest /\ s V_MEM32 = filled m p c len.


    (*
    POSTCONDITIONS: 

    Return value is a valid pointer or null. 
    Return pointer should match dest.
    Memory at dest of size count should match memory at src of size count.
    *)
End Invariants.