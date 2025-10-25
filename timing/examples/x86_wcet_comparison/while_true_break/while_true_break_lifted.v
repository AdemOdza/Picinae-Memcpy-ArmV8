(* Automatically generated with pcode2coq
arch: amd64
file: while_true_break
function: while_true_break
*)

Require Import Picinae_amd64.
Require Import NArith.
Require Import Lia.
Open Scope N.

Definition while_true_break_while_true_break_amd64 : program := fun _ a => match a with

(* 0x00101140: MOV EDX,EDI *)
(*    1052992: MOV EDX,EDI *)
| 0x101140 => Some (2,
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00101142: LEA ECX,[RDI + RDI*0x1] *)
(*    1052994: LEA ECX,[RDI + RDI*0x1] *)
| 0x101142 => Some (3,
	Move (V_TEMP 0x4600) (BinOp OP_TIMES (Var R_RDI) (Word 0x1 64)) $;
	Move (V_TEMP 0x4700) (BinOp OP_PLUS (Var R_RDI) (Var (V_TEMP 0x4600))) $;
	Move R_RCX (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x4700)) (Word 0 64))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00101145: MOV EAX,EDI *)
(*    1052997: MOV EAX,EDI *)
| 0x101145 => Some (2,
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX)))
)

(* 0x00101147: IMUL EDX,EDI *)
(*    1052999: IMUL EDX,EDI *)
| 0x101147 => Some (3,
	Move (V_TEMP 0x33e80) (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move (V_TEMP 0x33f00) (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_RDI))) $;
	Move (V_TEMP 0x34000) (BinOp OP_TIMES (Var (V_TEMP 0x33e80)) (Var (V_TEMP 0x33f00))) $;
	Move R_RDX (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x34000)) (Word 0 64))) $;
	Move (V_TEMP 0x34180) (Cast CAST_LOW 32 (BinOp OP_RSHIFT (Var (V_TEMP 0x34000)) (Word 32 64))) $;
	Move (V_TEMP 0x16080) (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_RDX))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x16080)) (Var (V_TEMP 0x34000)))) $;
	Move R_OF (Cast CAST_LOW 1 (Var R_CF)) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x0010114a: CMP ECX,EDX *)
(*    1053002: CMP ECX,EDX *)
| 0x10114a => Some (2,
	Move (V_TEMP 0x27e00) (Extract 31 0 (Var R_RCX)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x27e00)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x27e00)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x27e00)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x27e00)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x27f00) (BinOp OP_MINUS (Var (V_TEMP 0x27e00)) (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x27f00)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x27f00)) (Word 0x0 32))) $;
	Move (V_TEMP 0x15100) (BinOp OP_AND (Var (V_TEMP 0x27f00)) (Word 0xff 32)) $;
	Move (V_TEMP 0x15180) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x15100)))) $;
	Move (V_TEMP 0x15200) (BinOp OP_AND (Var (V_TEMP 0x15180)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x15200)) (Word 0x0 8)))
)

(* 0x0010114c: JGE 0x0010115f *)
(*    1053004: JGE 0x0010115f *)
| 0x10114c => Some (2,
	Move (V_TEMP 0xeb80) (BinOp OP_EQ (Var R_OF) (Var R_SF)) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xeb80))) (
		Jmp (Word 0x10115f 64)
	) (* else *) (
		Nop
	)
)

(* 0x0010114e: NOP *)
(*    1053006: NOP *)
| 0x10114e => Some (2,
	Nop
)

(* 0x00101150: SUB EAX,0x1 *)
(*    1053008: SUB EAX,0x1 *)
| 0x101150 => Some (3,
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RAX)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Word 0x1 32) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move R_RAX (Cast CAST_SIGNED 64 (BinOp OP_MINUS (Extract 31 0 (Var R_RAX)) (Word 0x1 32))) $;
	Move R_RAX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Extract 31 0 (Var R_RAX)) (Word 0x0 32))) $;
	Move (V_TEMP 0x15100) (BinOp OP_AND (Extract 31 0 (Var R_RAX)) (Word 0xff 32)) $;
	Move (V_TEMP 0x15180) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x15100)))) $;
	Move (V_TEMP 0x15200) (BinOp OP_AND (Var (V_TEMP 0x15180)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x15200)) (Word 0x0 8)))
)

(* 0x00101153: MOV ECX,EAX *)
(*    1053011: MOV ECX,EAX *)
| 0x101153 => Some (2,
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x00101155: LEA EDX,[RAX + RAX*0x1] *)
(*    1053013: LEA EDX,[RAX + RAX*0x1] *)
| 0x101155 => Some (3,
	Move (V_TEMP 0x4600) (BinOp OP_TIMES (Var R_RAX) (Word 0x1 64)) $;
	Move (V_TEMP 0x4700) (BinOp OP_PLUS (Var R_RAX) (Var (V_TEMP 0x4600))) $;
	Move R_RDX (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x4700)) (Word 0 64))) $;
	Move R_RDX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RDX)))
)

(* 0x00101158: IMUL ECX,EAX *)
(*    1053016: IMUL ECX,EAX *)
| 0x101158 => Some (3,
	Move (V_TEMP 0x33e80) (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move (V_TEMP 0x33f00) (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_RAX))) $;
	Move (V_TEMP 0x34000) (BinOp OP_TIMES (Var (V_TEMP 0x33e80)) (Var (V_TEMP 0x33f00))) $;
	Move R_RCX (Cast CAST_LOW 64 (BinOp OP_RSHIFT (Var (V_TEMP 0x34000)) (Word 0 64))) $;
	Move (V_TEMP 0x34180) (Cast CAST_LOW 32 (BinOp OP_RSHIFT (Var (V_TEMP 0x34000)) (Word 32 64))) $;
	Move (V_TEMP 0x16080) (Cast CAST_SIGNED 64 (Extract 31 0 (Var R_RCX))) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_NEQ (Var (V_TEMP 0x16080)) (Var (V_TEMP 0x34000)))) $;
	Move R_OF (Cast CAST_LOW 1 (Var R_CF)) $;
	Move R_RCX (Cast CAST_UNSIGNED 64 (Extract 31 0 (Var R_RCX)))
)

(* 0x0010115b: CMP ECX,EDX *)
(*    1053019: CMP ECX,EDX *)
| 0x10115b => Some (2,
	Move (V_TEMP 0x27e00) (Extract 31 0 (Var R_RCX)) $;
	Move R_CF (Cast CAST_LOW 1 (BinOp OP_LT (Var (V_TEMP 0x27e00)) (Extract 31 0 (Var R_RDX)))) $;
	Move R_OF (Cast CAST_LOW 1 (Cast CAST_LOW 8 (BinOp OP_AND (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (Var (V_TEMP 0x27e00)) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x27e00)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32))) (BinOp OP_XOR (BinOp OP_XOR (BinOp OP_AND (BinOp OP_RSHIFT (BinOp OP_MINUS (Var (V_TEMP 0x27e00)) (Extract 31 0 (Var R_RDX))) (Word 31 32)) (Word 1 32)) (BinOp OP_AND (BinOp OP_RSHIFT (Extract 31 0 (Var R_RDX)) (Word 31 32)) (Word 1 32))) (Word 1 32))))) $;
	Move (V_TEMP 0x27f00) (BinOp OP_MINUS (Var (V_TEMP 0x27e00)) (Extract 31 0 (Var R_RDX))) $;
	Move R_SF (Cast CAST_LOW 1 (BinOp OP_SLT (Var (V_TEMP 0x27f00)) (Word 0x0 32))) $;
	Move R_ZF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x27f00)) (Word 0x0 32))) $;
	Move (V_TEMP 0x15100) (BinOp OP_AND (Var (V_TEMP 0x27f00)) (Word 0xff 32)) $;
	Move (V_TEMP 0x15180) (Cast CAST_LOW 8 (UnOp OP_POPCOUNT (Var (V_TEMP 0x15100)))) $;
	Move (V_TEMP 0x15200) (BinOp OP_AND (Var (V_TEMP 0x15180)) (Word 0x1 8)) $;
	Move R_PF (Cast CAST_LOW 1 (BinOp OP_EQ (Var (V_TEMP 0x15200)) (Word 0x0 8)))
)

(* 0x0010115d: JG 0x00101150 *)
(*    1053021: JG 0x00101150 *)
| 0x10115d => Some (2,
	Move (V_TEMP 0xed80) (UnOp OP_NOT (Var R_ZF)) $;
	Move (V_TEMP 0xee00) (BinOp OP_EQ (Var R_OF) (Var R_SF)) $;
	Move (V_TEMP 0xef00) (BinOp OP_AND (Var (V_TEMP 0xed80)) (Var (V_TEMP 0xee00))) $;
	If (Cast CAST_LOW 1 (Var (V_TEMP 0xef00))) (
		Jmp (Word 0x101150 64)
	) (* else *) (
		Nop
	)
)

(* 0x0010115f: RET *)
(*    1053023: RET *)
| 0x10115f => Some (1,
	Move R_RIP (Load (Var V_MEM64) (Var R_RSP) LittleE 8) $;
	Move R_RSP (BinOp OP_PLUS (Var R_RSP) (Word 0x8 64)) $;
	Jmp (Var R_RIP)
)

| _ => None
end.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *                                                         *
 *                  Well-typed Theorem                     *
 *                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)

Theorem welltyped: welltyped_prog x64typctx while_true_break_while_true_break_amd64.
Proof. Picinae_typecheck. Qed.

