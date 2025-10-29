From Picinae Require Import Picinae_riscv.
Require Import NArith ZArith.

Definition resolve_jalr_addr (offset : Z) (a : addr) : addr :=
        N.clearbit (ofZ 32 (Z.add offset (toZ 32 a))) 0.

Definition add_signed_offset (a : N) (o : Z) : N :=
    ofZ 32 (Z.add (toZ 32 a) o).

Definition add_signed_offset' (a o : N) : N :=
    ofZ 32 (Z.add (toZ 32 a) (toZ 32 o)).

Definition reg s n := match n with 0 => 0 | _ => s (rv_varid n) end.

Inductive cache_type : Type := Data | Instruction.

Module Type RVPedanticCPUTimingBehavior.
    Parameter cache : Type.
    Parameter clear_cache : cache.
    Parameter cache_step : store -> cache -> addr -> cache.
    Parameter cached : cache -> addr -> cache_type -> bool.

    (* === Instruction Timings === *)
    Parameter
        (* ==== I ISA Extension ==== *)
        (* ALU *)
            tadd taddi tslt tslti tsltu tsltiu
            txor txori tor tori tand tandi tsub tlui
            tauipc : N.
    Parameter
        (* Branches *)
            (* taken *)
                ttbeq ttbne ttblt ttbge ttbltu ttbgeu
            (* not taken *)
                tfbeq tfbne tfblt tfbge tfbltu tfbgeu
        (* Jump/call *)
            tjal tjalr : bool -> addr -> N.
    Parameter
        (* Load/store *)
            tlb tlh tlw tlbu tlhu tsb tsh tsw
            : bool -> N -> N.
    Parameter
        (* Data fence *)
            tfence tfencei : N.
    Parameter
        (* System *)
            tecall tebreak tmret : bool -> N. 
    Parameter 
        (* System *) 
            twfi
        (* ==== M ISA Extension ==== *)
        (* Multiplication *)
            tmul tmulh tmulhsu tmulhu
        (* Division *)
            tdiv tdivu trem tremu

        (* ==== Zbb ISA Extension ==== *)
        (* Logic with negate *)
            tandn torn txnor
        (* Integer max/min *)
            tmin tminu tmax tmaxu
        (* Sign/zero extension *)
            tsext_b tsext_h tzext
        (* OR-combine *)
            torc_b
        (* Byte-reverse *)
            trev8

        (* ==== Zicsr ISA Extension ==== *)
        (* System *)
            tcsrrw tcsrrwi
            tcsrrs tcsrrsi
            tcsrrc tcsrrci
    : N.

    (* These instr times need to be N->N because they could depend on state values *)
    Parameter
        (* ==== I ISA Extension ==== *)
        (* ALU Shifts *)
            tsll tslli tsrl tsrli tsra tsrai

        (* ==== Zbb ISA Extension ==== *)
        (* Bit count *)
            tclz tctz tcpop
        (* Bitwise rotation *)
            trol tror trori
    : N -> N.
End CPUTimingBehavior.
