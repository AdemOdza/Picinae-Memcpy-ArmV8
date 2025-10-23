def time_of_instr(mnemonic: str) -> str :
	match mnemonic:
		case "adc r16, i":
			return "1"
		case "adc r16,r16":
			return "1"
		case "adc r32, i":
			return "1"
		case "adc r32,r32":
			return "1"
		case "adc r64, i":
			return "1"
		case "adc r64,r64":
			return "1"
		case "adc r8, i":
			return "2"
		case "adc r8,r8":
			return "1"
		case "adc_wc":
			return "2"
		case "adcx r32,r32":
			return "1"
		case "adcx r64,r64":
			return "1"
		case "adcx_wc":
			return "1"
		case "add [m]":
			return "5"
		case "add r16, i":
			return "1"
		case "add r16,r16":
			return "1"
		case "add r32, i":
			return "1"
		case "add r32,r32":
			return "1"
		case "add r64, i":
			return "1"
		case "add r64,r64":
			return "1"
		case "add r8, i":
			return "1"
		case "add r8,r8":
			return "1"
		case "add_wc":
			return "5"
		case "addps r128,r128":
			return "4"
		case "addps_wc":
			return "4"
		case "addss r128,r128":
			return "4"
		case "addss_wc":
			return "4"
		case "addsubps r128,r128":
			return "4"
		case "addsubps_wc":
			return "4"
		case "adox r32,r32":
			return "1"
		case "adox r64,r64":
			return "1"
		case "adox_wc":
			return "1"
		case "aesdec xmm,xmm":
			return "4"
		case "aesdec_wc":
			return "4"
		case "aesdeclast xmm,xmm":
			return "4"
		case "aesdeclast_wc":
			return "4"
		case "aesenc xmm,xmm":
			return "4"
		case "aesenc_wc":
			return "4"
		case "aesenclast xmm,xmm":
			return "4"
		case "aesenclast_wc":
			return "4"
		case "aesimc xmm,xmm":
			return "8"
		case "aesimc_wc":
			return "8"
		case "aeskeygenassist xmm,xmm ,0":
			return "12"
		case "aeskeygenassist_wc":
			return "12"
		case "and r16, i":
			return "1"
		case "and r16,r16":
			return "1"
		case "and r32, i":
			return "1"
		case "and r32,r32":
			return "1"
		case "and r64, i":
			return "1"
		case "and r64,r64":
			return "1"
		case "and r8, i":
			return "1"
		case "and r8,r8":
			return "1"
		case "and_wc":
			return "1"
		case "andn r32,r32,r32":
			return "1"
		case "andn r64,r64,r64":
			return "1"
		case "andn_wc":
			return "1"
		case "andps r128,r128":
			return "1"
		case "andps_wc":
			return "1"
		case "bextr r32,r32,r32":
			return "2"
		case "bextr r64,r64,r64":
			return "2"
		case "bextr_wc":
			return "2"
		case "blendpd r128,r128,i":
			return "1"
		case "blendpd_wc":
			return "1"
		case "blendps r128,r128,i":
			return "1"
		case "blendps_wc":
			return "1"
		case "blendvps r128,r128,xmm0":
			return "1"
		case "blendvps_wc":
			return "1"
		case "blsi r32,r32":
			return "1"
		case "blsi r64,r64":
			return "1"
		case "blsi_wc":
			return "1"
		case "blsmsk r32,r32":
			return "1"
		case "blsmsk r64,r64":
			return "1"
		case "blsmsk_wc":
			return "1"
		case "blsr r32,r32":
			return "1"
		case "blsr r64,r64":
			return "1"
		case "blsr_wc":
			return "1"
		case "bsf r16,r16":
			return "3"
		case "bsf r32,r32":
			return "3"
		case "bsf r64,r64":
			return "3"
		case "bsf_wc":
			return "3"
		case "bsr r16,r16":
			return "3"
		case "bsr r32,r32":
			return "3"
		case "bsr r64,r64":
			return "3"
		case "bsr_wc":
			return "3"
		case "bswap r32":
			return "1"
		case "bswap r64":
			return "2"
		case "bswap_wc":
			return "2"
		case "bt r16, 5":
			return "1"
		case "bt r32, 5":
			return "1"
		case "bt r32, ecx":
			return "1"
		case "bt r64, 5":
			return "1"
		case "bt_wc":
			return "1"
		case "btc r16, 5":
			return "1"
		case "btc r32, 5":
			return "1"
		case "btc r32, ecx":
			return "1"
		case "btc r64, 5":
			return "1"
		case "btc_wc":
			return "1"
		case "btr r16, 5":
			return "1"
		case "btr r32, 5":
			return "1"
		case "btr r32, ecx":
			return "1"
		case "btr r64, 5":
			return "1"
		case "btr_wc":
			return "1"
		case "bts r16, 5":
			return "1"
		case "bts r32, 5":
			return "1"
		case "bts r32, ecx":
			return "1"
		case "bts r64, 5":
			return "1"
		case "bts_wc":
			return "1"
		case "bzhi r32,r32,r32":
			return "1"
		case "bzhi r64,r64,r64":
			return "1"
		case "bzhi_wc":
			return "1"
		case "cbw":
			return "1"
		case "cbw_wc":
			return "1"
		case "cdq":
			return "1"
		case "cdq_wc":
			return "1"
		case "cdqe":
			return "1"
		case "cdqe_wc":
			return "1"
		case "clc":
			return "0"
		case "clc_wc":
			return "0"
		case "cld":
			return "4"
		case "cld_wc":
			return "4"
		case "cmc":
			return "1"
		case "cmc_wc":
			return "1"
		case "cmp r16, i":
			return "0"
		case "cmp r16,r16":
			return "0"
		case "cmp r32, i":
			return "0"
		case "cmp r32,r32":
			return "0"
		case "cmp r64, i":
			return "0"
		case "cmp r64,r64":
			return "0"
		case "cmp r8, i":
			return "0"
		case "cmp r8,r8":
			return "0"
		case "cmp_wc":
			return "0"
		case "cmpxchg [m16], r16":
			return "5"
		case "cmpxchg [m32], r32":
			return "5"
		case "cmpxchg [m64], r64":
			return "5"
		case "cmpxchg [m8], r8":
			return "5"
		case "cmpxchg16b [m]":
			return "26"
		case "cmpxchg16b_wc":
			return "26"
		case "cmpxchg8b [m]":
			return "12"
		case "cmpxchg8b_wc":
			return "12"
		case "cmpxchg_wc":
			return "5"
		case "comiss r128,r128":
			return "1"
		case "comiss_wc":
			return "1"
		case "cqo":
			return "1"
		case "cqo_wc":
			return "1"
		case "crc32 r32,r16":
			return "3"
		case "crc32 r32,r32":
			return "3"
		case "crc32 r32,r8":
			return "3"
		case "crc32_wc":
			return "3"
		case "cvtdq2pd r128,r128":
			return "5"
		case "cvtdq2pd xmm, xmm":
			return "5"
		case "cvtdq2pd xmm,xmm":
			return "5"
		case "cvtdq2pd_wc":
			return "5"
		case "cvtdq2ps r128,r128":
			return "4"
		case "cvtdq2ps xmm, xmm":
			return "4"
		case "cvtdq2ps xmm,xmm":
			return "4"
		case "cvtdq2ps_wc":
			return "4"
		case "cvtpd2dq r128,r128":
			return "5"
		case "cvtpd2dq xmm, xmm":
			return "5"
		case "cvtpd2dq_wc":
			return "5"
		case "cvtpd2pi mmx, xmm":
			return "5"
		case "cvtpd2pi_wc":
			return "5"
		case "cvtpd2ps r128,r128":
			return "5"
		case "cvtpd2ps xmm, xmm":
			return "5"
		case "cvtpd2ps xmm,xmm":
			return "5"
		case "cvtpd2ps_wc":
			return "5"
		case "cvtps2dq xmm, xmm":
			return "4"
		case "cvtps2dq_wc":
			return "4"
		case "cvtps2pd r128,r128":
			return "5"
		case "cvtps2pd xmm, xmm":
			return "5"
		case "cvtps2pd_wc":
			return "5"
		case "cvtps2pi mmx, xmm":
			return "6"
		case "cvtps2pi_wc":
			return "6"
		case "cvtsd2ss xmm,xmm":
			return "5"
		case "cvtsd2ss_wc":
			return "5"
		case "cvtsi2sd xmm, r32":
			return "6"
		case "cvtsi2sd xmm, r64":
			return "188"
		case "cvtsi2sd_wc":
			return "188"
		case "cvtss2sd xmm, xmm":
			return "5"
		case "cvtss2sd_wc":
			return "5"
		case "cvtss2si r32, xmm":
			return "6"
		case "cvtss2si r64, xmm":
			return "7"
		case "cvtss2si_wc":
			return "7"
		case "cvttps2dq r128,r128":
			return "4"
		case "cvttps2dq_wc":
			return "4"
		case "cwd":
			return "1"
		case "cwd_wc":
			return "1"
		case "cwde":
			return "1"
		case "cwde_wc":
			return "1"
		case "dec r16":
			return "1"
		case "dec r32":
			return "1"
		case "dec r64":
			return "1"
		case "dec r8":
			return "1"
		case "dec r8high":
			return "1"
		case "dec_wc":
			return "1"
		case "div , registersize 16":
			return "8"
		case "div , registersize 16, 1":
			return "8"
		case "div , registersize 32":
			return "9"
		case "div , registersize 32, 1":
			return "9"
		case "div , registersize 64":
			return "29"
		case "div , registersize 64, 1":
			return "12"
		case "div , registersize 8":
			return "8"
		case "div , registersize 8, 1":
			return "8"
		case "div_wc":
			return "29"
		case "divpd r128,r128 (best case)":
			return "13"
		case "divpd r128,r128 (worst case)":
			return "14"
		case "divpd_wc":
			return "14"
		case "divps r128,r128 (best case)":
			return "11"
		case "divps r128,r128 (worst case)":
			return "11"
		case "divps_wc":
			return "11"
		case "divsd r128,r128 (best case)":
			return "13"
		case "divsd r128,r128 (worst case)":
			return "14"
		case "divsd_wc":
			return "14"
		case "divss r128,r128 (best case)":
			return "11"
		case "divss r128,r128 (worst case)":
			return "11"
		case "divss_wc":
			return "11"
		case "dppd r128,r128,i":
			return "9"
		case "dppd_wc":
			return "9"
		case "dpps r128,r128,i":
			return "13"
		case "dpps_wc":
			return "13"
		case "f2xm1":
			return "67"
		case "f2xm1 + fcmov":
			return "44"
		case "f2xm1_wc":
			return "67"
		case "fabs":
			return "1"
		case "fabs_wc":
			return "1"
		case "fadd":
			return "3"
		case "fadd_wc":
			return "3"
		case "fbld [m80]":
			return "158"
		case "fbld [m80] + fstp [m80]":
			return "25"
		case "fbld_wc":
			return "158"
		case "fbstp + fld [m64]":
			return "134"
		case "fbstp + fld [m80]":
			return "135"
		case "fbstp_wc":
			return "135"
		case "fchs":
			return "3"
		case "fchs_wc":
			return "3"
		case "fcomi + fcmov":
			return "4"
		case "fcomi_wc":
			return "4"
		case "fcos":
			return "128"
		case "fcos + fcmov":
			return "27"
		case "fcos_wc":
			return "128"
		case "fdiv":
			return "15"
		case "fdiv_wc":
			return "15"
		case "fistp [m16] + fild [m16]":
			return "6"
		case "fistp [m32]":
			return "6"
		case "fistp [m32] + fild [m32]":
			return "7"
		case "fistp [m64] + fild [m64]":
			return "6"
		case "fistp_wc":
			return "7"
		case "fld + fxch":
			return "53"
		case "fld [m32]":
			return "5"
		case "fld [m32] + fchs":
			return "2"
		case "fld [m32] + fstp [m32]":
			return "4"
		case "fld [m64]":
			return "1"
		case "fld [m64] + fstp [m64]":
			return "4"
		case "fld [m80]":
			return "1"
		case "fld [m80] + fstp [m80]":
			return "4"
		case "fld st0 + fstp":
			return "1"
		case "fld_wc":
			return "53"
		case "fldcw + fnstcw":
			return "4"
		case "fldcw_wc":
			return "4"
		case "fmul":
			return "5"
		case "fmul_wc":
			return "5"
		case "fnsave + frstor":
			return "174"
		case "fnsave_wc":
			return "174"
		case "fnstsw + test + fcmov":
			return "3"
		case "fnstsw [m16] + test + fcmov + fcom":
			return "3"
		case "fnstsw ax + test + fcmov":
			return "3"
		case "fnstsw ax + test + fcmov + 2*fld":
			return "2"
		case "fnstsw ax + test + fcmov + fcom":
			return "3"
		case "fnstsw_wc":
			return "3"
		case "fprem + fadd":
			return "17"
		case "fprem1 + fadd":
			return "31"
		case "fprem1_wc":
			return "31"
		case "fprem_wc":
			return "17"
		case "fptan + fadd":
			return "74"
		case "fptan + fstp":
			return "74"
		case "fptan_wc":
			return "74"
		case "fsin + fadd":
			return "61"
		case "fsin_wc":
			return "61"
		case "fsincos + fadd":
			return "72"
		case "fsincos_wc":
			return "72"
		case "fsqrt + fadd":
			return "12"
		case "fsqrt_wc":
			return "12"
		case "fst st":
			return "1"
		case "fst_wc":
			return "1"
		case "fstp [m32]":
			return "4"
		case "fstp fstp + fld":
			return "1"
		case "fstp_wc":
			return "4"
		case "fxch":
			return "1"
		case "fxch_wc":
			return "1"
		case "fxsave + fxrstor":
			return "124"
		case "fxsave_wc":
			return "124"
		case "fxtract + fadd":
			return "7"
		case "fxtract_wc":
			return "7"
		case "fyl2x + fld":
			return "52"
		case "fyl2x_wc":
			return "52"
		case "fyl2xp1 + fld":
			return "75"
		case "fyl2xp1_wc":
			return "75"
		case "haddps r128,r128":
			return "6"
		case "haddps_wc":
			return "6"
		case "hsubpd r128,r128":
			return "6"
		case "hsubpd_wc":
			return "6"
		case "idiv , registersize 16":
			return "8"
		case "idiv , registersize 16, 1":
			return "8"
		case "idiv , registersize 32":
			return "9"
		case "idiv , registersize 32, 1":
			return "9"
		case "idiv , registersize 64":
			return "31"
		case "idiv , registersize 64, 1":
			return "14"
		case "idiv , registersize 8":
			return "8"
		case "idiv , registersize 8, 1":
			return "8"
		case "idiv_wc":
			return "31"
		case "imul , registersize 16":
			return "4"
		case "imul , registersize 32":
			return "4"
		case "imul , registersize 64":
			return "3"
		case "imul , registersize 8":
			return "3"
		case "imul , regsize 16, numop 2":
			return "3"
		case "imul , regsize 16, numop 3":
			return "4"
		case "imul , regsize 32, numop 2":
			return "3"
		case "imul , regsize 32, numop 3":
			return "3"
		case "imul , regsize 64, numop 2":
			return "3"
		case "imul , regsize 64, numop 3":
			return "3"
		case "imul r16,r16":
			return "3"
		case "imul r32,r32":
			return "3"
		case "imul r64,r64":
			return "3"
		case "imul_wc":
			return "4"
		case "inc + sbb":
			return "5"
		case "inc r16":
			return "1"
		case "inc r32":
			return "1"
		case "inc r64":
			return "1"
		case "inc r8":
			return "1"
		case "inc r8high":
			return "1"
		case "inc_wc":
			return "5"
		case "insertps":
			return "4"
		case "insertps xmm,xmm,i":
			return "1"
		case "insertps_wc":
			return "4"
		case "jg_addr":
			return "1"
		case "jge_addr":
			return "1"
		case "jle_addr":
			return "5"
		case "jmp_addr":
			return "1"
		case "jnc_addr":
			return "1"
		case "jnz_addr":
			return "1"
		case "jz_addr":
			return "1"
		case "ldmxcsr + stmccsr":
			return "4"
		case "ldmxcsr_wc":
			return "4"
		case "lea r16,[r64+0*rsi+(0 bytes)]":
			return "2"
		case "lea r16,[r64+0*rsi+(0 bytes)] + mov,":
			return "1"
		case "lea r16,[r64+0*rsi+(1 bytes)]":
			return "2"
		case "lea r16,[r64+0*rsi+(1 bytes)] + mov,":
			return "1"
		case "lea r16,[r64+0*rsi+(4 bytes)]":
			return "2"
		case "lea r16,[r64+1*rsi+(0 bytes)]":
			return "2"
		case "lea r16,[r64+1*rsi+(1 bytes)]":
			return "4"
		case "lea r16,[r64+1*rsi+(4 bytes)]":
			return "4"
		case "lea r16,[r64+4*rsi+(0 bytes)]":
			return "2"
		case "lea r16,[r64+4*rsi+(0 bytes)] + mov,":
			return "1"
		case "lea r16,[r64+4*rsi+(1 bytes)]":
			return "4"
		case "lea r16,[r64+4*rsi+(1 bytes)] + mov,":
			return "2"
		case "lea r16,[r64+4*rsi+(4 bytes)]":
			return "4"
		case "lea r32,[4*esi+(0 bytes)]":
			return "1"
		case "lea r32,[4*esi+(1 bytes)]":
			return "1"
		case "lea r32,[4*esi+(4 bytes)]":
			return "1"
		case "lea r32,[r64+0*rsi+(0 bytes)]":
			return "1"
		case "lea r32,[r64+0*rsi+(0 bytes)] + add,":
			return "1"
		case "lea r32,[r64+0*rsi+(0 bytes)] + mov,":
			return "1"
		case "lea r32,[r64+0*rsi+(1 bytes)]":
			return "1"
		case "lea r32,[r64+0*rsi+(1 bytes)] + mov,":
			return "1"
		case "lea r32,[r64+0*rsi+(4 bytes)]":
			return "1"
		case "lea r32,[r64+0*rsi+(4 bytes)] + add,":
			return "1"
		case "lea r32,[r64+1*rsi+(0 bytes)]":
			return "1"
		case "lea r32,[r64+1*rsi+(1 bytes)]":
			return "3"
		case "lea r32,[r64+1*rsi+(4 bytes)]":
			return "3"
		case "lea r32,[r64+4*rsi+(0 bytes)]":
			return "1"
		case "lea r32,[r64+4*rsi+(0 bytes)] + add,":
			return "1"
		case "lea r32,[r64+4*rsi+(0 bytes)] + mov,":
			return "1"
		case "lea r32,[r64+4*rsi+(1 bytes)]":
			return "3"
		case "lea r32,[r64+4*rsi+(1 bytes)] + mov,":
			return "2"
		case "lea r32,[r64+4*rsi+(4 bytes)]":
			return "3"
		case "lea r32,[r64+4*rsi+(4 bytes)] + add,":
			return "2"
		case "lea r64,[r64+0*rsi+(0 bytes)]":
			return "1"
		case "lea r64,[r64+0*rsi+(0 bytes)] + add,":
			return "1"
		case "lea r64,[r64+0*rsi+(0 bytes)] + mov,":
			return "1"
		case "lea r64,[r64+0*rsi+(1 bytes)]":
			return "1"
		case "lea r64,[r64+0*rsi+(1 bytes)] + mov,":
			return "1"
		case "lea r64,[r64+0*rsi+(4 bytes)]":
			return "1"
		case "lea r64,[r64+0*rsi+(4 bytes)] + add,":
			return "1"
		case "lea r64,[r64+1*rsi+(0 bytes)]":
			return "1"
		case "lea r64,[r64+1*rsi+(1 bytes)]":
			return "3"
		case "lea r64,[r64+1*rsi+(4 bytes)]":
			return "3"
		case "lea r64,[r64+4*rsi+(0 bytes)]":
			return "1"
		case "lea r64,[r64+4*rsi+(0 bytes)] + add,":
			return "1"
		case "lea r64,[r64+4*rsi+(0 bytes)] + mov,":
			return "1"
		case "lea r64,[r64+4*rsi+(1 bytes)]":
			return "3"
		case "lea r64,[r64+4*rsi+(1 bytes)] + mov,":
			return "2"
		case "lea r64,[r64+4*rsi+(4 bytes)]":
			return "3"
		case "lea r64,[r64+4*rsi+(4 bytes)] + add,":
			return "140"
		case "lea_r32_addr":
			return "1"
		case "lea_wc":
			return "140"
		case "lfence":
			return "4"
		case "lfence_wc":
			return "4"
		case "lock add [m]":
			return "18"
		case "lock cmpxchg [m16], r16":
			return "19"
		case "lock cmpxchg [m32], r32":
			return "22"
		case "lock cmpxchg [m64], r64":
			return "18"
		case "lock cmpxchg [m8], r8":
			return "18"
		case "lock cmpxchg8b [m]":
			return "19"
		case "lock xadd [m16], r16":
			return "18"
		case "lock xadd [m32], r32":
			return "19"
		case "lock xadd [m64], r64":
			return "21"
		case "lock xadd [m8], r8":
			return "18"
		case "lock_wc":
			return "22"
		case "lzcnt r16,r16":
			return "3"
		case "lzcnt r32,r32":
			return "3"
		case "lzcnt r64,r64":
			return "3"
		case "lzcnt_wc":
			return "3"
		case "maskmovdqu r,r (pattern 0x00) + movq":
			return "9"
		case "maskmovdqu r,r (pattern 0x02) + movq":
			return "214"
		case "maskmovdqu r,r (pattern 0x33) + movq":
			return "201"
		case "maskmovdqu r,r (pattern 0x55) + movq":
			return "212"
		case "maskmovdqu r,r (pattern 0xff) + movq":
			return "208"
		case "maskmovdqu_wc":
			return "214"
		case "maskmovq r,r (pattern 0x00) + movq":
			return "10"
		case "maskmovq r,r (pattern 0x02) + movq":
			return "190"
		case "maskmovq r,r (pattern 0x33) + movq":
			return "206"
		case "maskmovq r,r (pattern 0x55) + movq":
			return "192"
		case "maskmovq r,r (pattern 0xff) + movq":
			return "201"
		case "maskmovq_wc":
			return "206"
		case "maxpd r128,r128":
			return "4"
		case "maxpd xmm,xmm":
			return "5"
		case "maxpd_wc":
			return "5"
		case "maxps xmm,xmm":
			return "6"
		case "maxps_wc":
			return "6"
		case "maxss r128,r128":
			return "4"
		case "maxss_wc":
			return "4"
		case "mfence":
			return "55"
		case "mfence_wc":
			return "55"
		case "minps r128,r128":
			return "4"
		case "minps_wc":
			return "4"
		case "minsd r128,r128":
			return "4"
		case "minsd_wc":
			return "4"
		case "mov":
			return "4"
		case "mov m16, r16":
			return "3"
		case "mov m32, r32":
			return "2"
		case "mov m64, r64":
			return "2"
		case "mov m8, r8":
			return "3"
		case "mov m8, r8h":
			return "2"
		case "mov r16, i":
			return "1"
		case "mov r16,r16":
			return "1"
		case "mov r32, i":
			return "0"
		case "mov r32,r32":
			return "1"
		case "mov r64, i":
			return "0"
		case "mov r64,r64":
			return "1"
		case "mov r8, i":
			return "1"
		case "mov r8,r8":
			return "1"
		case "mov r8h, m8":
			return "2"
		case "mov r8h, r8":
			return "1"
		case "mov r8h, r8h":
			return "1"
		case "mov r8h,r8h":
			return "1"
		case "mov_wc":
			return "4"
		case "movapd m128, xmm":
			return "2"
		case "movapd r128,r128":
			return "1"
		case "movapd_wc":
			return "2"
		case "movaps m128, xmm":
			return "2"
		case "movaps r128,r128":
			return "1"
		case "movaps xmm, m128":
			return "192"
		case "movaps_wc":
			return "192"
		case "movd mmx, r32":
			return "2"
		case "movd r128,r21":
			return "3"
		case "movd xmm, m32":
			return "2"
		case "movd xmm, r32":
			return "2"
		case "movd_wc":
			return "3"
		case "movddup r128,r128":
			return "1"
		case "movddup_wc":
			return "1"
		case "movdq2q mmx, xmm":
			return "2"
		case "movdq2q_wc":
			return "2"
		case "movdqa m128, xmm":
			return "2"
		case "movdqa r128,r128":
			return "1"
		case "movdqa_wc":
			return "2"
		case "movdqu [m],xmm":
			return "3"
		case "movdqu m128, xmm":
			return "3"
		case "movdqu r128,r128":
			return "1"
		case "movdqu_wc":
			return "3"
		case "movhps m64, xmm":
			return "4"
		case "movhps_wc":
			return "4"
		case "movlhps xmm, xmm":
			return "1"
		case "movlhps xmm,xmm":
			return "1"
		case "movlhps_wc":
			return "1"
		case "movlpd m, xmm":
			return "4"
		case "movlpd_wc":
			return "4"
		case "movlps m64, xmm":
			return "4"
		case "movlps_wc":
			return "4"
		case "movmskpd r32, xmm":
			return "2"
		case "movmskpd_wc":
			return "2"
		case "movmskps r32, xmm":
			return "2"
		case "movmskps_wc":
			return "2"
		case "movntdq m128, xmm":
			return "186"
		case "movntdq_wc":
			return "186"
		case "movntdqa xmm, m":
			return "2"
		case "movntdqa_wc":
			return "2"
		case "movnti m32, r32":
			return "199"
		case "movnti_wc":
			return "199"
		case "movntpd m128, xmm":
			return "201"
		case "movntpd_wc":
			return "201"
		case "movntq m64, mmx":
			return "192"
		case "movntq_wc":
			return "192"
		case "movq m64, mmx":
			return "4"
		case "movq m64, xmm":
			return "3"
		case "movq mmx, r64":
			return "2"
		case "movq r128,r128":
			return "1"
		case "movq r64, xmm":
			return "3"
		case "movq r64,r64":
			return "1"
		case "movq xmm, m64":
			return "2"
		case "movq xmm, r64":
			return "3"
		case "movq_wc":
			return "4"
		case "movsd m64, xmm":
			return "2"
		case "movsd xmm, xmm":
			return "1"
		case "movsd xmm,xmm":
			return "1"
		case "movsd_wc":
			return "2"
		case "movshdup r128,r128":
			return "1"
		case "movshdup_wc":
			return "1"
		case "movsldup r128,r128":
			return "1"
		case "movsldup_wc":
			return "1"
		case "movss":
			return "4"
		case "movss m32, xmm":
			return "4"
		case "movss xmm, xmm":
			return "1"
		case "movss xmm,xmm":
			return "1"
		case "movss_wc":
			return "4"
		case "movsx r16,[m8]":
			return "3"
		case "movsx r16,r8":
			return "1"
		case "movsx r32,[m16]":
			return "2"
		case "movsx r32,[m8]":
			return "2"
		case "movsx r32,r16":
			return "1"
		case "movsx r32,r8":
			return "1"
		case "movsx r64,[m16]":
			return "2"
		case "movsx r64,[m8]":
			return "2"
		case "movsx r64,r16":
			return "1"
		case "movsx r64,r8":
			return "1"
		case "movsx_wc":
			return "3"
		case "movsxd r64,[m32]":
			return "2"
		case "movsxd r64,r32":
			return "1"
		case "movsxd_wc":
			return "2"
		case "movupd [m],xmm":
			return "3"
		case "movupd r128,r128":
			return "1"
		case "movupd_wc":
			return "3"
		case "movups [m],xmm":
			return "2"
		case "movups r128,r128":
			return "1"
		case "movups_wc":
			return "2"
		case "movzx r16,[m8]":
			return "3"
		case "movzx r16,r8":
			return "1"
		case "movzx r32,[m16]":
			return "2"
		case "movzx r32,[m8]":
			return "2"
		case "movzx r32,r16":
			return "1"
		case "movzx r32,r8":
			return "0"
		case "movzx r64,[m16]":
			return "2"
		case "movzx r64,[m8]":
			return "2"
		case "movzx r64,r16":
			return "1"
		case "movzx r64,r8":
			return "0"
		case "movzx_wc":
			return "3"
		case "mpsadbw r128,r128":
			return "4"
		case "mpsadbw_wc":
			return "4"
		case "mul , registersize 16":
			return "4"
		case "mul , registersize 32":
			return "4"
		case "mul , registersize 64":
			return "3"
		case "mul , registersize 8":
			return "3"
		case "mul_wc":
			return "4"
		case "mulpd r128,r128":
			return "4"
		case "mulpd_wc":
			return "4"
		case "mulps r128,r128":
			return "4"
		case "mulps_wc":
			return "4"
		case "mulsd r128,r128":
			return "4"
		case "mulsd_wc":
			return "4"
		case "mulss r128,r128":
			return "4"
		case "mulss_wc":
			return "4"
		case "mulx r32,r32,r32":
			return "4"
		case "mulx r64,r64,r64":
			return "4"
		case "mulx_wc":
			return "4"
		case "neg r16":
			return "1"
		case "neg r32":
			return "1"
		case "neg r64":
			return "1"
		case "neg r8":
			return "1"
		case "neg r8high":
			return "1"
		case "neg_wc":
			return "1"
		case "nop":
			return "0"
		case "nop_wc":
			return "0"
		case "not r16":
			return "1"
		case "not r32":
			return "1"
		case "not r64":
			return "1"
		case "not r8":
			return "1"
		case "not r8high":
			return "1"
		case "not_wc":
			return "1"
		case "or r16, i":
			return "1"
		case "or r16,r16":
			return "1"
		case "or r32, i":
			return "1"
		case "or r32,r32":
			return "1"
		case "or r64, i":
			return "1"
		case "or r64,r64":
			return "1"
		case "or r8, i":
			return "1"
		case "or r8,r8":
			return "1"
		case "or_wc":
			return "1"
		case "orpd r128,r128":
			return "1"
		case "orpd_wc":
			return "1"
		case "pabsb r128,r128":
			return "1"
		case "pabsb r64,r64":
			return "1"
		case "pabsb_wc":
			return "1"
		case "pabsd r128,r128":
			return "1"
		case "pabsd r64,r64":
			return "1"
		case "pabsd_wc":
			return "1"
		case "packssdw r128,r128":
			return "1"
		case "packssdw r64,r64":
			return "2"
		case "packssdw_wc":
			return "2"
		case "packsswb r128,r128":
			return "1"
		case "packsswb r64,r64":
			return "2"
		case "packsswb_wc":
			return "2"
		case "packusdw r128,r128":
			return "1"
		case "packusdw_wc":
			return "1"
		case "packuswb r128,r128":
			return "1"
		case "packuswb r64,r64":
			return "2"
		case "packuswb_wc":
			return "2"
		case "paddd r128,r128":
			return "1"
		case "paddd r64,r64":
			return "1"
		case "paddd_wc":
			return "1"
		case "paddq r128,r128":
			return "1"
		case "paddq r64,r64":
			return "1"
		case "paddq_wc":
			return "1"
		case "paddusb r128,r128":
			return "1"
		case "paddusb r64,r64":
			return "1"
		case "paddusb_wc":
			return "1"
		case "paddw r128,r128":
			return "1"
		case "paddw r64,r64":
			return "1"
		case "paddw_wc":
			return "1"
		case "palignr r128,r128":
			return "1"
		case "palignr r64,r64,i":
			return "1"
		case "palignr_wc":
			return "1"
		case "pand r128,r128":
			return "1"
		case "pand r64,r64":
			return "1"
		case "pand_wc":
			return "1"
		case "pandn r128,r128":
			return "1"
		case "pandn r64,r64":
			return "1"
		case "pandn_wc":
			return "1"
		case "pause":
			return "140"
		case "pause_wc":
			return "140"
		case "pavgb r128,r128":
			return "1"
		case "pavgb r64,r64":
			return "1"
		case "pavgb_wc":
			return "1"
		case "pavgw r128,r128":
			return "1"
		case "pavgw r64,r64":
			return "1"
		case "pavgw_wc":
			return "1"
		case "pblendvb r128,r128,xmm0":
			return "2"
		case "pblendvb_wc":
			return "2"
		case "pblendw r128,r128":
			return "1"
		case "pblendw_wc":
			return "1"
		case "pclmulqdq r128,r128":
			return "7"
		case "pclmulqdq xmm,xmm,0":
			return "7"
		case "pclmulqdq xmm,xmm,1":
			return "7"
		case "pclmulqdq xmm,xmm,2":
			return "7"
		case "pclmulqdq xmm,xmm,3":
			return "7"
		case "pclmulqdq_wc":
			return "7"
		case "pcmpeqb r128,r128":
			return "1"
		case "pcmpeqb r64,r64":
			return "1"
		case "pcmpeqb_wc":
			return "1"
		case "pcmpeqd r128,r128":
			return "1"
		case "pcmpeqd r64,r64":
			return "1"
		case "pcmpeqd_wc":
			return "1"
		case "pcmpeqq r128,r128":
			return "1"
		case "pcmpeqq_wc":
			return "1"
		case "pcmpeqw r128,r128":
			return "1"
		case "pcmpeqw r64,r64":
			return "1"
		case "pcmpeqw_wc":
			return "1"
		case "pcmpestri r128,r128":
			return "5"
		case "pcmpestri_wc":
			return "5"
		case "pcmpestrm r128,r128":
			return "9"
		case "pcmpestrm_wc":
			return "9"
		case "pcmpgtd r128,r128":
			return "1"
		case "pcmpgtd r64,r64":
			return "1"
		case "pcmpgtd_wc":
			return "1"
		case "pcmpgtq r128,r128":
			return "3"
		case "pcmpgtq_wc":
			return "3"
		case "pcmpgtw r128,r128":
			return "1"
		case "pcmpgtw r64,r64":
			return "1"
		case "pcmpgtw_wc":
			return "1"
		case "pcmpistri r128,r128":
			return "3"
		case "pcmpistri_wc":
			return "3"
		case "pcmpistrm r128,r128":
			return "9"
		case "pcmpistrm_wc":
			return "9"
		case "pdep r32,r32,r32":
			return "3"
		case "pdep r64,r64,r64":
			return "3"
		case "pdep_wc":
			return "3"
		case "pext r32,r32,r32":
			return "3"
		case "pext r64,r64,r64":
			return "3"
		case "pext_wc":
			return "3"
		case "pextrb r32, xmm,1":
			return "2"
		case "pextrb_wc":
			return "2"
		case "pextrd r32, xmm,1":
			return "3"
		case "pextrd_wc":
			return "3"
		case "pextrw r32, mmx,1":
			return "2"
		case "pextrw r32, xmm,1":
			return "2"
		case "pextrw_wc":
			return "2"
		case "phaddsw r128,r128":
			return "3"
		case "phaddsw r64,r64":
			return "3"
		case "phaddsw_wc":
			return "3"
		case "phaddw r128,r128":
			return "3"
		case "phaddw r64,r64":
			return "3"
		case "phaddw_wc":
			return "3"
		case "phminposuw r128,r128":
			return "4"
		case "phminposuw_wc":
			return "4"
		case "phsubd r128,r128":
			return "3"
		case "phsubd r64,r64":
			return "3"
		case "phsubd_wc":
			return "3"
		case "pinsrb xmm, r32,1":
			return "3"
		case "pinsrb_wc":
			return "3"
		case "pinsrd xmm, r32,1":
			return "3"
		case "pinsrd_wc":
			return "3"
		case "pinsrw mmx, r32,1":
			return "2"
		case "pinsrw xmm, r32,1":
			return "2"
		case "pinsrw_wc":
			return "2"
		case "pmaddubsw r128,r128":
			return "5"
		case "pmaddubsw r64,r64":
			return "5"
		case "pmaddubsw_wc":
			return "5"
		case "pmaddwd r128,r128":
			return "5"
		case "pmaddwd r64,r64":
			return "5"
		case "pmaddwd_wc":
			return "5"
		case "pmaxsw r128,r128":
			return "1"
		case "pmaxsw r64,r64":
			return "1"
		case "pmaxsw_wc":
			return "1"
		case "pmaxud r128,r128":
			return "1"
		case "pmaxud_wc":
			return "1"
		case "pmaxuw r128,r128":
			return "1"
		case "pmaxuw_wc":
			return "1"
		case "pminsb r128,r128":
			return "1"
		case "pminsb_wc":
			return "1"
		case "pminub r128,r128":
			return "1"
		case "pminub r64,r64":
			return "1"
		case "pminub_wc":
			return "1"
		case "pmovmskb r32, xmm":
			return "2"
		case "pmovmskb_wc":
			return "2"
		case "pmuldq r128,r128":
			return "5"
		case "pmuldq_wc":
			return "5"
		case "pmulhrsw r128,r128":
			return "5"
		case "pmulhrsw r64,r64":
			return "5"
		case "pmulhrsw_wc":
			return "5"
		case "pmulhuw r128,r128":
			return "5"
		case "pmulhuw r64,r64":
			return "5"
		case "pmulhuw_wc":
			return "5"
		case "pmulld r128,r128":
			return "10"
		case "pmulld_wc":
			return "10"
		case "pmullw r128,r128":
			return "5"
		case "pmullw r64,r64":
			return "5"
		case "pmullw_wc":
			return "5"
		case "pmuludq r128,r128":
			return "5"
		case "pmuludq r64,r64":
			return "5"
		case "pmuludq_wc":
			return "5"
		case "popcnt r16,r16":
			return "3"
		case "popcnt r32,r32":
			return "3"
		case "popcnt r64,r64":
			return "3"
		case "popcnt_wc":
			return "3"
		case "por xmm,xmm":
			return "5"
		case "por_wc":
			return "5"
		case "psadbw r128,r128":
			return "3"
		case "psadbw r64,r64":
			return "3"
		case "psadbw_wc":
			return "3"
		case "pshufb r128,r128":
			return "1"
		case "pshufb r64,r64":
			return "3"
		case "pshufb_wc":
			return "3"
		case "pshufd r128,r128":
			return "1"
		case "pshufd_wc":
			return "1"
		case "pshufhw r128,r128":
			return "1"
		case "pshufhw_wc":
			return "1"
		case "pshuflw r128,r128":
			return "1"
		case "pshuflw_wc":
			return "1"
		case "pshufw r64,r64,i":
			return "1"
		case "pshufw_wc":
			return "1"
		case "psignw r128,r128":
			return "1"
		case "psignw r64,r64":
			return "1"
		case "psignw_wc":
			return "1"
		case "pslld r128,r128":
			return "2"
		case "pslld r64,r64":
			return "1"
		case "pslld_wc":
			return "2"
		case "pslldq r128,i":
			return "1"
		case "pslldq_wc":
			return "1"
		case "psllq r128,r128":
			return "2"
		case "psllq r64,r64":
			return "1"
		case "psllq_wc":
			return "2"
		case "psllw r128,i":
			return "1"
		case "psllw r128,r128":
			return "2"
		case "psllw r64,i":
			return "1"
		case "psllw r64,r64":
			return "1"
		case "psllw_wc":
			return "2"
		case "psrad r128,i":
			return "1"
		case "psrad r64,i":
			return "1"
		case "psrad_wc":
			return "1"
		case "psraw r128,i":
			return "1"
		case "psraw r128,r128":
			return "2"
		case "psraw r64,i":
			return "1"
		case "psraw r64,r64":
			return "1"
		case "psraw_wc":
			return "2"
		case "psrldq r128,i":
			return "1"
		case "psrldq_wc":
			return "1"
		case "psrlq r128,i":
			return "1"
		case "psrlq r128,r128":
			return "2"
		case "psrlq r64,i":
			return "1"
		case "psrlq r64,r64":
			return "1"
		case "psrlq_wc":
			return "2"
		case "ptest r128,r128":
			return "1"
		case "ptest xmm,xmm":
			return "2"
		case "ptest_wc":
			return "2"
		case "punpckhbw r128,r128":
			return "1"
		case "punpckhbw r64,r64":
			return "1"
		case "punpckhbw_wc":
			return "1"
		case "punpckhdq r128,r128":
			return "1"
		case "punpckhdq r64,r64":
			return "1"
		case "punpckhdq_wc":
			return "1"
		case "punpckhqdq r128,r128":
			return "1"
		case "punpckhqdq_wc":
			return "1"
		case "punpckhwd r128,r128":
			return "1"
		case "punpckhwd r64,r64":
			return "1"
		case "punpckhwd_wc":
			return "1"
		case "punpckldq r128,r128":
			return "1"
		case "punpckldq r64,r64":
			return "1"
		case "punpckldq_wc":
			return "1"
		case "punpcklqdq r128,r128":
			return "1"
		case "punpcklqdq_wc":
			return "1"
		case "rcl , 1 regsize 16":
			return "2"
		case "rcl , 1 regsize 32":
			return "2"
		case "rcl , 1 regsize 64":
			return "2"
		case "rcl , 1 regsize 8":
			return "2"
		case "rcl , 4 regsize 16":
			return "7"
		case "rcl , 4 regsize 32":
			return "7"
		case "rcl , 4 regsize 64":
			return "7"
		case "rcl , 4 regsize 8":
			return "7"
		case "rcl , cl regsize 16":
			return "7"
		case "rcl , cl regsize 32":
			return "7"
		case "rcl , cl regsize 64":
			return "7"
		case "rcl , cl regsize 8":
			return "7"
		case "rcl_wc":
			return "7"
		case "rcpps r128,r128":
			return "4"
		case "rcpps_wc":
			return "4"
		case "rcpss r128,r128":
			return "4"
		case "rcpss_wc":
			return "4"
		case "rcr , 1 regsize 16":
			return "2"
		case "rcr , 1 regsize 32":
			return "2"
		case "rcr , 1 regsize 64":
			return "2"
		case "rcr , 1 regsize 8":
			return "2"
		case "rcr , 4 regsize 16":
			return "6"
		case "rcr , 4 regsize 32":
			return "6"
		case "rcr , 4 regsize 64":
			return "6"
		case "rcr , 4 regsize 8":
			return "6"
		case "rcr , cl regsize 16":
			return "6"
		case "rcr , cl regsize 32":
			return "6"
		case "rcr , cl regsize 64":
			return "6"
		case "rcr , cl regsize 8":
			return "6"
		case "rcr_wc":
			return "6"
		case "ret":
			return "13"
		case "rol , 1 regsize 16":
			return "1"
		case "rol , 1 regsize 32":
			return "1"
		case "rol , 1 regsize 64":
			return "1"
		case "rol , 1 regsize 8":
			return "1"
		case "rol , 4 regsize 16":
			return "1"
		case "rol , 4 regsize 32":
			return "1"
		case "rol , 4 regsize 64":
			return "1"
		case "rol , 4 regsize 8":
			return "1"
		case "rol , cl regsize 16":
			return "2"
		case "rol , cl regsize 32":
			return "2"
		case "rol , cl regsize 64":
			return "2"
		case "rol , cl regsize 8":
			return "2"
		case "rol_wc":
			return "2"
		case "ror , 1 regsize 16":
			return "1"
		case "ror , 1 regsize 32":
			return "1"
		case "ror , 1 regsize 64":
			return "1"
		case "ror , 1 regsize 8":
			return "1"
		case "ror , 4 regsize 16":
			return "1"
		case "ror , 4 regsize 32":
			return "1"
		case "ror , 4 regsize 64":
			return "1"
		case "ror , 4 regsize 8":
			return "1"
		case "ror , cl regsize 16":
			return "2"
		case "ror , cl regsize 32":
			return "2"
		case "ror , cl regsize 64":
			return "2"
		case "ror , cl regsize 8":
			return "2"
		case "ror_wc":
			return "2"
		case "rorx r32,r32,imm":
			return "1"
		case "rorx r64,r64,imm":
			return "1"
		case "rorx_wc":
			return "1"
		case "roundpd r128,r128,i":
			return "8"
		case "roundpd_wc":
			return "8"
		case "roundps r128,r128,i":
			return "8"
		case "roundps_wc":
			return "8"
		case "roundsd r128,r128,i":
			return "8"
		case "roundsd_wc":
			return "8"
		case "roundss r128,r128,i":
			return "8"
		case "roundss_wc":
			return "8"
		case "rsqrtps r128,r128":
			return "4"
		case "rsqrtps_wc":
			return "4"
		case "rsqrtss r128,r128":
			return "4"
		case "rsqrtss_wc":
			return "4"
		case "sar , 1 regsize 16":
			return "1"
		case "sar , 1 regsize 32":
			return "1"
		case "sar , 1 regsize 64":
			return "1"
		case "sar , 1 regsize 8":
			return "1"
		case "sar , 4 regsize 16":
			return "1"
		case "sar , 4 regsize 32":
			return "1"
		case "sar , 4 regsize 64":
			return "1"
		case "sar , 4 regsize 8":
			return "1"
		case "sar , cl regsize 16":
			return "2"
		case "sar , cl regsize 32":
			return "2"
		case "sar , cl regsize 64":
			return "2"
		case "sar , cl regsize 8":
			return "2"
		case "sar_wc":
			return "2"
		case "sarx r32,r32,r32":
			return "1"
		case "sarx r64,r64,r64":
			return "1"
		case "sarx_wc":
			return "1"
		case "sbb + movd":
			return "3"
		case "sbb + vmovd":
			return "3"
		case "sbb r16, i":
			return "1"
		case "sbb r16,r16":
			return "1"
		case "sbb r32, i":
			return "1"
		case "sbb r32,r32":
			return "1"
		case "sbb r64, i":
			return "1"
		case "sbb r64,r64":
			return "1"
		case "sbb r8, i":
			return "2"
		case "sbb r8,r8":
			return "1"
		case "sbb_wc":
			return "3"
		case "sfence":
			return "6"
		case "sfence_wc":
			return "6"
		case "shl , 1 regsize 16":
			return "1"
		case "shl , 1 regsize 32":
			return "1"
		case "shl , 1 regsize 64":
			return "1"
		case "shl , 1 regsize 8":
			return "1"
		case "shl , 4 regsize 16":
			return "1"
		case "shl , 4 regsize 32":
			return "1"
		case "shl , 4 regsize 64":
			return "1"
		case "shl , 4 regsize 8":
			return "1"
		case "shl , cl regsize 16":
			return "2"
		case "shl , cl regsize 32":
			return "2"
		case "shl , cl regsize 64":
			return "2"
		case "shl , cl regsize 8":
			return "2"
		case "shl_wc":
			return "2"
		case "shld , 1 regsize 16":
			return "3"
		case "shld , 1 regsize 32":
			return "3"
		case "shld , 1 regsize 64":
			return "3"
		case "shld , 6 regsize 16":
			return "3"
		case "shld , 6 regsize 32":
			return "3"
		case "shld , 6 regsize 64":
			return "3"
		case "shld , cl regsize 16":
			return "3"
		case "shld , cl regsize 32":
			return "3"
		case "shld , cl regsize 64":
			return "3"
		case "shld_wc":
			return "3"
		case "shlx r32,r32,r32":
			return "1"
		case "shlx r64,r64,r64":
			return "1"
		case "shlx_wc":
			return "1"
		case "shr , 1 regsize 16":
			return "1"
		case "shr , 1 regsize 32":
			return "1"
		case "shr , 1 regsize 64":
			return "1"
		case "shr , 1 regsize 8":
			return "1"
		case "shr , 4 regsize 16":
			return "1"
		case "shr , 4 regsize 32":
			return "1"
		case "shr , 4 regsize 64":
			return "1"
		case "shr , 4 regsize 8":
			return "1"
		case "shr , cl regsize 16":
			return "2"
		case "shr , cl regsize 32":
			return "2"
		case "shr , cl regsize 64":
			return "2"
		case "shr , cl regsize 8":
			return "2"
		case "shr_wc":
			return "2"
		case "shrd , 1 regsize 16":
			return "3"
		case "shrd , 1 regsize 32":
			return "3"
		case "shrd , 1 regsize 64":
			return "3"
		case "shrd , 6 regsize 16":
			return "3"
		case "shrd , 6 regsize 32":
			return "3"
		case "shrd , 6 regsize 64":
			return "3"
		case "shrd , cl regsize 16":
			return "4"
		case "shrd , cl regsize 32":
			return "4"
		case "shrd , cl regsize 64":
			return "4"
		case "shrd_wc":
			return "4"
		case "shrx r32,r32,r32":
			return "1"
		case "shrx r64,r64,r64":
			return "1"
		case "shrx_wc":
			return "1"
		case "shufpd r128,r128,i":
			return "1"
		case "shufpd_wc":
			return "1"
		case "shufps r128,r128,i":
			return "1"
		case "shufps_wc":
			return "1"
		case "sqrtpd r128,r128 (best case)":
			return "15"
		case "sqrtpd r128,r128 (worst case)":
			return "16"
		case "sqrtpd_wc":
			return "16"
		case "sqrtps r128,r128 (best case)":
			return "12"
		case "sqrtps r128,r128 (worst case)":
			return "12"
		case "sqrtps_wc":
			return "12"
		case "sqrtsd r128,r128 (best case)":
			return "15"
		case "sqrtsd r128,r128 (worst case)":
			return "16"
		case "sqrtsd_wc":
			return "16"
		case "sqrtss r128,r128 (best case)":
			return "12"
		case "sqrtss r128,r128 (worst case)":
			return "12"
		case "sqrtss_wc":
			return "12"
		case "stc":
			return "0"
		case "stc_wc":
			return "0"
		case "std":
			return "4"
		case "std_wc":
			return "4"
		case "sub":
			return "150"
		case "sub r16, i":
			return "1"
		case "sub r16,r16":
			return "1"
		case "sub r32, i":
			return "1"
		case "sub r32,r32":
			return "1"
		case "sub r64, i":
			return "1"
		case "sub r64,r64":
			return "1"
		case "sub r8, i":
			return "1"
		case "sub r8,r8":
			return "1"
		case "sub_wc":
			return "150"
		case "subpd r128,r128":
			return "4"
		case "subpd_wc":
			return "4"
		case "subsd r128,r128":
			return "4"
		case "subsd_wc":
			return "4"
		case "test mode":
			return "14"
		case "test r16, i":
			return "3"
		case "test r16,r16":
			return "0"
		case "test r32, i":
			return "0"
		case "test r32,r32":
			return "0"
		case "test r64, i":
			return "0"
		case "test r64,r64":
			return "0"
		case "test r8, i":
			return "0"
		case "test r8,r8":
			return "0"
		case "test_wc":
			return "14"
		case "tzcnt r16,r16":
			return "3"
		case "tzcnt r32,r32":
			return "3"
		case "tzcnt r64,r64":
			return "3"
		case "tzcnt_wc":
			return "3"
		case "ucomisd r128,r128":
			return "1"
		case "ucomisd_wc":
			return "1"
		case "unpckhps r128,r128":
			return "1"
		case "unpckhps_wc":
			return "1"
		case "unpcklpd r128,r128":
			return "1"
		case "unpcklpd_wc":
			return "1"
		case "vcvtph2ps xmm, xmm":
			return "5"
		case "vcvtph2ps ymm, xmm":
			return "7"
		case "vcvtph2ps_wc":
			return "7"
		case "vcvtps2ph xmm,xmm,0":
			return "5"
		case "vcvtps2ph_wc":
			return "5"
		case "vextractf128 [m128],ymm,0 + vmovdqa x,[m]":
			return "4"
		case "vextractf128 [m128],ymm,1 + vmovdqa x,[m]":
			return "4"
		case "vextractf128 xmm,ymm,0":
			return "3"
		case "vextractf128 xmm,ymm,0 + vinserti128 y,y,x,1":
			return "3"
		case "vextractf128 xmm,ymm,1":
			return "4"
		case "vextractf128 xmm,ymm,1 + vinserti128 y,y,x,1":
			return "3"
		case "vextractf128 ymm,":
			return "3"
		case "vextractf128_wc":
			return "4"
		case "vextracti128 [m128],ymm,0 + vmovdqa x,[m]":
			return "4"
		case "vextracti128 [m128],ymm,1 + vmovdqa x,[m]":
			return "4"
		case "vextracti128 xmm,ymm,0":
			return "3"
		case "vextracti128 xmm,ymm,0 + vinserti128 y,y,x,1":
			return "3"
		case "vextracti128 xmm,ymm,1":
			return "3"
		case "vextracti128 xmm,ymm,1 + vinserti128 y,y,x,1":
			return "3"
		case "vextracti128_wc":
			return "4"
		case "vfmadd132pd r128,r128,r128":
			return "4"
		case "vfmadd132pd r256,r256,r256":
			return "4"
		case "vfmadd132pd_wc":
			return "4"
		case "vfmadd132ps r128,r128,r128":
			return "4"
		case "vfmadd132ps r256,r256,r256":
			return "4"
		case "vfmadd132ps_wc":
			return "4"
		case "vfmadd132sd r128,r128,r128":
			return "4"
		case "vfmadd132sd_wc":
			return "4"
		case "vfmadd132ss r128,r128,r128":
			return "4"
		case "vfmadd132ss_wc":
			return "4"
		case "vfmadd213ps r128,r128,r128":
			return "4"
		case "vfmadd213ps r256,r256,r256":
			return "4"
		case "vfmadd213ps_wc":
			return "4"
		case "vfmadd213ss r128,r128,r128":
			return "4"
		case "vfmadd213ss_wc":
			return "4"
		case "vfmadd231pd r128,r128,r128":
			return "4"
		case "vfmadd231pd r256,r256,r256":
			return "4"
		case "vfmadd231pd_wc":
			return "4"
		case "vfmadd231ps r128,r128,r128":
			return "4"
		case "vfmadd231ps r256,r256,r256":
			return "4"
		case "vfmadd231ps_wc":
			return "4"
		case "vfmadd231sd r128,r128,r128":
			return "4"
		case "vfmadd231sd_wc":
			return "4"
		case "vfmadd231ss r128,r128,r128":
			return "4"
		case "vfmadd231ss_wc":
			return "4"
		case "vfmsub132pd r128,r128,r128":
			return "4"
		case "vfmsub132pd r256,r256,r256":
			return "4"
		case "vfmsub132pd_wc":
			return "4"
		case "vfmsub132sd r128,r128,r128":
			return "4"
		case "vfmsub132sd_wc":
			return "4"
		case "vfmsub231pd r128,r128,r128":
			return "4"
		case "vfmsub231pd r256,r256,r256":
			return "4"
		case "vfmsub231pd_wc":
			return "4"
		case "vfmsub231sd r128,r128,r128":
			return "4"
		case "vfmsub231sd_wc":
			return "4"
		case "vfnmadd132pd r128,r128,r128":
			return "4"
		case "vfnmadd132pd r256,r256,r256":
			return "4"
		case "vfnmadd132pd_wc":
			return "4"
		case "vfnmadd132sd r128,r128,r128":
			return "4"
		case "vfnmadd132sd_wc":
			return "4"
		case "vfnmadd231pd r128,r128,r128":
			return "4"
		case "vfnmadd231pd r256,r256,r256":
			return "4"
		case "vfnmadd231pd_wc":
			return "4"
		case "vfnmadd231sd r128,r128,r128":
			return "4"
		case "vfnmadd231sd_wc":
			return "4"
		case "vfnmsub132pd r128,r128,r128":
			return "4"
		case "vfnmsub132pd r256,r256,r256":
			return "4"
		case "vfnmsub132pd_wc":
			return "4"
		case "vfnmsub132sd r128,r128,r128":
			return "4"
		case "vfnmsub132sd_wc":
			return "4"
		case "vfnmsub231pd r128,r128,r128":
			return "4"
		case "vfnmsub231pd r256,r256,r256":
			return "4"
		case "vfnmsub231pd_wc":
			return "4"
		case "vfnmsub231sd r128,r128,r128":
			return "4"
		case "vfnmsub231sd_wc":
			return "4"
		case "vinsertf128 y,y,x,1":
			return "3"
		case "vinsertf128 ymm,":
			return "3"
		case "vinsertf128 ymm,ymm,xmm,0":
			return "3"
		case "vinsertf128 ymm,ymm,xmm,0 + vextractf128 xmm,ymm,1":
			return "3"
		case "vinsertf128 ymm,ymm,xmm,0 + vextracti128 xmm,ymm,1":
			return "3"
		case "vinsertf128 ymm,ymm,xmm,1":
			return "3"
		case "vinsertf128 ymm,ymm,xmm,1 + vextractf128 xmm,ymm,1":
			return "4"
		case "vinsertf128 ymm,ymm,xmm,1 + vextracti128 xmm,ymm,1":
			return "3"
		case "vinsertf128_wc":
			return "4"
		case "vinserti128 ymm,xmm,xmm,1":
			return "3"
		case "vinserti128 ymm,ymm,xmm,0":
			return "3"
		case "vinserti128 ymm,ymm,xmm,1":
			return "3"
		case "vinserti128_wc":
			return "3"
		case "vpbroadcastb xmm,m8 + mov.. m8,xmm":
			return "3"
		case "vpbroadcastb xmm,xmm":
			return "1"
		case "vpbroadcastb ymm,m8 + mov.. m8,xmm":
			return "4"
		case "vpbroadcastb ymm,xmm":
			return "3"
		case "vpbroadcastb_wc":
			return "4"
		case "vpbroadcastd xmm,m32 + mov.. m32,xmm":
			return "2"
		case "vpbroadcastd xmm,xmm":
			return "1"
		case "vpbroadcastd ymm,m32 + mov.. m32,xmm":
			return "4"
		case "vpbroadcastd ymm,xmm":
			return "3"
		case "vpbroadcastd_wc":
			return "4"
		case "vpbroadcastq xmm,m64 + mov.. m64,xmm":
			return "2"
		case "vpbroadcastq xmm,xmm":
			return "1"
		case "vpbroadcastq ymm,m64 + mov.. m64,xmm":
			return "4"
		case "vpbroadcastq ymm,xmm":
			return "3"
		case "vpbroadcastq_wc":
			return "4"
		case "vpbroadcastw xmm,m16 + mov.. m16,xmm":
			return "3"
		case "vpbroadcastw xmm,xmm":
			return "1"
		case "vpbroadcastw ymm,m16 + mov.. m16,xmm":
			return "3"
		case "vpbroadcastw ymm,xmm":
			return "3"
		case "vpbroadcastw_wc":
			return "3"
		case "vperm2f128 r256,r256,r256,i":
			return "3"
		case "vperm2f128_wc":
			return "3"
		case "vpermilpd r128,r128,i":
			return "1"
		case "vpermilpd r128,r128,r128":
			return "1"
		case "vpermilpd r256,r256,i":
			return "1"
		case "vpermilpd r256,r256,r256":
			return "1"
		case "vpermilpd_wc":
			return "1"
		case "vpermilps r128,r128,i":
			return "1"
		case "vpermilps r128,r128,r128":
			return "1"
		case "vpermilps r256,r256,i":
			return "1"
		case "vpermilps r256,r256,r256":
			return "1"
		case "vpermilps_wc":
			return "1"
		case "vtestpd r128,r128 + sbb + movd":
			return "2"
		case "vtestpd_wc":
			return "2"
		case "vtestps r128,r128 + sbb + movd":
			return "2"
		case "vtestps_wc":
			return "2"
		case "xadd [m16], r16":
			return "5"
		case "xadd [m32], r32":
			return "5"
		case "xadd [m64], r64":
			return "5"
		case "xadd [m8], r8":
			return "6"
		case "xadd_wc":
			return "6"
		case "xchg r16,r16":
			return "2"
		case "xchg r32,r32":
			return "2"
		case "xchg r64,r64":
			return "1"
		case "xchg r8,r8":
			return "2"
		case "xchg_wc":
			return "2"
		case "xlat":
			return "7"
		case "xlat_wc":
			return "7"
		case "xor r16, i":
			return "1"
		case "xor r16,r16":
			return "1"
		case "xor r32, i":
			return "1"
		case "xor r32,r32":
			return "1"
		case "xor r64, i":
			return "1"
		case "xor r64,r64":
			return "1"
		case "xor r8, i":
			return "1"
		case "xor r8,r8":
			return "1"
		case "xor_wc":
			return "1"
		case "xsave + xrstor":
			return "114"
		case "xsave_wc":
			return "114"
