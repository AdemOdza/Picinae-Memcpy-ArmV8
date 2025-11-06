replace_dict = {'rcx': 'r64', 'rax': 'r64', 'rbx': 'r64', 'rdx': 'r64', 'rsi': 'r64', 'rdi': 'r64', 'rsp': 'r64', 'rbp': 'r64', 'r8': 'r64', 'r9': 'r64', 'r10': 'r64', 'r11': 'r64', 'r12': 'r64', 'r13': 'r64', 'r14': 'r64', 'r15': 'r64', 'ecx': 'r32', 'eax': 'r32', 'ebx': 'r32', 'edx': 'r32', 'esi': 'r32', 'edi': 'r32', 'esp': 'r32', 'ebp': 'r32', 'r8d': 'r32', 'r9d': 'r32', 'r10d': 'r32', 'r11d': 'r32', 'r12d': 'r32', 'r13d': 'r32', 'r14d': 'r32', 'r15d': 'r32', 'ax': 'r16', 'bx': 'r16', 'cx': 'r16', 'dx': 'r16', 'si': 'r16', 'di': 'r16', 'sp': 'r16', 'bp': 'r16', 'r8w': 'r16', 'r9w': 'r16', 'r10w': 'r16', 'r11w': 'r16', 'r12w': 'r16', 'r13w': 'r16', 'r14w': 'r16', 'r15w': 'r16', 'ah': 'r8', 'al': 'r8', 'bh': 'r8', 'bl': 'r8', 'ch': 'r8', 'cl': 'r8', 'dh': 'r8', 'dl': 'r8', 'sil': 'r8', 'dil': 'r8', 'spl': 'r8', 'bpl': 'r8', 'r8b': 'r8', 'r9b': 'r8', 'r10b': 'r8', 'r11b': 'r8', 'r12b': 'r8', 'r13b': 'r8', 'r14b': 'r8', 'r15b': 'r8'}

def time_of_instr(mnemonic: str, args) -> str :
	for arg in args:
		arg = str(arg)
		if arg.isnumeric():
			arg = "i"
		else:
			arg = replace_dict[arg.lower()]

	match mnemonic, args:
		case "adc", ['r16', 'i']:
			return "adc_r16_i"
		case "adc", ['r16', 'r16']:
			return "adc_r16_r16"
		case "adc", ['r32', 'i']:
			return "adc_r32_i"
		case "adc", ['r32', 'r32']:
			return "adc_r32_r32"
		case "adc", ['r64', 'i']:
			return "adc_r64_i"
		case "adc", ['r64', 'r64']:
			return "adc_r64_r64"
		case "adc", ['r8', 'i']:
			return "adc_r8_i"
		case "adc", ['r8', 'r8']:
			return "adc_r8_r8"
		case "adc_wc", []:
			return "adc_wc"
		case "adcx", ['r32', 'r32']:
			return "adcx_r32_r32"
		case "adcx", ['r64', 'r64']:
			return "adcx_r64_r64"
		case "adcx_wc", []:
			return "adcx_wc"
		case "add", ['[m]']:
			return "add_[m]"
		case "add", ['r16', 'i']:
			return "add_r16_i"
		case "add", ['r16', 'r16']:
			return "add_r16_r16"
		case "add", ['r32', 'i']:
			return "add_r32_i"
		case "add", ['r32', 'r32']:
			return "add_r32_r32"
		case "add", ['r64', 'i']:
			return "add_r64_i"
		case "add", ['r64', 'r64']:
			return "add_r64_r64"
		case "add", ['r8', 'i']:
			return "add_r8_i"
		case "add", ['r8', 'r8']:
			return "add_r8_r8"
		case "add_wc", []:
			return "add_wc"
		case "addps", ['r128', 'r128']:
			return "addps_r128_r128"
		case "addps_wc", []:
			return "addps_wc"
		case "addss", ['r128', 'r128']:
			return "addss_r128_r128"
		case "addss_wc", []:
			return "addss_wc"
		case "addsubps", ['r128', 'r128']:
			return "addsubps_r128_r128"
		case "addsubps_wc", []:
			return "addsubps_wc"
		case "adox", ['r32', 'r32']:
			return "adox_r32_r32"
		case "adox", ['r64', 'r64']:
			return "adox_r64_r64"
		case "adox_wc", []:
			return "adox_wc"
		case "aesdec", ['xmm', 'xmm']:
			return "aesdec_xmm_xmm"
		case "aesdec_wc", []:
			return "aesdec_wc"
		case "aesdeclast", ['xmm', 'xmm']:
			return "aesdeclast_xmm_xmm"
		case "aesdeclast_wc", []:
			return "aesdeclast_wc"
		case "aesenc", ['xmm', 'xmm']:
			return "aesenc_xmm_xmm"
		case "aesenc_wc", []:
			return "aesenc_wc"
		case "aesenclast", ['xmm', 'xmm']:
			return "aesenclast_xmm_xmm"
		case "aesenclast_wc", []:
			return "aesenclast_wc"
		case "aesimc", ['xmm', 'xmm']:
			return "aesimc_xmm_xmm"
		case "aesimc_wc", []:
			return "aesimc_wc"
		case "aeskeygenassist", ['xmm', 'xmm', '0']:
			return "aeskeygenassist_xmm_xmm_0"
		case "aeskeygenassist_wc", []:
			return "aeskeygenassist_wc"
		case "and", ['r16', 'i']:
			return "and_r16_i"
		case "and", ['r16', 'r16']:
			return "and_r16_r16"
		case "and", ['r32', 'i']:
			return "and_r32_i"
		case "and", ['r32', 'r32']:
			return "and_r32_r32"
		case "and", ['r64', 'i']:
			return "and_r64_i"
		case "and", ['r64', 'r64']:
			return "and_r64_r64"
		case "and", ['r8', 'i']:
			return "and_r8_i"
		case "and", ['r8', 'r8']:
			return "and_r8_r8"
		case "and_wc", []:
			return "and_wc"
		case "andn", ['r32', 'r32', 'r32']:
			return "andn_r32_r32_r32"
		case "andn", ['r64', 'r64', 'r64']:
			return "andn_r64_r64_r64"
		case "andn_wc", []:
			return "andn_wc"
		case "andps", ['r128', 'r128']:
			return "andps_r128_r128"
		case "andps_wc", []:
			return "andps_wc"
		case "bextr", ['r32', 'r32', 'r32']:
			return "bextr_r32_r32_r32"
		case "bextr", ['r64', 'r64', 'r64']:
			return "bextr_r64_r64_r64"
		case "bextr_wc", []:
			return "bextr_wc"
		case "blendpd", ['r128', 'r128', 'i']:
			return "blendpd_r128_r128_i"
		case "blendpd_wc", []:
			return "blendpd_wc"
		case "blendps", ['r128', 'r128', 'i']:
			return "blendps_r128_r128_i"
		case "blendps_wc", []:
			return "blendps_wc"
		case "blendvps", ['r128', 'r128', 'xmm0']:
			return "blendvps_r128_r128_xmm0"
		case "blendvps_wc", []:
			return "blendvps_wc"
		case "blsi", ['r32', 'r32']:
			return "blsi_r32_r32"
		case "blsi", ['r64', 'r64']:
			return "blsi_r64_r64"
		case "blsi_wc", []:
			return "blsi_wc"
		case "blsmsk", ['r32', 'r32']:
			return "blsmsk_r32_r32"
		case "blsmsk", ['r64', 'r64']:
			return "blsmsk_r64_r64"
		case "blsmsk_wc", []:
			return "blsmsk_wc"
		case "blsr", ['r32', 'r32']:
			return "blsr_r32_r32"
		case "blsr", ['r64', 'r64']:
			return "blsr_r64_r64"
		case "blsr_wc", []:
			return "blsr_wc"
		case "bsf", ['r16', 'r16']:
			return "bsf_r16_r16"
		case "bsf", ['r32', 'r32']:
			return "bsf_r32_r32"
		case "bsf", ['r64', 'r64']:
			return "bsf_r64_r64"
		case "bsf_wc", []:
			return "bsf_wc"
		case "bsr", ['r16', 'r16']:
			return "bsr_r16_r16"
		case "bsr", ['r32', 'r32']:
			return "bsr_r32_r32"
		case "bsr", ['r64', 'r64']:
			return "bsr_r64_r64"
		case "bsr_wc", []:
			return "bsr_wc"
		case "bswap", ['r32']:
			return "bswap_r32"
		case "bswap", ['r64']:
			return "bswap_r64"
		case "bswap_wc", []:
			return "bswap_wc"
		case "bt", ['r16', '5']:
			return "bt_r16_5"
		case "bt", ['r32', '5']:
			return "bt_r32_5"
		case "bt", ['r32', 'ecx']:
			return "bt_r32_ecx"
		case "bt", ['r64', '5']:
			return "bt_r64_5"
		case "bt_wc", []:
			return "bt_wc"
		case "btc", ['r16', '5']:
			return "btc_r16_5"
		case "btc", ['r32', '5']:
			return "btc_r32_5"
		case "btc", ['r32', 'ecx']:
			return "btc_r32_ecx"
		case "btc", ['r64', '5']:
			return "btc_r64_5"
		case "btc_wc", []:
			return "btc_wc"
		case "btr", ['r16', '5']:
			return "btr_r16_5"
		case "btr", ['r32', '5']:
			return "btr_r32_5"
		case "btr", ['r32', 'ecx']:
			return "btr_r32_ecx"
		case "btr", ['r64', '5']:
			return "btr_r64_5"
		case "btr_wc", []:
			return "btr_wc"
		case "bts", ['r16', '5']:
			return "bts_r16_5"
		case "bts", ['r32', '5']:
			return "bts_r32_5"
		case "bts", ['r32', 'ecx']:
			return "bts_r32_ecx"
		case "bts", ['r64', '5']:
			return "bts_r64_5"
		case "bts_wc", []:
			return "bts_wc"
		case "bzhi", ['r32', 'r32', 'r32']:
			return "bzhi_r32_r32_r32"
		case "bzhi", ['r64', 'r64', 'r64']:
			return "bzhi_r64_r64_r64"
		case "bzhi_wc", []:
			return "bzhi_wc"
		case "cbw", []:
			return "bzhi_wc"
		case "cbw_wc", []:
			return "cbw_wc"
		case "cdq", []:
			return "cbw_wc"
		case "cdq_wc", []:
			return "cdq_wc"
		case "cdqe", []:
			return "cdq_wc"
		case "cdqe_wc", []:
			return "cdqe_wc"
		case "clc", []:
			return "cdqe_wc"
		case "clc_wc", []:
			return "clc_wc"
		case "cld", []:
			return "clc_wc"
		case "cld_wc", []:
			return "cld_wc"
		case "cmc", []:
			return "cld_wc"
		case "cmc_wc", []:
			return "cmc_wc"
		case "cmp", ['r16', 'i']:
			return "cmp_r16_i"
		case "cmp", ['r16', 'r16']:
			return "cmp_r16_r16"
		case "cmp", ['r32', 'i']:
			return "cmp_r32_i"
		case "cmp", ['r32', 'r32']:
			return "cmp_r32_r32"
		case "cmp", ['r64', 'i']:
			return "cmp_r64_i"
		case "cmp", ['r64', 'r64']:
			return "cmp_r64_r64"
		case "cmp", ['r8', 'i']:
			return "cmp_r8_i"
		case "cmp", ['r8', 'r8']:
			return "cmp_r8_r8"
		case "cmp_wc", []:
			return "cmp_wc"
		case "cmpxchg", ['[m16]', 'r16']:
			return "cmpxchg_[m16]_r16"
		case "cmpxchg", ['[m32]', 'r32']:
			return "cmpxchg_[m32]_r32"
		case "cmpxchg", ['[m64]', 'r64']:
			return "cmpxchg_[m64]_r64"
		case "cmpxchg", ['[m8]', 'r8']:
			return "cmpxchg_[m8]_r8"
		case "cmpxchg16b", ['[m]']:
			return "cmpxchg16b_[m]"
		case "cmpxchg16b_wc", []:
			return "cmpxchg16b_wc"
		case "cmpxchg8b", ['[m]']:
			return "cmpxchg8b_[m]"
		case "cmpxchg8b_wc", []:
			return "cmpxchg8b_wc"
		case "cmpxchg_wc", []:
			return "cmpxchg_wc"
		case "comiss", ['r128', 'r128']:
			return "comiss_r128_r128"
		case "comiss_wc", []:
			return "comiss_wc"
		case "cqo", []:
			return "comiss_wc"
		case "cqo_wc", []:
			return "cqo_wc"
		case "crc32", ['r32', 'r16']:
			return "crc32_r32_r16"
		case "crc32", ['r32', 'r32']:
			return "crc32_r32_r32"
		case "crc32", ['r32', 'r8']:
			return "crc32_r32_r8"
		case "crc32_wc", []:
			return "crc32_wc"
		case "cvtdq2pd", ['r128', 'r128']:
			return "cvtdq2pd_r128_r128"
		case "cvtdq2pd", ['xmm', 'xmm']:
			return "cvtdq2pd_xmm_xmm"
		case "cvtdq2pd", ['xmm', 'xmm']:
			return "cvtdq2pd_xmm_xmm"
		case "cvtdq2pd_wc", []:
			return "cvtdq2pd_wc"
		case "cvtdq2ps", ['r128', 'r128']:
			return "cvtdq2ps_r128_r128"
		case "cvtdq2ps", ['xmm', 'xmm']:
			return "cvtdq2ps_xmm_xmm"
		case "cvtdq2ps_wc", []:
			return "cvtdq2ps_wc"
		case "cvtpd2dq", ['r128', 'r128']:
			return "cvtpd2dq_r128_r128"
		case "cvtpd2dq", ['xmm', 'xmm']:
			return "cvtpd2dq_xmm_xmm"
		case "cvtpd2dq_wc", []:
			return "cvtpd2dq_wc"
		case "cvtpd2pi", ['mmx', 'xmm']:
			return "cvtpd2pi_mmx_xmm"
		case "cvtpd2pi_wc", []:
			return "cvtpd2pi_wc"
		case "cvtpd2ps", ['r128', 'r128']:
			return "cvtpd2ps_r128_r128"
		case "cvtpd2ps", ['xmm', 'xmm']:
			return "cvtpd2ps_xmm_xmm"
		case "cvtpd2ps_wc", []:
			return "cvtpd2ps_wc"
		case "cvtpi2ps", ['xmm', 'mmx']:
			return "cvtpi2ps_xmm_mmx"
		case "cvtpi2ps_wc", []:
			return "cvtpi2ps_wc"
		case "cvtps2dq", ['xmm', 'xmm']:
			return "cvtps2dq_xmm_xmm"
		case "cvtps2dq_wc", []:
			return "cvtps2dq_wc"
		case "cvtps2pd", ['r128', 'r128']:
			return "cvtps2pd_r128_r128"
		case "cvtps2pd", ['xmm', 'xmm']:
			return "cvtps2pd_xmm_xmm"
		case "cvtps2pd_wc", []:
			return "cvtps2pd_wc"
		case "cvtsd2ss", ['xmm', 'xmm']:
			return "cvtsd2ss_xmm_xmm"
		case "cvtsd2ss_wc", []:
			return "cvtsd2ss_wc"
		case "cvtsi2sd", ['xmm', 'r32']:
			return "cvtsi2sd_xmm_r32"
		case "cvtsi2sd", ['xmm', 'r64']:
			return "cvtsi2sd_xmm_r64"
		case "cvtsi2sd_wc", []:
			return "cvtsi2sd_wc"
		case "cvtss2sd", ['xmm', 'xmm']:
			return "cvtss2sd_xmm_xmm"
		case "cvtss2sd_wc", []:
			return "cvtss2sd_wc"
		case "cvtss2si", ['r32', 'xmm']:
			return "cvtss2si_r32_xmm"
		case "cvtss2si", ['r64', 'xmm']:
			return "cvtss2si_r64_xmm"
		case "cvtss2si_wc", []:
			return "cvtss2si_wc"
		case "cvttps2dq", ['r128', 'r128']:
			return "cvttps2dq_r128_r128"
		case "cvttps2dq_wc", []:
			return "cvttps2dq_wc"
		case "cwd", []:
			return "cvttps2dq_wc"
		case "cwd_wc", []:
			return "cwd_wc"
		case "cwde", []:
			return "cwd_wc"
		case "cwde_wc", []:
			return "cwde_wc"
		case "dec", ['r16']:
			return "dec_r16"
		case "dec", ['r32']:
			return "dec_r32"
		case "dec", ['r64']:
			return "dec_r64"
		case "dec", ['r8']:
			return "dec_r8"
		case "dec", ['r8high']:
			return "dec_r8h"
		case "dec_wc", []:
			return "dec_wc"
		case "div", ['', 'registersize 16']:
			return "div_r16"
		case "div", ['', 'registersize 16', '1']:
			return "div_r16_1"
		case "div", ['', 'registersize 32']:
			return "div_r32"
		case "div", ['', 'registersize 32', '1']:
			return "div_r32_1"
		case "div", ['', 'registersize 64']:
			return "div_r64"
		case "div", ['', 'registersize 64', '1']:
			return "div_r64_1"
		case "div", ['', 'registersize 8']:
			return "div_r8"
		case "div", ['', 'registersize 8', '1']:
			return "div_r8_1"
		case "div_wc", []:
			return "div_wc"
		case "divpd", ['r128', 'r128 (best case)']:
			return "div_wc"
		case "divpd", ['r128', 'r128 (worst case)']:
			return "divpd_r128_r128"
		case "divpd_wc", []:
			return "divpd_wc"
		case "divps", ['r128', 'r128 (best case)']:
			return "divpd_wc"
		case "divps", ['r128', 'r128 (worst case)']:
			return "divps_r128_r128"
		case "divps_wc", []:
			return "divps_wc"
		case "divsd", ['r128', 'r128 (best case)']:
			return "divps_wc"
		case "divsd", ['r128', 'r128 (worst case)']:
			return "divsd_r128_r128"
		case "divsd_wc", []:
			return "divsd_wc"
		case "divss", ['r128', 'r128 (best case)']:
			return "divsd_wc"
		case "divss", ['r128', 'r128 (worst case)']:
			return "divss_r128_r128"
		case "divss_wc", []:
			return "divss_wc"
		case "dppd", ['r128', 'r128', 'i']:
			return "dppd_r128_r128_i"
		case "dppd_wc", []:
			return "dppd_wc"
		case "dpps", ['r128', 'r128', 'i']:
			return "dpps_r128_r128_i"
		case "dpps_wc", []:
			return "dpps_wc"
		case "f2xm1", []:
			return "dpps_wc"
		case "f2xm1", ['+ fcmov']:
			return "dpps_wc"
		case "f2xm1_wc", []:
			return "f2xm1_wc"
		case "fabs", []:
			return "f2xm1_wc"
		case "fabs_wc", []:
			return "fabs_wc"
		case "fadd", []:
			return "fabs_wc"
		case "fadd_wc", []:
			return "fadd_wc"
		case "fbld", ['[m80] + fstp [m80]']:
			return "fadd_wc"
		case "fbld_wc", []:
			return "fbld_wc"
		case "fbstp", ['+ fbld [m80]']:
			return "fbld_wc"
		case "fbstp", ['+ fld [m64]']:
			return "fbld_wc"
		case "fbstp", ['+ fld [m80]']:
			return "fbld_wc"
		case "fbstp_wc", []:
			return "fbstp_wc"
		case "fchs", []:
			return "fbstp_wc"
		case "fchs_wc", []:
			return "fchs_wc"
		case "fcomi", ['+ fcmov']:
			return "fchs_wc"
		case "fcomi_wc", []:
			return "fcomi_wc"
		case "fcos", []:
			return "fcomi_wc"
		case "fcos", ['+ fcmov']:
			return "fcomi_wc"
		case "fcos_wc", []:
			return "fcos_wc"
		case "fdiv", []:
			return "fcos_wc"
		case "fdiv_wc", []:
			return "fdiv_wc"
		case "fild", ['[m16]']:
			return "fild_[m16]"
		case "fild", ['[m32]']:
			return "fild_[m32]"
		case "fild", ['[m32] + fistp [m32]']:
			return "fild_[m32]"
		case "fild", ['[m32] + fstp [m32]']:
			return "fild_[m32]"
		case "fild", ['[m64]']:
			return "fild_[m64]"
		case "fild_wc", []:
			return "fild_wc"
		case "fistp", ['[m32] + fld [m32]']:
			return "fild_wc"
		case "fistp_wc", []:
			return "fistp_wc"
		case "fld", ['st0 + fstp']:
			return "fistp_wc"
		case "fld_wc", []:
			return "fld_wc"
		case "fldcw", ['+ fnstcw']:
			return "fld_wc"
		case "fldcw_wc", []:
			return "fldcw_wc"
		case "fmul", []:
			return "fldcw_wc"
		case "fmul_wc", []:
			return "fmul_wc"
		case "fnsave", ['+ frstor']:
			return "fmul_wc"
		case "fnsave_wc", []:
			return "fnsave_wc"
		case "fnstsw", ['+ test + fcmov']:
			return "fnsave_wc"
		case "fnstsw", ['[m16] + test + fcmov + fcom']:
			return "fnsave_wc"
		case "fnstsw", ['ax + test + fcmov']:
			return "fnsave_wc"
		case "fnstsw", ['ax + test + fcmov + 2*fld']:
			return "fnsave_wc"
		case "fnstsw", ['ax + test + fcmov + fcom']:
			return "fnsave_wc"
		case "fnstsw_wc", []:
			return "fnstsw_wc"
		case "fpatan", ['+ fld + fxch']:
			return "fnstsw_wc"
		case "fpatan_wc", []:
			return "fpatan_wc"
		case "fprem", ['+ fadd']:
			return "fpatan_wc"
		case "fprem1", ['+ fadd']:
			return "fpatan_wc"
		case "fprem1_wc", []:
			return "fprem1_wc"
		case "fprem_wc", []:
			return "fprem_wc"
		case "fptan", ['+ fadd']:
			return "fprem_wc"
		case "fptan", ['+ fstp']:
			return "fprem_wc"
		case "fptan_wc", []:
			return "fptan_wc"
		case "fsin", ['+ fadd']:
			return "fptan_wc"
		case "fsin_wc", []:
			return "fsin_wc"
		case "fsincos", ['+ fadd']:
			return "fsin_wc"
		case "fsincos_wc", []:
			return "fsincos_wc"
		case "fsqrt", ['+ fadd']:
			return "fsincos_wc"
		case "fsqrt_wc", []:
			return "fsqrt_wc"
		case "fst", ['st']:
			return "fst_st"
		case "fst_wc", []:
			return "fst_wc"
		case "fstp", ['[m32]']:
			return "fstp_[m32]"
		case "fstp", ['[m32] + fld [m32]']:
			return "fstp_[m32]"
		case "fstp", ['[m32] + fld [m32] + fchs']:
			return "fstp_[m32]"
		case "fstp", ['[m64]']:
			return "fstp_[m64]"
		case "fstp", ['[m64] + fld [m64]']:
			return "fstp_[m64]"
		case "fstp", ['[m80]']:
			return "fstp_[m80]"
		case "fstp", ['[m80] + fld [m80]']:
			return "fstp_[m80]"
		case "fstp", ['fstp + fld']:
			return "fstp_[m80]"
		case "fstp_wc", []:
			return "fstp_wc"
		case "ftst", ['+ fnstsw + test + fcmov']:
			return "fstp_wc"
		case "ftst_wc", []:
			return "ftst_wc"
		case "fxch", []:
			return "ftst_wc"
		case "fxch_wc", []:
			return "fxch_wc"
		case "fxsave", ['+ fxrstor']:
			return "fxch_wc"
		case "fxsave_wc", []:
			return "fxsave_wc"
		case "fxtract", ['+ fadd']:
			return "fxsave_wc"
		case "fxtract_wc", []:
			return "fxtract_wc"
		case "fyl2x", ['+ fld']:
			return "fxtract_wc"
		case "fyl2x_wc", []:
			return "fyl2x_wc"
		case "fyl2xp1", ['+ fld']:
			return "fyl2x_wc"
		case "fyl2xp1_wc", []:
			return "fyl2xp1_wc"
		case "haddps", ['r128', 'r128']:
			return "haddps_r128_r128"
		case "haddps_wc", []:
			return "haddps_wc"
		case "hsubpd", ['r128', 'r128']:
			return "hsubpd_r128_r128"
		case "hsubpd_wc", []:
			return "hsubpd_wc"
		case "idiv", ['', 'registersize 16']:
			return "idiv_r16"
		case "idiv", ['', 'registersize 16', '1']:
			return "idiv_r16_1"
		case "idiv", ['', 'registersize 32']:
			return "idiv_r32"
		case "idiv", ['', 'registersize 32', '1']:
			return "idiv_r32_1"
		case "idiv", ['', 'registersize 64']:
			return "idiv_r64"
		case "idiv", ['', 'registersize 64', '1']:
			return "idiv_r64_1"
		case "idiv", ['', 'registersize 8']:
			return "idiv_r8"
		case "idiv", ['', 'registersize 8', '1']:
			return "idiv_r8_1"
		case "idiv_wc", []:
			return "idiv_wc"
		case "imul", ['', 'registersize 16']:
			return "imul_r16"
		case "imul", ['', 'registersize 32']:
			return "imul_r32"
		case "imul", ['', 'registersize 64']:
			return "imul_r64"
		case "imul", ['', 'registersize 8']:
			return "imul_r8"
		case "imul", ['', 'regsize 16', 'numop 2']:
			return "imul_r16"
		case "imul", ['', 'regsize 16', 'numop 3']:
			return "imul_r16"
		case "imul", ['', 'regsize 32', 'numop 2']:
			return "imul_r32"
		case "imul", ['', 'regsize 32', 'numop 3']:
			return "imul_r32"
		case "imul", ['', 'regsize 64', 'numop 2']:
			return "imul_r64"
		case "imul", ['', 'regsize 64', 'numop 3']:
			return "imul_r64"
		case "imul", ['r16', 'r16']:
			return "imul_r16_r16"
		case "imul", ['r32', 'r32']:
			return "imul_r32_r32"
		case "imul", ['r64', 'r64']:
			return "imul_r64_r64"
		case "imul_wc", []:
			return "imul_wc"
		case "inc", ['r16']:
			return "inc_r16"
		case "inc", ['r32']:
			return "inc_r32"
		case "inc", ['r64']:
			return "inc_r64"
		case "inc", ['r8']:
			return "inc_r8"
		case "inc", ['r8high']:
			return "inc_r8h"
		case "inc_wc", []:
			return "inc_wc"
		case "insertps", []:
			return "inc_wc"
		case "insertps", ['xmm', 'xmm', 'i']:
			return "insertps_xmm_xmm_i"
		case "insertps_wc", []:
			return "insertps_wc"
		case "jg_addr", []:
			return "jg_addr"
		case "jge_addr", []:
			return "jge_addr"
		case "jle_addr", []:
			return "jle_addr"
		case "jmp_addr", []:
			return "jmp_addr"
		case "jnc_addr", []:
			return "jnc_addr"
		case "jnz_addr", []:
			return "jnz_addr"
		case "jz_addr", []:
			return "jz_addr"
		case "lddqu", ['xmm', 'm128']:
			return "lddqu_xmm_m128"
		case "lddqu_wc", []:
			return "lddqu_wc"
		case "ldmxcsr", ['+ stmccsr']:
			return "lddqu_wc"
		case "ldmxcsr_wc", []:
			return "ldmxcsr_wc"
		case "lea", ['r16', '[r64+0*rsi+(0 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r16', '[r64+0*rsi+(0 bytes)] + mov', '']:
			return "ldmxcsr_wc"
		case "lea", ['r16', '[r64+0*rsi+(1 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r16', '[r64+0*rsi+(1 bytes)] + mov', '']:
			return "ldmxcsr_wc"
		case "lea", ['r16', '[r64+0*rsi+(4 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r16', '[r64+1*rsi+(0 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r16', '[r64+1*rsi+(1 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r16', '[r64+1*rsi+(4 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r16', '[r64+4*rsi+(0 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r16', '[r64+4*rsi+(0 bytes)] + mov', '']:
			return "ldmxcsr_wc"
		case "lea", ['r16', '[r64+4*rsi+(1 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r16', '[r64+4*rsi+(1 bytes)] + mov', '']:
			return "ldmxcsr_wc"
		case "lea", ['r16', '[r64+4*rsi+(4 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[4*esi+(0 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[4*esi+(1 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[4*esi+(4 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+0*rsi+(0 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+0*rsi+(0 bytes)] + add', '']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+0*rsi+(0 bytes)] + mov', '']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+0*rsi+(1 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+0*rsi+(1 bytes)] + mov', '']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+0*rsi+(4 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+0*rsi+(4 bytes)] + add', '']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+1*rsi+(0 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+1*rsi+(1 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+1*rsi+(4 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+4*rsi+(0 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+4*rsi+(0 bytes)] + add', '']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+4*rsi+(0 bytes)] + mov', '']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+4*rsi+(1 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+4*rsi+(1 bytes)] + mov', '']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+4*rsi+(4 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r32', '[r64+4*rsi+(4 bytes)] + add', '']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+0*rsi+(0 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+0*rsi+(0 bytes)] + add', '']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+0*rsi+(0 bytes)] + mov', '']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+0*rsi+(1 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+0*rsi+(1 bytes)] + mov', '']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+0*rsi+(4 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+0*rsi+(4 bytes)] + add', '']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+1*rsi+(0 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+1*rsi+(1 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+1*rsi+(4 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+4*rsi+(0 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+4*rsi+(0 bytes)] + add', '']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+4*rsi+(0 bytes)] + mov', '']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+4*rsi+(1 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+4*rsi+(1 bytes)] + mov', '']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+4*rsi+(4 bytes)]']:
			return "ldmxcsr_wc"
		case "lea", ['r64', '[r64+4*rsi+(4 bytes)] + add', '']:
			return "ldmxcsr_wc"
		case "lea_r32_addr", []:
			return "ldmxcsr_wc"
		case "lea_wc", []:
			return "lea_wc"
		case "lfence", []:
			return "lea_wc"
		case "lfence_wc", []:
			return "lfence_wc"
		case "lock", ['cmpxchg [m16]', 'r16']:
			return "lock_cmpxchg_[m16]_r16"
		case "lock", ['cmpxchg [m32]', 'r32']:
			return "lock_cmpxchg_[m32]_r32"
		case "lock", ['cmpxchg [m64]', 'r64']:
			return "lock_cmpxchg_[m64]_r64"
		case "lock", ['cmpxchg [m8]', 'r8']:
			return "lock_cmpxchg_[m8]_r8"
		case "lock", ['cmpxchg16b [m]']:
			return "lock_cmpxchg16b_[m]"
		case "lock_wc", []:
			return "lock_wc"
		case "lzcnt", ['r16', 'r16']:
			return "lzcnt_r16_r16"
		case "lzcnt", ['r32', 'r32']:
			return "lzcnt_r32_r32"
		case "lzcnt", ['r64', 'r64']:
			return "lzcnt_r64_r64"
		case "lzcnt_wc", []:
			return "lzcnt_wc"
		case "maskmovdqu", ['r', 'r (pattern 0x00) + movq']:
			return "lzcnt_wc"
		case "maskmovdqu", ['r', 'r (pattern 0x02) + movq']:
			return "lzcnt_wc"
		case "maskmovdqu", ['r', 'r (pattern 0x33) + movq']:
			return "lzcnt_wc"
		case "maskmovdqu", ['r', 'r (pattern 0x55) + movq']:
			return "lzcnt_wc"
		case "maskmovdqu", ['r', 'r (pattern 0xff) + movq']:
			return "lzcnt_wc"
		case "maskmovdqu_wc", []:
			return "maskmovdqu_wc"
		case "maskmovq", ['r', 'r (pattern 0x00) + movq']:
			return "maskmovdqu_wc"
		case "maskmovq", ['r', 'r (pattern 0x02) + movq']:
			return "maskmovdqu_wc"
		case "maskmovq", ['r', 'r (pattern 0x33) + movq']:
			return "maskmovdqu_wc"
		case "maskmovq", ['r', 'r (pattern 0x55) + movq']:
			return "maskmovdqu_wc"
		case "maskmovq", ['r', 'r (pattern 0xff) + movq']:
			return "maskmovdqu_wc"
		case "maskmovq_wc", []:
			return "maskmovq_wc"
		case "maxpd", ['r128', 'r128']:
			return "maxpd_r128_r128"
		case "maxpd", ['xmm', 'xmm']:
			return "maxpd_xmm_xmm"
		case "maxpd_wc", []:
			return "maxpd_wc"
		case "maxps", ['xmm', 'xmm']:
			return "maxps_xmm_xmm"
		case "maxps_wc", []:
			return "maxps_wc"
		case "maxss", ['r128', 'r128']:
			return "maxss_r128_r128"
		case "maxss_wc", []:
			return "maxss_wc"
		case "mfence", []:
			return "maxss_wc"
		case "mfence_wc", []:
			return "mfence_wc"
		case "minps", ['r128', 'r128']:
			return "minps_r128_r128"
		case "minps_wc", []:
			return "minps_wc"
		case "minsd", ['r128', 'r128']:
			return "minsd_r128_r128"
		case "minsd_wc", []:
			return "minsd_wc"
		case "mov", []:
			return "minsd_wc"
		case "mov", ['m16', 'r16']:
			return "mov_m16_r16"
		case "mov", ['m32', 'r32']:
			return "mov_m32_r32"
		case "mov", ['m64', 'r64']:
			return "mov_m64_r64"
		case "mov", ['m8', 'r8']:
			return "mov_m8_r8"
		case "mov", ['m8', 'r8h']:
			return "mov_m8_r8h"
		case "mov", ['r16', 'i']:
			return "mov_r16_i"
		case "mov", ['r16', 'r16']:
			return "mov_r16_r16"
		case "mov", ['r32', 'i']:
			return "mov_r32_i"
		case "mov", ['r32', 'r32']:
			return "mov_r32_r32"
		case "mov", ['r64', 'i']:
			return "mov_r64_i"
		case "mov", ['r64', 'r64']:
			return "mov_r64_r64"
		case "mov", ['r8', 'i']:
			return "mov_r8_i"
		case "mov", ['r8', 'r8']:
			return "mov_r8_r8"
		case "mov", ['r8h', 'm8']:
			return "mov_r8h_m8"
		case "mov", ['r8h', 'r8']:
			return "mov_r8h_r8"
		case "mov", ['r8h', 'r8h']:
			return "mov_r8h_r8h"
		case "mov", ['r8h', 'r8h']:
			return "mov_r8h_r8h"
		case "mov_wc", []:
			return "mov_wc"
		case "movapd", ['m128', 'xmm']:
			return "movapd_m128_xmm"
		case "movapd", ['r128', 'r128']:
			return "movapd_r128_r128"
		case "movapd_wc", []:
			return "movapd_wc"
		case "movaps", ['m128', 'xmm']:
			return "movaps_m128_xmm"
		case "movaps", ['r128', 'r128']:
			return "movaps_r128_r128"
		case "movaps", ['xmm', 'm128']:
			return "movaps_xmm_m128"
		case "movaps", ['xmm', 'xmm']:
			return "movaps_xmm_xmm"
		case "movaps_wc", []:
			return "movaps_wc"
		case "movd", []:
			return "movaps_wc"
		case "movd", ['mmx', 'r32']:
			return "movd_mmx_r32"
		case "movd", ['r128', 'r21']:
			return "movd_r128_r21"
		case "movd", ['r32', 'xmm']:
			return "movd_r32_xmm"
		case "movd", ['xmm', 'm32']:
			return "movd_xmm_m32"
		case "movd", ['xmm', 'r32']:
			return "movd_xmm_r32"
		case "movd_wc", []:
			return "movd_wc"
		case "movddup", ['r128', 'r128']:
			return "movddup_r128_r128"
		case "movddup_wc", []:
			return "movddup_wc"
		case "movdqa", ['m128', 'xmm']:
			return "movdqa_m128_xmm"
		case "movdqa", ['r128', 'r128']:
			return "movdqa_r128_r128"
		case "movdqa", ['xmm', 'm128']:
			return "movdqa_xmm_m128"
		case "movdqa_wc", []:
			return "movdqa_wc"
		case "movdqu", ['[m]', 'xmm']:
			return "movdqu_[m]_xmm"
		case "movdqu", ['m128', 'xmm']:
			return "movdqu_m128_xmm"
		case "movdqu", ['r128', 'r128']:
			return "movdqu_r128_r128"
		case "movdqu_wc", []:
			return "movdqu_wc"
		case "movhps", ['m64', 'xmm']:
			return "movhps_m64_xmm"
		case "movhps_wc", []:
			return "movhps_wc"
		case "movlhps", ['xmm', 'xmm']:
			return "movlhps_xmm_xmm"
		case "movlhps", ['xmm', 'xmm']:
			return "movlhps_xmm_xmm"
		case "movlhps_wc", []:
			return "movlhps_wc"
		case "movlpd", ['m', 'xmm']:
			return "movlpd_m_xmm"
		case "movlpd_wc", []:
			return "movlpd_wc"
		case "movlps", ['m64', 'xmm']:
			return "movlps_m64_xmm"
		case "movlps_wc", []:
			return "movlps_wc"
		case "movmskpd", ['r32', 'xmm']:
			return "movmskpd_r32_xmm"
		case "movmskpd_wc", []:
			return "movmskpd_wc"
		case "movntdqa", ['xmm', 'm']:
			return "movntdqa_xmm_m"
		case "movntdqa_wc", []:
			return "movntdqa_wc"
		case "movnti", ['m32', 'r32']:
			return "movnti_m32_r32"
		case "movnti_wc", []:
			return "movnti_wc"
		case "movntq", ['m64', 'mmx']:
			return "movntq_m64_mmx"
		case "movntq_wc", []:
			return "movntq_wc"
		case "movq", ['m64', 'mmx']:
			return "movq_m64_mmx"
		case "movq", ['m64', 'xmm']:
			return "movq_m64_xmm"
		case "movq", ['mmx', 'r64']:
			return "movq_mmx_r64"
		case "movq", ['r128', 'r128']:
			return "movq_r128_r128"
		case "movq", ['r64', 'xmm']:
			return "movq_r64_xmm"
		case "movq", ['r64', 'r64']:
			return "movq_r64_r64"
		case "movq", ['xmm', 'm64']:
			return "movq_xmm_m64"
		case "movq", ['xmm', 'r64']:
			return "movq_xmm_r64"
		case "movq2dq", ['xmm', 'mmx']:
			return "movq2dq_xmm_mmx"
		case "movq2dq_wc", []:
			return "movq2dq_wc"
		case "movq_wc", []:
			return "movq_wc"
		case "movsd", ['m64', 'xmm']:
			return "movsd_m64_xmm"
		case "movsd", ['xmm', 'xmm']:
			return "movsd_xmm_xmm"
		case "movsd", ['xmm', 'xmm']:
			return "movsd_xmm_xmm"
		case "movsd_wc", []:
			return "movsd_wc"
		case "movshdup", ['r128', 'r128']:
			return "movshdup_r128_r128"
		case "movshdup_wc", []:
			return "movshdup_wc"
		case "movsldup", ['r128', 'r128']:
			return "movsldup_r128_r128"
		case "movsldup_wc", []:
			return "movsldup_wc"
		case "movss", []:
			return "movsldup_wc"
		case "movss", ['m32', 'xmm']:
			return "movss_m32_xmm"
		case "movss", ['xmm', 'xmm']:
			return "movss_xmm_xmm"
		case "movss", ['xmm', 'xmm']:
			return "movss_xmm_xmm"
		case "movss_wc", []:
			return "movss_wc"
		case "movsx", ['r16', '[m8]']:
			return "movsx_r16_[m8]"
		case "movsx", ['r16', 'r8']:
			return "movsx_r16_r8"
		case "movsx", ['r32', '[m16]']:
			return "movsx_r32_[m16]"
		case "movsx", ['r32', '[m8]']:
			return "movsx_r32_[m8]"
		case "movsx", ['r32', 'r16']:
			return "movsx_r32_r16"
		case "movsx", ['r32', 'r8']:
			return "movsx_r32_r8"
		case "movsx", ['r64', '[m16]']:
			return "movsx_r64_[m16]"
		case "movsx", ['r64', '[m8]']:
			return "movsx_r64_[m8]"
		case "movsx", ['r64', 'r16']:
			return "movsx_r64_r16"
		case "movsx", ['r64', 'r8']:
			return "movsx_r64_r8"
		case "movsx_wc", []:
			return "movsx_wc"
		case "movsxd", ['r64', '[m32]']:
			return "movsxd_r64_[m32]"
		case "movsxd", ['r64', 'r32']:
			return "movsxd_r64_r32"
		case "movsxd_wc", []:
			return "movsxd_wc"
		case "movupd", ['[m]', 'xmm']:
			return "movupd_[m]_xmm"
		case "movupd", ['r128', 'r128']:
			return "movupd_r128_r128"
		case "movupd_wc", []:
			return "movupd_wc"
		case "movups", ['[m]', 'xmm']:
			return "movups_[m]_xmm"
		case "movups", ['r128', 'r128']:
			return "movups_r128_r128"
		case "movups_wc", []:
			return "movups_wc"
		case "movzx", ['r16', '[m8]']:
			return "movzx_r16_[m8]"
		case "movzx", ['r16', 'r8']:
			return "movzx_r16_r8"
		case "movzx", ['r32', '[m16]']:
			return "movzx_r32_[m16]"
		case "movzx", ['r32', '[m8]']:
			return "movzx_r32_[m8]"
		case "movzx", ['r32', 'r16']:
			return "movzx_r32_r16"
		case "movzx", ['r32', 'r8']:
			return "movzx_r32_r8"
		case "movzx", ['r64', '[m16]']:
			return "movzx_r64_[m16]"
		case "movzx", ['r64', '[m8]']:
			return "movzx_r64_[m8]"
		case "movzx", ['r64', 'r16']:
			return "movzx_r64_r16"
		case "movzx", ['r64', 'r8']:
			return "movzx_r64_r8"
		case "movzx_wc", []:
			return "movzx_wc"
		case "mpsadbw", ['r128', 'r128']:
			return "mpsadbw_r128_r128"
		case "mpsadbw_wc", []:
			return "mpsadbw_wc"
		case "mul", ['', 'registersize 16']:
			return "mul_r16"
		case "mul", ['', 'registersize 32']:
			return "mul_r32"
		case "mul", ['', 'registersize 64']:
			return "mul_r64"
		case "mul", ['', 'registersize 8']:
			return "mul_r8"
		case "mul_wc", []:
			return "mul_wc"
		case "mulpd", ['r128', 'r128']:
			return "mulpd_r128_r128"
		case "mulpd_wc", []:
			return "mulpd_wc"
		case "mulps", ['r128', 'r128']:
			return "mulps_r128_r128"
		case "mulps_wc", []:
			return "mulps_wc"
		case "mulsd", ['r128', 'r128']:
			return "mulsd_r128_r128"
		case "mulsd_wc", []:
			return "mulsd_wc"
		case "mulss", ['r128', 'r128']:
			return "mulss_r128_r128"
		case "mulss_wc", []:
			return "mulss_wc"
		case "mulx", ['r32', 'r32', 'r32']:
			return "mulx_r32_r32_r32"
		case "mulx", ['r64', 'r64', 'r64']:
			return "mulx_r64_r64_r64"
		case "mulx_wc", []:
			return "mulx_wc"
		case "neg", ['r16']:
			return "neg_r16"
		case "neg", ['r32']:
			return "neg_r32"
		case "neg", ['r64']:
			return "neg_r64"
		case "neg", ['r8']:
			return "neg_r8"
		case "neg", ['r8high']:
			return "neg_r8h"
		case "neg_wc", []:
			return "neg_wc"
		case "nop", []:
			return "neg_wc"
		case "nop_wc", []:
			return "nop_wc"
		case "not", ['r16']:
			return "not_r16"
		case "not", ['r32']:
			return "not_r32"
		case "not", ['r64']:
			return "not_r64"
		case "not", ['r8']:
			return "not_r8"
		case "not", ['r8high']:
			return "not_r8h"
		case "not_wc", []:
			return "not_wc"
		case "or", ['r16', 'i']:
			return "or_r16_i"
		case "or", ['r16', 'r16']:
			return "or_r16_r16"
		case "or", ['r32', 'i']:
			return "or_r32_i"
		case "or", ['r32', 'r32']:
			return "or_r32_r32"
		case "or", ['r64', 'i']:
			return "or_r64_i"
		case "or", ['r64', 'r64']:
			return "or_r64_r64"
		case "or", ['r8', 'i']:
			return "or_r8_i"
		case "or", ['r8', 'r8']:
			return "or_r8_r8"
		case "or_wc", []:
			return "or_wc"
		case "orpd", ['r128', 'r128']:
			return "orpd_r128_r128"
		case "orpd_wc", []:
			return "orpd_wc"
		case "pabsb", ['r128', 'r128']:
			return "pabsb_r128_r128"
		case "pabsb", ['r64', 'r64']:
			return "pabsb_r64_r64"
		case "pabsb_wc", []:
			return "pabsb_wc"
		case "pabsd", ['r128', 'r128']:
			return "pabsd_r128_r128"
		case "pabsd", ['r64', 'r64']:
			return "pabsd_r64_r64"
		case "pabsd_wc", []:
			return "pabsd_wc"
		case "packssdw", ['r128', 'r128']:
			return "packssdw_r128_r128"
		case "packssdw", ['r64', 'r64']:
			return "packssdw_r64_r64"
		case "packssdw_wc", []:
			return "packssdw_wc"
		case "packsswb", ['r128', 'r128']:
			return "packsswb_r128_r128"
		case "packsswb", ['r64', 'r64']:
			return "packsswb_r64_r64"
		case "packsswb_wc", []:
			return "packsswb_wc"
		case "packusdw", ['r128', 'r128']:
			return "packusdw_r128_r128"
		case "packusdw_wc", []:
			return "packusdw_wc"
		case "packuswb", ['r128', 'r128']:
			return "packuswb_r128_r128"
		case "packuswb", ['r64', 'r64']:
			return "packuswb_r64_r64"
		case "packuswb_wc", []:
			return "packuswb_wc"
		case "paddd", ['r128', 'r128']:
			return "paddd_r128_r128"
		case "paddd", ['r64', 'r64']:
			return "paddd_r64_r64"
		case "paddd_wc", []:
			return "paddd_wc"
		case "paddq", ['r128', 'r128']:
			return "paddq_r128_r128"
		case "paddq", ['r64', 'r64']:
			return "paddq_r64_r64"
		case "paddq_wc", []:
			return "paddq_wc"
		case "paddusb", ['r128', 'r128']:
			return "paddusb_r128_r128"
		case "paddusb", ['r64', 'r64']:
			return "paddusb_r64_r64"
		case "paddusb_wc", []:
			return "paddusb_wc"
		case "paddw", ['r128', 'r128']:
			return "paddw_r128_r128"
		case "paddw", ['r64', 'r64']:
			return "paddw_r64_r64"
		case "paddw_wc", []:
			return "paddw_wc"
		case "palignr", ['r128', 'r128']:
			return "palignr_r128_r128"
		case "palignr", ['r64', 'r64', 'i']:
			return "palignr_r64_r64_i"
		case "palignr_wc", []:
			return "palignr_wc"
		case "pand", ['r128', 'r128']:
			return "pand_r128_r128"
		case "pand", ['r64', 'r64']:
			return "pand_r64_r64"
		case "pand_wc", []:
			return "pand_wc"
		case "pandn", ['r128', 'r128']:
			return "pandn_r128_r128"
		case "pandn", ['r64', 'r64']:
			return "pandn_r64_r64"
		case "pandn_wc", []:
			return "pandn_wc"
		case "pause", []:
			return "pandn_wc"
		case "pause_wc", []:
			return "pause_wc"
		case "pavgb", ['r128', 'r128']:
			return "pavgb_r128_r128"
		case "pavgb", ['r64', 'r64']:
			return "pavgb_r64_r64"
		case "pavgb_wc", []:
			return "pavgb_wc"
		case "pavgw", ['r128', 'r128']:
			return "pavgw_r128_r128"
		case "pavgw", ['r64', 'r64']:
			return "pavgw_r64_r64"
		case "pavgw_wc", []:
			return "pavgw_wc"
		case "pblendvb", ['r128', 'r128', 'xmm0']:
			return "pblendvb_r128_r128_xmm0"
		case "pblendvb_wc", []:
			return "pblendvb_wc"
		case "pblendw", ['r128', 'r128']:
			return "pblendw_r128_r128"
		case "pblendw_wc", []:
			return "pblendw_wc"
		case "pclmulqdq", ['r128', 'r128']:
			return "pclmulqdq_r128_r128"
		case "pclmulqdq", ['xmm', 'xmm', '0']:
			return "pclmulqdq_xmm_xmm_0"
		case "pclmulqdq", ['xmm', 'xmm', '1']:
			return "pclmulqdq_xmm_xmm_1"
		case "pclmulqdq", ['xmm', 'xmm', '2']:
			return "pclmulqdq_xmm_xmm_2"
		case "pclmulqdq", ['xmm', 'xmm', '3']:
			return "pclmulqdq_xmm_xmm_3"
		case "pclmulqdq_wc", []:
			return "pclmulqdq_wc"
		case "pcmpeqb", ['r128', 'r128']:
			return "pcmpeqb_r128_r128"
		case "pcmpeqb", ['r64', 'r64']:
			return "pcmpeqb_r64_r64"
		case "pcmpeqb_wc", []:
			return "pcmpeqb_wc"
		case "pcmpeqd", ['r128', 'r128']:
			return "pcmpeqd_r128_r128"
		case "pcmpeqd", ['r64', 'r64']:
			return "pcmpeqd_r64_r64"
		case "pcmpeqd_wc", []:
			return "pcmpeqd_wc"
		case "pcmpeqq", ['r128', 'r128']:
			return "pcmpeqq_r128_r128"
		case "pcmpeqq_wc", []:
			return "pcmpeqq_wc"
		case "pcmpeqw", ['r128', 'r128']:
			return "pcmpeqw_r128_r128"
		case "pcmpeqw", ['r64', 'r64']:
			return "pcmpeqw_r64_r64"
		case "pcmpeqw_wc", []:
			return "pcmpeqw_wc"
		case "pcmpestri", ['r128', 'r128']:
			return "pcmpestri_r128_r128"
		case "pcmpestri_wc", []:
			return "pcmpestri_wc"
		case "pcmpestrm", ['r128', 'r128']:
			return "pcmpestrm_r128_r128"
		case "pcmpestrm_wc", []:
			return "pcmpestrm_wc"
		case "pcmpgtd", ['r128', 'r128']:
			return "pcmpgtd_r128_r128"
		case "pcmpgtd", ['r64', 'r64']:
			return "pcmpgtd_r64_r64"
		case "pcmpgtd_wc", []:
			return "pcmpgtd_wc"
		case "pcmpgtq", ['r128', 'r128']:
			return "pcmpgtq_r128_r128"
		case "pcmpgtq_wc", []:
			return "pcmpgtq_wc"
		case "pcmpgtw", ['r128', 'r128']:
			return "pcmpgtw_r128_r128"
		case "pcmpgtw", ['r64', 'r64']:
			return "pcmpgtw_r64_r64"
		case "pcmpgtw_wc", []:
			return "pcmpgtw_wc"
		case "pcmpistri", ['r128', 'r128']:
			return "pcmpistri_r128_r128"
		case "pcmpistri_wc", []:
			return "pcmpistri_wc"
		case "pcmpistrm", ['r128', 'r128']:
			return "pcmpistrm_r128_r128"
		case "pcmpistrm_wc", []:
			return "pcmpistrm_wc"
		case "pdep", ['r32', 'r32', 'r32']:
			return "pdep_r32_r32_r32"
		case "pdep", ['r64', 'r64', 'r64']:
			return "pdep_r64_r64_r64"
		case "pdep_wc", []:
			return "pdep_wc"
		case "pext", ['r32', 'r32', 'r32']:
			return "pext_r32_r32_r32"
		case "pext", ['r64', 'r64', 'r64']:
			return "pext_r64_r64_r64"
		case "pext_wc", []:
			return "pext_wc"
		case "pextrb", ['r32', 'xmm', '1']:
			return "pextrb_r32_xmm_1"
		case "pextrb_wc", []:
			return "pextrb_wc"
		case "pextrd", ['r32', 'xmm', '1']:
			return "pextrd_r32_xmm_1"
		case "pextrd_wc", []:
			return "pextrd_wc"
		case "phaddsw", ['r128', 'r128']:
			return "phaddsw_r128_r128"
		case "phaddsw", ['r64', 'r64']:
			return "phaddsw_r64_r64"
		case "phaddsw_wc", []:
			return "phaddsw_wc"
		case "phaddw", ['r128', 'r128']:
			return "phaddw_r128_r128"
		case "phaddw", ['r64', 'r64']:
			return "phaddw_r64_r64"
		case "phaddw_wc", []:
			return "phaddw_wc"
		case "phminposuw", ['r128', 'r128']:
			return "phminposuw_r128_r128"
		case "phminposuw_wc", []:
			return "phminposuw_wc"
		case "phsubd", ['r128', 'r128']:
			return "phsubd_r128_r128"
		case "phsubd", ['r64', 'r64']:
			return "phsubd_r64_r64"
		case "phsubd_wc", []:
			return "phsubd_wc"
		case "pinsrd", ['xmm', 'r32', '1']:
			return "pinsrd_xmm_r32_1"
		case "pinsrd_wc", []:
			return "pinsrd_wc"
		case "pinsrw", ['mmx', 'r32', '1']:
			return "pinsrw_mmx_r32_1"
		case "pinsrw", ['xmm', 'r32', '1']:
			return "pinsrw_xmm_r32_1"
		case "pinsrw_wc", []:
			return "pinsrw_wc"
		case "pmaddubsw", ['r128', 'r128']:
			return "pmaddubsw_r128_r128"
		case "pmaddubsw", ['r64', 'r64']:
			return "pmaddubsw_r64_r64"
		case "pmaddubsw_wc", []:
			return "pmaddubsw_wc"
		case "pmaddwd", ['r128', 'r128']:
			return "pmaddwd_r128_r128"
		case "pmaddwd", ['r64', 'r64']:
			return "pmaddwd_r64_r64"
		case "pmaddwd_wc", []:
			return "pmaddwd_wc"
		case "pmaxsw", ['r128', 'r128']:
			return "pmaxsw_r128_r128"
		case "pmaxsw", ['r64', 'r64']:
			return "pmaxsw_r64_r64"
		case "pmaxsw_wc", []:
			return "pmaxsw_wc"
		case "pmaxud", ['r128', 'r128']:
			return "pmaxud_r128_r128"
		case "pmaxud_wc", []:
			return "pmaxud_wc"
		case "pmaxuw", ['r128', 'r128']:
			return "pmaxuw_r128_r128"
		case "pmaxuw_wc", []:
			return "pmaxuw_wc"
		case "pminsb", ['r128', 'r128']:
			return "pminsb_r128_r128"
		case "pminsb_wc", []:
			return "pminsb_wc"
		case "pminub", ['r128', 'r128']:
			return "pminub_r128_r128"
		case "pminub", ['r64', 'r64']:
			return "pminub_r64_r64"
		case "pminub_wc", []:
			return "pminub_wc"
		case "pmuldq", ['r128', 'r128']:
			return "pmuldq_r128_r128"
		case "pmuldq_wc", []:
			return "pmuldq_wc"
		case "pmulhrsw", ['r128', 'r128']:
			return "pmulhrsw_r128_r128"
		case "pmulhrsw", ['r64', 'r64']:
			return "pmulhrsw_r64_r64"
		case "pmulhrsw_wc", []:
			return "pmulhrsw_wc"
		case "pmulhuw", ['r128', 'r128']:
			return "pmulhuw_r128_r128"
		case "pmulhuw", ['r64', 'r64']:
			return "pmulhuw_r64_r64"
		case "pmulhuw_wc", []:
			return "pmulhuw_wc"
		case "pmulld", ['r128', 'r128']:
			return "pmulld_r128_r128"
		case "pmulld_wc", []:
			return "pmulld_wc"
		case "pmullw", ['r128', 'r128']:
			return "pmullw_r128_r128"
		case "pmullw", ['r64', 'r64']:
			return "pmullw_r64_r64"
		case "pmullw_wc", []:
			return "pmullw_wc"
		case "pmuludq", ['r128', 'r128']:
			return "pmuludq_r128_r128"
		case "pmuludq", ['r64', 'r64']:
			return "pmuludq_r64_r64"
		case "pmuludq_wc", []:
			return "pmuludq_wc"
		case "popcnt", ['r16', 'r16']:
			return "popcnt_r16_r16"
		case "popcnt", ['r32', 'r32']:
			return "popcnt_r32_r32"
		case "popcnt", ['r64', 'r64']:
			return "popcnt_r64_r64"
		case "popcnt_wc", []:
			return "popcnt_wc"
		case "por", ['xmm', 'xmm']:
			return "por_xmm_xmm"
		case "por_wc", []:
			return "por_wc"
		case "psadbw", ['r128', 'r128']:
			return "psadbw_r128_r128"
		case "psadbw", ['r64', 'r64']:
			return "psadbw_r64_r64"
		case "psadbw_wc", []:
			return "psadbw_wc"
		case "pshufb", ['r128', 'r128']:
			return "pshufb_r128_r128"
		case "pshufb", ['r64', 'r64']:
			return "pshufb_r64_r64"
		case "pshufb_wc", []:
			return "pshufb_wc"
		case "pshufd", ['r128', 'r128']:
			return "pshufd_r128_r128"
		case "pshufd_wc", []:
			return "pshufd_wc"
		case "pshufhw", ['r128', 'r128']:
			return "pshufhw_r128_r128"
		case "pshufhw_wc", []:
			return "pshufhw_wc"
		case "pshuflw", ['r128', 'r128']:
			return "pshuflw_r128_r128"
		case "pshuflw_wc", []:
			return "pshuflw_wc"
		case "pshufw", ['r64', 'r64', 'i']:
			return "pshufw_r64_r64_i"
		case "pshufw_wc", []:
			return "pshufw_wc"
		case "psignw", ['r128', 'r128']:
			return "psignw_r128_r128"
		case "psignw", ['r64', 'r64']:
			return "psignw_r64_r64"
		case "psignw_wc", []:
			return "psignw_wc"
		case "pslld", ['r128', 'r128']:
			return "pslld_r128_r128"
		case "pslld", ['r64', 'r64']:
			return "pslld_r64_r64"
		case "pslld_wc", []:
			return "pslld_wc"
		case "pslldq", ['r128', 'i']:
			return "pslldq_r128_i"
		case "pslldq_wc", []:
			return "pslldq_wc"
		case "psllq", ['r128', 'r128']:
			return "psllq_r128_r128"
		case "psllq", ['r64', 'r64']:
			return "psllq_r64_r64"
		case "psllq_wc", []:
			return "psllq_wc"
		case "psllw", ['r128', 'i']:
			return "psllw_r128_i"
		case "psllw", ['r128', 'r128']:
			return "psllw_r128_r128"
		case "psllw", ['r64', 'i']:
			return "psllw_r64_i"
		case "psllw", ['r64', 'r64']:
			return "psllw_r64_r64"
		case "psllw_wc", []:
			return "psllw_wc"
		case "psrad", ['r128', 'i']:
			return "psrad_r128_i"
		case "psrad", ['r64', 'i']:
			return "psrad_r64_i"
		case "psrad_wc", []:
			return "psrad_wc"
		case "psraw", ['r128', 'i']:
			return "psraw_r128_i"
		case "psraw", ['r128', 'r128']:
			return "psraw_r128_r128"
		case "psraw", ['r64', 'i']:
			return "psraw_r64_i"
		case "psraw", ['r64', 'r64']:
			return "psraw_r64_r64"
		case "psraw_wc", []:
			return "psraw_wc"
		case "psrldq", ['r128', 'i']:
			return "psrldq_r128_i"
		case "psrldq_wc", []:
			return "psrldq_wc"
		case "psrlq", ['r128', 'i']:
			return "psrlq_r128_i"
		case "psrlq", ['r128', 'r128']:
			return "psrlq_r128_r128"
		case "psrlq", ['r64', 'i']:
			return "psrlq_r64_i"
		case "psrlq", ['r64', 'r64']:
			return "psrlq_r64_r64"
		case "psrlq_wc", []:
			return "psrlq_wc"
		case "ptest", ['r128', 'r128']:
			return "ptest_r128_r128"
		case "ptest_wc", []:
			return "ptest_wc"
		case "punpckhbw", ['r128', 'r128']:
			return "punpckhbw_r128_r128"
		case "punpckhbw", ['r64', 'r64']:
			return "punpckhbw_r64_r64"
		case "punpckhbw_wc", []:
			return "punpckhbw_wc"
		case "punpckhdq", ['r128', 'r128']:
			return "punpckhdq_r128_r128"
		case "punpckhdq", ['r64', 'r64']:
			return "punpckhdq_r64_r64"
		case "punpckhdq_wc", []:
			return "punpckhdq_wc"
		case "punpckhqdq", ['r128', 'r128']:
			return "punpckhqdq_r128_r128"
		case "punpckhqdq_wc", []:
			return "punpckhqdq_wc"
		case "punpckhwd", ['r128', 'r128']:
			return "punpckhwd_r128_r128"
		case "punpckhwd", ['r64', 'r64']:
			return "punpckhwd_r64_r64"
		case "punpckhwd_wc", []:
			return "punpckhwd_wc"
		case "punpckldq", ['r128', 'r128']:
			return "punpckldq_r128_r128"
		case "punpckldq", ['r64', 'r64']:
			return "punpckldq_r64_r64"
		case "punpckldq_wc", []:
			return "punpckldq_wc"
		case "punpcklqdq", ['r128', 'r128']:
			return "punpcklqdq_r128_r128"
		case "punpcklqdq_wc", []:
			return "punpcklqdq_wc"
		case "rcl", ['', '1 regsize 16']:
			return "rcl_1_r16"
		case "rcl", ['', '1 regsize 32']:
			return "rcl_1_r32"
		case "rcl", ['', '1 regsize 64']:
			return "rcl_1_r64"
		case "rcl", ['', '1 regsize 8']:
			return "rcl_1_r8"
		case "rcl", ['', '4 regsize 16']:
			return "rcl_4_r16"
		case "rcl", ['', '4 regsize 32']:
			return "rcl_4_r32"
		case "rcl", ['', '4 regsize 64']:
			return "rcl_4_r64"
		case "rcl", ['', '4 regsize 8']:
			return "rcl_4_r8"
		case "rcl", ['', 'cl regsize 16']:
			return "rcl_cl_r16"
		case "rcl", ['', 'cl regsize 32']:
			return "rcl_cl_r32"
		case "rcl", ['', 'cl regsize 64']:
			return "rcl_cl_r64"
		case "rcl", ['', 'cl regsize 8']:
			return "rcl_cl_r8"
		case "rcl_wc", []:
			return "rcl_wc"
		case "rcpps", ['r128', 'r128']:
			return "rcpps_r128_r128"
		case "rcpps_wc", []:
			return "rcpps_wc"
		case "rcpss", ['r128', 'r128']:
			return "rcpss_r128_r128"
		case "rcpss_wc", []:
			return "rcpss_wc"
		case "rcr", ['', '1 regsize 16']:
			return "rcr_1_r16"
		case "rcr", ['', '1 regsize 32']:
			return "rcr_1_r32"
		case "rcr", ['', '1 regsize 64']:
			return "rcr_1_r64"
		case "rcr", ['', '1 regsize 8']:
			return "rcr_1_r8"
		case "rcr", ['', '4 regsize 16']:
			return "rcr_4_r16"
		case "rcr", ['', '4 regsize 32']:
			return "rcr_4_r32"
		case "rcr", ['', '4 regsize 64']:
			return "rcr_4_r64"
		case "rcr", ['', '4 regsize 8']:
			return "rcr_4_r8"
		case "rcr", ['', 'cl regsize 16']:
			return "rcr_cl_r16"
		case "rcr", ['', 'cl regsize 32']:
			return "rcr_cl_r32"
		case "rcr", ['', 'cl regsize 64']:
			return "rcr_cl_r64"
		case "rcr", ['', 'cl regsize 8']:
			return "rcr_cl_r8"
		case "rcr_wc", []:
			return "rcr_wc"
		case "ret", []:
			return "ret"
		case "rol", ['', '1 regsize 16']:
			return "rol_1_r16"
		case "rol", ['', '1 regsize 32']:
			return "rol_1_r32"
		case "rol", ['', '1 regsize 64']:
			return "rol_1_r64"
		case "rol", ['', '1 regsize 8']:
			return "rol_1_r8"
		case "rol", ['', '4 regsize 16']:
			return "rol_4_r16"
		case "rol", ['', '4 regsize 32']:
			return "rol_4_r32"
		case "rol", ['', '4 regsize 64']:
			return "rol_4_r64"
		case "rol", ['', '4 regsize 8']:
			return "rol_4_r8"
		case "rol", ['', 'cl regsize 16']:
			return "rol_cl_r16"
		case "rol", ['', 'cl regsize 32']:
			return "rol_cl_r32"
		case "rol", ['', 'cl regsize 64']:
			return "rol_cl_r64"
		case "rol", ['', 'cl regsize 8']:
			return "rol_cl_r8"
		case "rol_wc", []:
			return "rol_wc"
		case "ror", ['', '1 regsize 16']:
			return "ror_1_r16"
		case "ror", ['', '1 regsize 32']:
			return "ror_1_r32"
		case "ror", ['', '1 regsize 64']:
			return "ror_1_r64"
		case "ror", ['', '1 regsize 8']:
			return "ror_1_r8"
		case "ror", ['', '4 regsize 16']:
			return "ror_4_r16"
		case "ror", ['', '4 regsize 32']:
			return "ror_4_r32"
		case "ror", ['', '4 regsize 64']:
			return "ror_4_r64"
		case "ror", ['', '4 regsize 8']:
			return "ror_4_r8"
		case "ror", ['', 'cl regsize 16']:
			return "ror_cl_r16"
		case "ror", ['', 'cl regsize 32']:
			return "ror_cl_r32"
		case "ror", ['', 'cl regsize 64']:
			return "ror_cl_r64"
		case "ror", ['', 'cl regsize 8']:
			return "ror_cl_r8"
		case "ror_wc", []:
			return "ror_wc"
		case "rorx", ['r32', 'r32', 'imm']:
			return "rorx_r32_r32_i"
		case "rorx", ['r64', 'r64', 'imm']:
			return "rorx_r64_r64_i"
		case "rorx_wc", []:
			return "rorx_wc"
		case "roundpd", ['r128', 'r128', 'i']:
			return "roundpd_r128_r128_i"
		case "roundpd_wc", []:
			return "roundpd_wc"
		case "roundps", ['r128', 'r128', 'i']:
			return "roundps_r128_r128_i"
		case "roundps_wc", []:
			return "roundps_wc"
		case "roundsd", ['r128', 'r128', 'i']:
			return "roundsd_r128_r128_i"
		case "roundsd_wc", []:
			return "roundsd_wc"
		case "roundss", ['r128', 'r128', 'i']:
			return "roundss_r128_r128_i"
		case "roundss_wc", []:
			return "roundss_wc"
		case "rsqrtps", ['r128', 'r128']:
			return "rsqrtps_r128_r128"
		case "rsqrtps_wc", []:
			return "rsqrtps_wc"
		case "rsqrtss", ['r128', 'r128']:
			return "rsqrtss_r128_r128"
		case "rsqrtss_wc", []:
			return "rsqrtss_wc"
		case "sar", ['', '1 regsize 16']:
			return "sar_1_r16"
		case "sar", ['', '1 regsize 32']:
			return "sar_1_r32"
		case "sar", ['', '1 regsize 64']:
			return "sar_1_r64"
		case "sar", ['', '1 regsize 8']:
			return "sar_1_r8"
		case "sar", ['', '4 regsize 16']:
			return "sar_4_r16"
		case "sar", ['', '4 regsize 32']:
			return "sar_4_r32"
		case "sar", ['', '4 regsize 64']:
			return "sar_4_r64"
		case "sar", ['', '4 regsize 8']:
			return "sar_4_r8"
		case "sar", ['', 'cl regsize 16']:
			return "sar_cl_r16"
		case "sar", ['', 'cl regsize 32']:
			return "sar_cl_r32"
		case "sar", ['', 'cl regsize 64']:
			return "sar_cl_r64"
		case "sar", ['', 'cl regsize 8']:
			return "sar_cl_r8"
		case "sar_wc", []:
			return "sar_wc"
		case "sarx", ['r32', 'r32', 'r32']:
			return "sarx_r32_r32_r32"
		case "sarx", ['r64', 'r64', 'r64']:
			return "sarx_r64_r64_r64"
		case "sarx_wc", []:
			return "sarx_wc"
		case "sbb", []:
			return "sarx_wc"
		case "sbb", ['+ vmovd']:
			return "sarx_wc"
		case "sbb", ['r16', 'i']:
			return "sbb_r16_i"
		case "sbb", ['r16', 'r16']:
			return "sbb_r16_r16"
		case "sbb", ['r32', 'i']:
			return "sbb_r32_i"
		case "sbb", ['r32', 'r32']:
			return "sbb_r32_r32"
		case "sbb", ['r64', 'i']:
			return "sbb_r64_i"
		case "sbb", ['r64', 'r64']:
			return "sbb_r64_r64"
		case "sbb", ['r8', 'i']:
			return "sbb_r8_i"
		case "sbb", ['r8', 'r8']:
			return "sbb_r8_r8"
		case "sbb_wc", []:
			return "sbb_wc"
		case "sfence", []:
			return "sbb_wc"
		case "sfence_wc", []:
			return "sfence_wc"
		case "shl", ['', '1 regsize 16']:
			return "shl_1_r16"
		case "shl", ['', '1 regsize 32']:
			return "shl_1_r32"
		case "shl", ['', '1 regsize 64']:
			return "shl_1_r64"
		case "shl", ['', '1 regsize 8']:
			return "shl_1_r8"
		case "shl", ['', '4 regsize 16']:
			return "shl_4_r16"
		case "shl", ['', '4 regsize 32']:
			return "shl_4_r32"
		case "shl", ['', '4 regsize 64']:
			return "shl_4_r64"
		case "shl", ['', '4 regsize 8']:
			return "shl_4_r8"
		case "shl", ['', 'cl regsize 16']:
			return "shl_cl_r16"
		case "shl", ['', 'cl regsize 32']:
			return "shl_cl_r32"
		case "shl", ['', 'cl regsize 64']:
			return "shl_cl_r64"
		case "shl", ['', 'cl regsize 8']:
			return "shl_cl_r8"
		case "shl_wc", []:
			return "shl_wc"
		case "shld", ['', '1 regsize 16']:
			return "shld_1_r16"
		case "shld", ['', '1 regsize 32']:
			return "shld_1_r32"
		case "shld", ['', '1 regsize 64']:
			return "shld_1_r64"
		case "shld", ['', '6 regsize 16']:
			return "shld_6_r16"
		case "shld", ['', '6 regsize 32']:
			return "shld_6_r32"
		case "shld", ['', '6 regsize 64']:
			return "shld_6_r64"
		case "shld", ['', 'cl regsize 16']:
			return "shld_cl_r16"
		case "shld", ['', 'cl regsize 32']:
			return "shld_cl_r32"
		case "shld", ['', 'cl regsize 64']:
			return "shld_cl_r64"
		case "shld_wc", []:
			return "shld_wc"
		case "shlx", ['r32', 'r32', 'r32']:
			return "shlx_r32_r32_r32"
		case "shlx", ['r64', 'r64', 'r64']:
			return "shlx_r64_r64_r64"
		case "shlx_wc", []:
			return "shlx_wc"
		case "shr", ['', '1 regsize 16']:
			return "shr_r16_1"
		case "shr", ['', '1 regsize 32']:
			return "shr_r32_1"
		case "shr", ['', '1 regsize 64']:
			return "shr_r64_1"
		case "shr", ['', '1 regsize 8']:
			return "shr_r8_1"
		case "shr", ['', '4 regsize 16']:
			return "shr_r16_4"
		case "shr", ['', '4 regsize 32']:
			return "shr_r32_4"
		case "shr", ['', '4 regsize 64']:
			return "shr_r64_4"
		case "shr", ['', '4 regsize 8']:
			return "shr_r8_4"
		case "shr", ['', 'cl regsize 16']:
			return "shr_r16_cl"
		case "shr", ['', 'cl regsize 32']:
			return "shr_r32_cl"
		case "shr", ['', 'cl regsize 64']:
			return "shr_r64_cl"
		case "shr", ['', 'cl regsize 8']:
			return "shr_r8_cl"
		case "shr_wc", []:
			return "shr_wc"
		case "shrd", ['', '1 regsize 16']:
			return "shrd_1_r16"
		case "shrd", ['', '1 regsize 32']:
			return "shrd_1_r32"
		case "shrd", ['', '1 regsize 64']:
			return "shrd_1_r64"
		case "shrd", ['', '6 regsize 16']:
			return "shrd_6_r16"
		case "shrd", ['', '6 regsize 32']:
			return "shrd_6_r32"
		case "shrd", ['', '6 regsize 64']:
			return "shrd_6_r64"
		case "shrd", ['', 'cl regsize 16']:
			return "shrd_cl_r16"
		case "shrd", ['', 'cl regsize 32']:
			return "shrd_cl_r32"
		case "shrd", ['', 'cl regsize 64']:
			return "shrd_cl_r64"
		case "shrd_wc", []:
			return "shrd_wc"
		case "shrx", ['r32', 'r32', 'r32']:
			return "shrx_r32_r32_r32"
		case "shrx", ['r64', 'r64', 'r64']:
			return "shrx_r64_r64_r64"
		case "shrx_wc", []:
			return "shrx_wc"
		case "shufpd", ['r128', 'r128', 'i']:
			return "shufpd_r128_r128_i"
		case "shufpd_wc", []:
			return "shufpd_wc"
		case "shufps", ['r128', 'r128', 'i']:
			return "shufps_r128_r128_i"
		case "shufps_wc", []:
			return "shufps_wc"
		case "sqrtpd", ['r128', 'r128 (best case)']:
			return "shufps_wc"
		case "sqrtpd", ['r128', 'r128 (worst case)']:
			return "sqrtpd_r128_r128"
		case "sqrtpd_wc", []:
			return "sqrtpd_wc"
		case "sqrtps", ['r128', 'r128 (best case)']:
			return "sqrtpd_wc"
		case "sqrtps", ['r128', 'r128 (worst case)']:
			return "sqrtps_r128_r128"
		case "sqrtps_wc", []:
			return "sqrtps_wc"
		case "sqrtsd", ['r128', 'r128 (best case)']:
			return "sqrtps_wc"
		case "sqrtsd", ['r128', 'r128 (worst case)']:
			return "sqrtsd_r128_r128"
		case "sqrtsd_wc", []:
			return "sqrtsd_wc"
		case "sqrtss", ['r128', 'r128 (best case)']:
			return "sqrtsd_wc"
		case "sqrtss", ['r128', 'r128 (worst case)']:
			return "sqrtss_r128_r128"
		case "sqrtss_wc", []:
			return "sqrtss_wc"
		case "stc", []:
			return "sqrtss_wc"
		case "stc_wc", []:
			return "stc_wc"
		case "std", []:
			return "stc_wc"
		case "std_wc", []:
			return "std_wc"
		case "sub", []:
			return "std_wc"
		case "sub", ['r16', 'i']:
			return "sub_r16_i"
		case "sub", ['r16', 'r16']:
			return "sub_r16_r16"
		case "sub", ['r32', 'i']:
			return "sub_r32_i"
		case "sub", ['r32', 'r32']:
			return "sub_r32_r32"
		case "sub", ['r64', 'i']:
			return "sub_r64_i"
		case "sub", ['r64', 'r64']:
			return "sub_r64_r64"
		case "sub", ['r8', 'i']:
			return "sub_r8_i"
		case "sub", ['r8', 'r8']:
			return "sub_r8_r8"
		case "sub_wc", []:
			return "sub_wc"
		case "subpd", ['r128', 'r128']:
			return "subpd_r128_r128"
		case "subpd_wc", []:
			return "subpd_wc"
		case "subsd", ['r128', 'r128']:
			return "subsd_r128_r128"
		case "subsd_wc", []:
			return "subsd_wc"
		case "test", ['mode']:
			return "test_mode"
		case "test", ['r16', 'i']:
			return "test_r16_i"
		case "test", ['r16', 'r16']:
			return "test_r16_r16"
		case "test", ['r32', 'i']:
			return "test_r32_i"
		case "test", ['r32', 'r32']:
			return "test_r32_r32"
		case "test", ['r64', 'i']:
			return "test_r64_i"
		case "test", ['r64', 'r64']:
			return "test_r64_r64"
		case "test", ['r8', 'i']:
			return "test_r8_i"
		case "test", ['r8', 'r8']:
			return "test_r8_r8"
		case "test_wc", []:
			return "test_wc"
		case "tzcnt", ['r16', 'r16']:
			return "tzcnt_r16_r16"
		case "tzcnt", ['r32', 'r32']:
			return "tzcnt_r32_r32"
		case "tzcnt", ['r64', 'r64']:
			return "tzcnt_r64_r64"
		case "tzcnt_wc", []:
			return "tzcnt_wc"
		case "ucomisd", ['r128', 'r128']:
			return "ucomisd_r128_r128"
		case "ucomisd_wc", []:
			return "ucomisd_wc"
		case "unpckhps", ['r128', 'r128']:
			return "unpckhps_r128_r128"
		case "unpckhps_wc", []:
			return "unpckhps_wc"
		case "unpcklpd", ['r128', 'r128']:
			return "unpcklpd_r128_r128"
		case "unpcklpd_wc", []:
			return "unpcklpd_wc"
		case "vcvtph2ps", ['xmm', 'xmm']:
			return "vcvtph2ps_xmm_xmm"
		case "vcvtph2ps_wc", []:
			return "vcvtph2ps_wc"
		case "vcvtps2ph", ['xmm', 'xmm']:
			return "vcvtps2ph_xmm_xmm"
		case "vcvtps2ph", ['xmm', 'xmm', '0']:
			return "vcvtps2ph_xmm_xmm_0"
		case "vcvtps2ph", ['xmm', 'ymm', '0']:
			return "vcvtps2ph_xmm_ymm_0"
		case "vcvtps2ph", ['xmm', 'xmm', '0']:
			return "vcvtps2ph_xmm_xmm_0"
		case "vcvtps2ph_wc", []:
			return "vcvtps2ph_wc"
		case "vextractf128", ['[m128]', 'ymm', '0 + vmovdqa x', '[m]']:
			return "vcvtps2ph_wc"
		case "vextractf128", ['[m128]', 'ymm', '1 + vmovdqa x', '[m]']:
			return "vcvtps2ph_wc"
		case "vextractf128", ['xmm', 'ymm', '0']:
			return "vextractf128_xmm_ymm_0"
		case "vextractf128", ['xmm', 'ymm', '0 + vinsertf128 y', 'y', 'x', '1']:
			return "vextractf128_xmm_ymm_0"
		case "vextractf128", ['xmm', 'ymm', '1']:
			return "vextractf128_xmm_ymm_1"
		case "vextractf128", ['xmm', 'ymm', '1 + vinsertf128 y', 'y', 'x', '1']:
			return "vextractf128_xmm_ymm_1"
		case "vextractf128", ['ymm', '']:
			return "vextractf128_ymm"
		case "vextractf128_wc", []:
			return "vextractf128_wc"
		case "vextracti128", ['[m128]', 'ymm', '0 + vmovdqa x', '[m]']:
			return "vextractf128_wc"
		case "vextracti128", ['[m128]', 'ymm', '1 + vmovdqa x', '[m]']:
			return "vextractf128_wc"
		case "vextracti128", ['xmm', 'ymm', '0']:
			return "vextracti128_xmm_ymm_0"
		case "vextracti128", ['xmm', 'ymm', '1']:
			return "vextracti128_xmm_ymm_1"
		case "vextracti128_wc", []:
			return "vextracti128_wc"
		case "vfmadd132pd", ['r128', 'r128', 'r128']:
			return "vfmadd132pd_r128_r128_r128"
		case "vfmadd132pd", ['r256', 'r256', 'r256']:
			return "vfmadd132pd_r256_r256_r256"
		case "vfmadd132pd_wc", []:
			return "vfmadd132pd_wc"
		case "vfmadd132ps", ['r128', 'r128', 'r128']:
			return "vfmadd132ps_r128_r128_r128"
		case "vfmadd132ps", ['r256', 'r256', 'r256']:
			return "vfmadd132ps_r256_r256_r256"
		case "vfmadd132ps_wc", []:
			return "vfmadd132ps_wc"
		case "vfmadd132sd", ['r128', 'r128', 'r128']:
			return "vfmadd132sd_r128_r128_r128"
		case "vfmadd132sd_wc", []:
			return "vfmadd132sd_wc"
		case "vfmadd132ss", ['r128', 'r128', 'r128']:
			return "vfmadd132ss_r128_r128_r128"
		case "vfmadd132ss_wc", []:
			return "vfmadd132ss_wc"
		case "vfmadd213ps", ['r128', 'r128', 'r128']:
			return "vfmadd213ps_r128_r128_r128"
		case "vfmadd213ps", ['r256', 'r256', 'r256']:
			return "vfmadd213ps_r256_r256_r256"
		case "vfmadd213ps_wc", []:
			return "vfmadd213ps_wc"
		case "vfmadd213ss", ['r128', 'r128', 'r128']:
			return "vfmadd213ss_r128_r128_r128"
		case "vfmadd213ss_wc", []:
			return "vfmadd213ss_wc"
		case "vfmadd231pd", ['r128', 'r128', 'r128']:
			return "vfmadd231pd_r128_r128_r128"
		case "vfmadd231pd", ['r256', 'r256', 'r256']:
			return "vfmadd231pd_r256_r256_r256"
		case "vfmadd231pd_wc", []:
			return "vfmadd231pd_wc"
		case "vfmadd231ps", ['r128', 'r128', 'r128']:
			return "vfmadd231ps_r128_r128_r128"
		case "vfmadd231ps", ['r256', 'r256', 'r256']:
			return "vfmadd231ps_r256_r256_r256"
		case "vfmadd231ps_wc", []:
			return "vfmadd231ps_wc"
		case "vfmadd231sd", ['r128', 'r128', 'r128']:
			return "vfmadd231sd_r128_r128_r128"
		case "vfmadd231sd_wc", []:
			return "vfmadd231sd_wc"
		case "vfmadd231ss", ['r128', 'r128', 'r128']:
			return "vfmadd231ss_r128_r128_r128"
		case "vfmadd231ss_wc", []:
			return "vfmadd231ss_wc"
		case "vfmsub132pd", ['r128', 'r128', 'r128']:
			return "vfmsub132pd_r128_r128_r128"
		case "vfmsub132pd", ['r256', 'r256', 'r256']:
			return "vfmsub132pd_r256_r256_r256"
		case "vfmsub132pd_wc", []:
			return "vfmsub132pd_wc"
		case "vfmsub132sd", ['r128', 'r128', 'r128']:
			return "vfmsub132sd_r128_r128_r128"
		case "vfmsub132sd_wc", []:
			return "vfmsub132sd_wc"
		case "vfmsub231pd", ['r128', 'r128', 'r128']:
			return "vfmsub231pd_r128_r128_r128"
		case "vfmsub231pd", ['r256', 'r256', 'r256']:
			return "vfmsub231pd_r256_r256_r256"
		case "vfmsub231pd_wc", []:
			return "vfmsub231pd_wc"
		case "vfmsub231sd", ['r128', 'r128', 'r128']:
			return "vfmsub231sd_r128_r128_r128"
		case "vfmsub231sd_wc", []:
			return "vfmsub231sd_wc"
		case "vfnmadd132pd", ['r128', 'r128', 'r128']:
			return "vfnmadd132pd_r128_r128_r128"
		case "vfnmadd132pd", ['r256', 'r256', 'r256']:
			return "vfnmadd132pd_r256_r256_r256"
		case "vfnmadd132pd_wc", []:
			return "vfnmadd132pd_wc"
		case "vfnmadd132sd", ['r128', 'r128', 'r128']:
			return "vfnmadd132sd_r128_r128_r128"
		case "vfnmadd132sd_wc", []:
			return "vfnmadd132sd_wc"
		case "vfnmadd231pd", ['r128', 'r128', 'r128']:
			return "vfnmadd231pd_r128_r128_r128"
		case "vfnmadd231pd", ['r256', 'r256', 'r256']:
			return "vfnmadd231pd_r256_r256_r256"
		case "vfnmadd231pd_wc", []:
			return "vfnmadd231pd_wc"
		case "vfnmadd231sd", ['r128', 'r128', 'r128']:
			return "vfnmadd231sd_r128_r128_r128"
		case "vfnmadd231sd_wc", []:
			return "vfnmadd231sd_wc"
		case "vfnmsub132pd", ['r128', 'r128', 'r128']:
			return "vfnmsub132pd_r128_r128_r128"
		case "vfnmsub132pd", ['r256', 'r256', 'r256']:
			return "vfnmsub132pd_r256_r256_r256"
		case "vfnmsub132pd_wc", []:
			return "vfnmsub132pd_wc"
		case "vfnmsub132sd", ['r128', 'r128', 'r128']:
			return "vfnmsub132sd_r128_r128_r128"
		case "vfnmsub132sd_wc", []:
			return "vfnmsub132sd_wc"
		case "vfnmsub231pd", ['r128', 'r128', 'r128']:
			return "vfnmsub231pd_r128_r128_r128"
		case "vfnmsub231pd", ['r256', 'r256', 'r256']:
			return "vfnmsub231pd_r256_r256_r256"
		case "vfnmsub231pd_wc", []:
			return "vfnmsub231pd_wc"
		case "vfnmsub231sd", ['r128', 'r128', 'r128']:
			return "vfnmsub231sd_r128_r128_r128"
		case "vfnmsub231sd_wc", []:
			return "vfnmsub231sd_wc"
		case "vinsertf128", ['y', 'y', 'x', '1']:
			return "vinsertf128_ymm_ymm_xmm_1"
		case "vinsertf128", ['ymm', '']:
			return "vinsertf128_ymm"
		case "vinsertf128", ['ymm', 'ymm', 'xmm', '0']:
			return "vinsertf128_ymm_ymm_xmm_0"
		case "vinsertf128", ['ymm', 'ymm', 'xmm', '0 + vextracti128 xmm', 'ymm', '1']:
			return "vinsertf128_ymm_ymm_xmm_0"
		case "vinsertf128", ['ymm', 'ymm', 'xmm', '1']:
			return "vinsertf128_ymm_ymm_xmm_1"
		case "vinsertf128", ['ymm', 'ymm', 'xmm', '1 + vextracti128 xmm', 'ymm', '1']:
			return "vinsertf128_ymm_ymm_xmm_1"
		case "vinsertf128_wc", []:
			return "vinsertf128_wc"
		case "vinserti128", ['y', 'y', 'x', '1']:
			return "vinserti128_ymm_ymm_xmm_1"
		case "vinserti128", ['ymm', 'xmm', 'xmm', '1']:
			return "vinserti128_ymm_xmm_xmm_1"
		case "vinserti128", ['ymm', 'ymm', 'xmm', '0']:
			return "vinserti128_ymm_ymm_xmm_0"
		case "vinserti128", ['ymm', 'ymm', 'xmm', '0 + vextractf128 xmm', 'ymm', '1']:
			return "vinserti128_ymm_ymm_xmm_0"
		case "vinserti128", ['ymm', 'ymm', 'xmm', '0 + vextracti128 xmm', 'ymm', '1']:
			return "vinserti128_ymm_ymm_xmm_0"
		case "vinserti128", ['ymm', 'ymm', 'xmm', '1']:
			return "vinserti128_ymm_ymm_xmm_1"
		case "vinserti128", ['ymm', 'ymm', 'xmm', '1 + vextractf128 xmm', 'ymm', '1']:
			return "vinserti128_ymm_ymm_xmm_1"
		case "vinserti128", ['ymm', 'ymm', 'xmm', '1 + vextracti128 xmm', 'ymm', '1']:
			return "vinserti128_ymm_ymm_xmm_1"
		case "vinserti128_wc", []:
			return "vinserti128_wc"
		case "vpbroadcastb", ['xmm', 'm8 + mov.. m8', 'xmm']:
			return "vinserti128_wc"
		case "vpbroadcastb", ['xmm', 'xmm']:
			return "vpbroadcastb_xmm_xmm"
		case "vpbroadcastb", ['ymm', 'm8 + mov.. m8', 'xmm']:
			return "vpbroadcastb_xmm_xmm"
		case "vpbroadcastb", ['ymm', 'xmm']:
			return "vpbroadcastb_ymm_xmm"
		case "vpbroadcastb_wc", []:
			return "vpbroadcastb_wc"
		case "vpbroadcastd", ['xmm', 'm32 + mov.. m32', 'xmm']:
			return "vpbroadcastb_wc"
		case "vpbroadcastd", ['xmm', 'xmm']:
			return "vpbroadcastd_xmm_xmm"
		case "vpbroadcastd", ['ymm', 'm32 + mov.. m32', 'xmm']:
			return "vpbroadcastd_xmm_xmm"
		case "vpbroadcastd", ['ymm', 'xmm']:
			return "vpbroadcastd_ymm_xmm"
		case "vpbroadcastd_wc", []:
			return "vpbroadcastd_wc"
		case "vpbroadcastq", ['xmm', 'm64 + mov.. m64', 'xmm']:
			return "vpbroadcastd_wc"
		case "vpbroadcastq", ['xmm', 'xmm']:
			return "vpbroadcastq_xmm_xmm"
		case "vpbroadcastq", ['ymm', 'm64 + mov.. m64', 'xmm']:
			return "vpbroadcastq_xmm_xmm"
		case "vpbroadcastq", ['ymm', 'xmm']:
			return "vpbroadcastq_ymm_xmm"
		case "vpbroadcastq_wc", []:
			return "vpbroadcastq_wc"
		case "vpbroadcastw", ['xmm', 'm16 + mov.. m16', 'xmm']:
			return "vpbroadcastq_wc"
		case "vpbroadcastw", ['xmm', 'xmm']:
			return "vpbroadcastw_xmm_xmm"
		case "vpbroadcastw", ['ymm', 'm16 + mov.. m16', 'xmm']:
			return "vpbroadcastw_xmm_xmm"
		case "vpbroadcastw", ['ymm', 'xmm']:
			return "vpbroadcastw_ymm_xmm"
		case "vpbroadcastw_wc", []:
			return "vpbroadcastw_wc"
		case "vperm2f128", ['r256', 'r256', 'r256', 'i']:
			return "vperm2f128_r256_r256_r256_i"
		case "vperm2f128_wc", []:
			return "vperm2f128_wc"
		case "vpermilpd", ['r128', 'r128', 'i']:
			return "vpermilpd_r128_r128_i"
		case "vpermilpd", ['r128', 'r128', 'r128']:
			return "vpermilpd_r128_r128_r128"
		case "vpermilpd", ['r256', 'r256', 'i']:
			return "vpermilpd_r256_r256_i"
		case "vpermilpd", ['r256', 'r256', 'r256']:
			return "vpermilpd_r256_r256_r256"
		case "vpermilpd_wc", []:
			return "vpermilpd_wc"
		case "vpermilps", ['r128', 'r128', 'i']:
			return "vpermilps_r128_r128_i"
		case "vpermilps", ['r128', 'r128', 'r128']:
			return "vpermilps_r128_r128_r128"
		case "vpermilps", ['r256', 'r256', 'i']:
			return "vpermilps_r256_r256_i"
		case "vpermilps", ['r256', 'r256', 'r256']:
			return "vpermilps_r256_r256_r256"
		case "vpermilps_wc", []:
			return "vpermilps_wc"
		case "vtestps", ['r128', 'r128 + sbb + movd']:
			return "vpermilps_wc"
		case "vtestps_wc", []:
			return "vtestps_wc"
		case "xadd", ['[m16]', 'r16']:
			return "xadd_[m16]_r16"
		case "xadd", ['[m32]', 'r32']:
			return "xadd_[m32]_r32"
		case "xadd", ['[m64]', 'r64']:
			return "xadd_[m64]_r64"
		case "xadd", ['[m8]', 'r8']:
			return "xadd_[m8]_r8"
		case "xadd_wc", []:
			return "xadd_wc"
		case "xchg", ['r16', 'r16']:
			return "xchg_r16_r16"
		case "xchg", ['r32', 'r32']:
			return "xchg_r32_r32"
		case "xchg", ['r64', 'r64']:
			return "xchg_r64_r64"
		case "xchg", ['r8', 'r8']:
			return "xchg_r8_r8"
		case "xchg_wc", []:
			return "xchg_wc"
		case "xlat", []:
			return "xchg_wc"
		case "xlat_wc", []:
			return "xlat_wc"
		case "xor", ['r16', 'i']:
			return "xor_r16_i"
		case "xor", ['r16', 'r16']:
			return "xor_r16_r16"
		case "xor", ['r32', 'i']:
			return "xor_r32_i"
		case "xor", ['r32', 'r32']:
			return "xor_r32_r32"
		case "xor", ['r64', 'i']:
			return "xor_r64_i"
		case "xor", ['r64', 'r64']:
			return "xor_r64_r64"
		case "xor", ['r8', 'i']:
			return "xor_r8_i"
		case "xor", ['r8', 'r8']:
			return "xor_r8_r8"
		case "xor_wc", []:
			return "xor_wc"
		case "xsave", ['+ xrstor']:
			return "xor_wc"
		case "xsave_wc", []:
			return "xsave_wc"
