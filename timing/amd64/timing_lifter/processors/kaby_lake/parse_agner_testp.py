# This file generates i5_7300u.py
# https://github.com/biqar/agner-testp/tree/master
# First need to run ./agner-testp/testp/TestScripts/allsh1.sh to generate ./agner-testp/testp/TestScripts/results1/
import os
import re
import sys
from collections import defaultdict
from pathlib import Path
from i5_7300u_old1 import time_of_instr as itime

# From ./jle_ret.c
custom = {
    "ret": 13,
    "jle_addr": 5,
    # Have to measure these!
    "jz_addr" : 1,
    "jmp_addr" : 1,
    "jnz_addr" : 1,
    "jnc_addr" : 1,
    "jge_addr" : 1,
    "jg_addr" : 1,
    "lea_r32_addr" : 1
    #lea
}



def parse_agner_results(dir, mnemonics):
    wcet_dict = defaultdict(int)
    number_usable_blocks = 0
    number_no_use_blocks = 0
    mnemonics = set(mnemonics)

    # Get all .txt files in current directory
    txt_files = [Path(f) for f in os.listdir(dir) if f.endswith('.txt')]

    # Pattern to extract numeric columns (Core cyc, Instruct)
    numeric_line = re.compile(r'^\s*(\d+)\s+(\d+)\s+(\d+)')

    #Table header
    table_headers = re.compile(r'^\s*clock.*$')
    with open('i5_7300u_new.py','w') as output:
        for fname in txt_files:
            block_found = False
            #print(f"(* {fname} *)")
            
            with open(Path(dir) / fname) as f:
                current_instr = None
                #print("FILE NAME: ",fname) 
                for line in f:
                    line = line.strip()
                    line = line.lower()
                    
                    if 'memory destination operand:' in line:
                        line = line[line.index('memory destination operand:'):]
                    if 'memory operand:' in line:
                        line = line[line.index('memory operand:'):]
                    words = line.split(' ')
                    # Detect new instruction block
                    common = list(set(words) & mnemonics)
                    
                    if common and (not re.search(table_headers, line)):
                        if ((re.search(r'latency', line))):
                            instr_full = line[line.index(common[0]):]
                            match = re.search(r':|latency|/', instr_full)
                            if match:
                                instr_full=instr_full[:match.start()]
                            block_found = True  
                            current_instr = instr_full.strip()                  
                            #print('current instruction considered: ',current_instr)
                        elif((re.search(r'throughput',line))):
                            #print('not considered: ', line)
                            block_found = False 
                        
                    if re.search(table_headers, line):
                        if current_instr:
                            if 'movaps' in current_instr: 
                                print(line)

                    if current_instr and block_found:
                        mnum = numeric_line.match(line)
                        if mnum:
                            # Core cyc = column 2, Instruct = column 3
                            core_cyc = int(mnum.group(2))
                            instructs = int(mnum.group(3))
                            if instructs > 0:
                                latency = int(round(core_cyc / instructs))
                                # Update WCET as max observed
                                max_latency = max(latency,wcet_dict[current_instr])
                                wcet_dict[current_instr] = max_latency
                                ci = current_instr.replace(', ', ' ').split()
                                wcet_dict[ci[0]+'_wc'] = max(latency, wcet_dict[ci[0]+'_wc'])
                    
        wcet_dict.update(custom) 
        output.write('def time_of_instr(mnemonic: str) -> str :\n\tmatch mnemonic:\n')
        for instr in sorted(wcet_dict.keys()):
            output.write(f"\t\tcase \"{instr}\":\n\t\t\treturn \"{wcet_dict[instr]}\"\n")                
    return wcet_dict

def parse_wcet_instructions(wcet):
    parsed_instr ={} 
    for instr in wcet:
        og_instr = instr
        if not('+' in instr) and not('best' in instr) and not ('..' in instr):
            instr = instr.replace('registersize','r')
            instr = instr.replace('(worstcase)','')
            instr = instr.replace('(worst case)','')
            instr = instr.replace('high','h')
            instr = instr.replace('imm','i')
            instr = re.sub(r'regsize (\d+)', r'r\1', instr)
            instr = re.sub(r'numop (\d+)', r'', instr)
            instr = re.sub(r'r (\d+)', r'r\1', instr)
            instr = re.sub(r'\by\b', 'ymm', instr)
            instr = re.sub(r'\bx\b', 'xmm', instr)
            instr = instr.replace(',',' ')
            if re.search(r'\b(jmp|jle|jnz|jz|jnc|jge|jg)_addr\b',instr) \
               or re.search(r'\b(.*)_wc\b', instr):
                parsed_instr[instr]=wcet[og_instr]
            instr_split = instr.replace(', ', ' ').split()
            instr = '_'.join(instr_split)

            if 'ret' == instr:parsed_instr[instr]=wcet[og_instr]
            

            if len(instr_split) > 1 :
                if 'shr_' in instr:
                    instr='shr'+'_'+instr_split[2]+'_'+instr_split[1]
                parsed_instr[instr]=wcet[og_instr]

    return parsed_instr

def time_of_addr(timing_behavior_instructions):
    # Get all .txt files in current directory
    v_files = [Path(f) for f in os.listdir('./timing_x86_lifted') if f.endswith('.v')]

    replacer_dict={}
    #r64
    replacer_dict.update({'rcx':'r64','rax':"r64",'rbx':"r64",'rdx':"r64",
                          'rsi':"r64",'rdi':"r64",'rsp':"r64",'rbp':"r64",
                          'r8':"r64",'r9':"r64",'r10':"r64",'r11':"r64",
                          'r12':"r64",'r13':"r64",'r14':"r64",'r15': "r64"})
    #r32
    replacer_dict.update({'ecx':'r32','eax':'r32','ebx':'r32','edx':'r32',
                          'esi':'r32','edi':'r32','esp':'r32','ebp':'r32',
                          'r8d':'r32','r9d':'r32','r10d':'r32','r11d':'r32',
                          'r12d':'r32','r13d':'r32','r14d':'r32','r15d':'r32'})
    #r16
    replacer_dict.update({'ax':'r16','bx':'r16','cx':'r16','dx':'r16','si':'r16',
                          'di':'r16','sp':'r16','bp':'r16','r8w':'r16','r9w':'r16',
                          'r10w':'r16','r11w':'r16','r12w':'r16','r13w':'r16',
                          'r14w':'r16','r15w':'r16'})

    #r8
    replacer_dict.update({'ah':'r8','al':'r8','bh':'r8','bl':'r8','ch':'r8','cl':'r8',
                          'dh':'r8','dl':'r8','sil':'r8','dil':'r8','spl':'r8',
                          'bpl':'r8','r8b':'r8','r9b':'r8','r10b':'r8','r11b':'r8',
                          'r12b':'r8','r13b':'r8','r14b':'r8','r15b':'r8'})

    with open('time_of_addrs.txt','w') as output:
        for file in v_files:
            filedata = ''
            with open("timing_x86_lifted/"+str(file)) as f:
                filedata = f.read()
            #addr_to_time
            output.write('File : '+str(file)+'\n')
            output.write('Definition time_of_addr (s : store) (a : addr) : N :=\n')
            output.write('\tmatch a with\n')
            cmd = re.compile("\(\*[^else]+\*\)")
            patterns = cmd.findall(filedata)
            for pattern in patterns:
                #print(pattern)
                line = pattern.split('\n')[0].lower()
                address = line[line.index('(*')+2:line.index(':')]
                instruction = line[line.index(':')+1:line.index('*)')].strip()
                instruction = instruction.replace(',',' ')
                #print(instruction)
                #dword, hword, etc.
                if re.search(r'\b(dword|qword)\b', instruction):
                    instruction = re.sub(r'dword ptr \[.*?\]', '[m32]', instruction)
                    instruction = re.sub(r'qword ptr \[.*?\]', '[m64]', instruction)   
                if re.search(r'\b(cmp|add|test|shr|sub)\b',instruction):
                    instr_split = instruction.split(' ')
                    if '0x' in instr_split[2]:
                        instruction = instr_split[0]+' '+instr_split[1]+' i'
                if re.search(r'lea', instruction):
                    instr_split = instruction.split(' ')
                    instruction = instr_split[0]+' '+instr_split[1]+' addr'
                
                #handle jmps
                if re.search(r'\b(jmp|jle|jnz|jz|jnc|jge|jg)\b', instruction):
                    instr_split = instruction.split(' ')
                    instruction= instr_split[0]+' '+'addr'

                result = '_'.join(replacer_dict.get(word, word) for word in instruction.split())

                #in dict?
                if not(result in timing_behavior_instructions):
                    if not 'nop' in result:
                        i_split = result.split('_')
                        if i_split: result = i_split[0]+'_wc'
                output.write(f'\t\t|{address}\t=>{result}\n')


def cpuTimingModule(timing_behavior_instructions):
    with open('CPUTimingModule_new.v','w') as file:
        file.write('Require Import NArith.\n\nModule Type CPUTimingModule.\n(* === Instruction Timings === *)\n\tParameter')
        i=0
        for instr in timing_behavior_instructions:
            if i%5==0: 
                file.write('\n\t\t')
            file.write(instr+' ')
            i+=1
        file.write('\n\t:N.\nEnd CPUTimingModule.')

def gen_timing_config(timing_behavior_instructions):
    with open('timing_config.v','w') as config_file:
        config_file.write('Require Import CPUTimingModule.\n'+
                          'Require Import NArith.\nRequire Import Picinae_core.\n'+
                          'Open Scope N.\n')
        config_file.write('Module Type x86Config.\n'+
                          '\tParameter CLOCK_FREQUENCY : N.\n'+
                          'End x86Config.\n')
        config_file.write('Module x86 (cfg : x86Config) <: CPUTimingModule.\n')
        config_file.write('\tParameter T_data_latency : N.\n'+
                            '\tParameter T_inst_latency : N.\n'+
                        '\t(* ==== Instructions ==== *)\n')
        for instr , value in timing_behavior_instructions.items():
            config_file.write(f'\tDefinition '+instr+' := '+str(value)+'.\n')
        config_file.write('End x86.\n')
        config_file.write('Module x86BaseConfig <: x86Config.\n'+
                          '(* 50 MHz *)\n'+'\tDefinition CLOCK_FREQUENCY : N := 50000000.\n'+
                          'End x86BaseConfig.\n')    
        config_file.write('Module x86Base := x86 x86BaseConfig.')


header = """# This file was generated by parse_agner_testp.py
def time_of_instr(mnemonic: str, args: List[X86Var]) -> str :
    match mnemonic:"""

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("usage: python parse_agner_testp.py <path_to_results1>")
        exit(1)

    with open("./x86_mnemonics.txt") as file:
        mnemonics = [line.strip().lower() for line in file.readlines()]

    wcet = parse_agner_results(sys.argv[1], mnemonics)

    # Print sorted by mnemonic
    #for instr in sorted(wcet.keys()):
        #print(f"        case \"{instr}\":\n            return \"{wcet[instr]}\"")
    
    #parse wcet instructions
    timing_behavior_instructions = parse_wcet_instructions(wcet)

    #write instr to timingmoduletype
    #cpuTimingModule(timing_behavior_instructions)

    #write time_of_addr for given .v files under ./timing_x86_lifted
    #time_of_addr(timing_behavior_instructions)

    #create timing configuration file
    #gen_timing_config(timing_behavior_instructions)

        

