package common;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;

public class Lib {
	public static final HashMap<String, String> FLAG_CONDITIONS;
	public static final HashMap<String, Triplet<String, Integer, Integer>> REG_INFO_DICT;
	public static final HashMap<Integer, Triplet<String, String, String>> AUX_REG_INFO;
	public static final String TERMINATION_FUNCTIONS[];
	
	public static final String REG64_NAME_LIST[] = new String[] {
			"rax", "rbx", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15", "rsp", "rbp"};
	
	public static final HashSet<String> REG64_NAMES;
	public static final HashSet<String> REG_NAMES;
	
	public static final HashSet<String> CONDITIONAL_JMP_INST;
	public static final HashSet<String> JMP_INST;
	public static final HashSet<String> JMP_INST_WITHOUT_CALL;
	public static final HashSet<String> JMP_INST_WITH_ADDRESS;

	public static final HashSet<String> CALLEE_SAVED_REGS = new HashSet<>(Arrays.asList("rbx", "rbp", "r12", "r13", "r14", "r15"));
	
	public static final HashSet<String> CALLEE_NOT_SAVED_REGS = new HashSet<>(Arrays.asList("rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11"));
	
	public static final String RFlags[] = new String[] {"CF", "ZF", "OF", "SF"};
	public static final HashSet<String> SEG_REGS = new HashSet<>(Arrays.asList("ss", "cs", "ds", "es", "fs", "gs"));
	
	public static final HashSet<String> GENERAL_INSTRUCTIONS;
	public static final HashSet<String> INSTS_AFF_FLAGS_WO_CMP_TEST;
	
	public static final int DEFAULT_REG_LEN = 64;
	public static final int C_INT_LEN = 32;
	
	public static final String REG = "register";
	public static final String MEM = "memory";
	public static final String FLAGS = "flags";
	public static final String FS = "fs";
	public static final String CS = "cs";
	public static final String GS = "gs";
	public static final String AUX_MEM = "aux_memory";
	public static final String STDIN = "stdin";
	public static final String STDOUT = "stdout";
	public static final String NEED_TRACE_BACK = "need_trace_back";
	public static final String POINTER_RELATED_ERROR = "pointer_related_error";
	public static final String STDOUT_ADDRESS = "stdout_address";
	public static final String STDOUT_HANDLER = "stdout_handler";
	public static final String VERIFIED_FUNC_INFO = "verified_func_info";
	public static final String TO_BE_VERIFIED_ARGS = "to_be_verified_args";
	public static final String CALLEE_SAVED_REG_INFO = "callee_saved_reg_info";
	public static final String MEM_CONTENT_POLLUTED = "mem_content_polluted";
	public static final String HEAP_ADDR = "heap_addr";
	
	public static final Set<String> STATE_NAMES = Set.of(REG, MEM, FLAGS, FS, CS, GS, STDOUT);
	public static final Set<String> SEG_STATE_NAMES = Set.of(FS, CS, GS);
	
	public static final Set<String> RECORD_STATE_NAMES = Set.of(REG, MEM);
	
	public static final Set<String> CONDITIONAL_MOV_INST;
	public static final Set<String> CONDITIONAL_SET_INST;
	
	public static enum MEM_DATA_SECT_STATUS {
	    RAW,
	    POLLUTED,
	    RESTORED
	}


	public static enum MEMORY_RELATED_ERROR_TYPE {
		NONE,
	    NULL_POINTER_DEREFERENCE,
	    USE_AFTER_FREE,
	    FREE_AFTER_FREE,
	    BUFFER_OVERFLOW
	}


	public static enum TRACE_BACK_TYPE {
	    INDIRECT,
	    SYMBOLIC,
	}


	public static enum TRACE_BACK_RET_TYPE {
	    JT_UNRESOLVED,
	    JT_SUCCEED,
	    JT_NO_UPPERBOUND,
	    JT_NOT_ASSIGN_INST,
	    JT_NO_DISTINCT_ENTRIES,
	    JT_NO_TARGET_ADDRESSES,
	    SYMADDR_SUCCEED,
	    SYMADDR_NO_FUNC_INVARIANTS,
	    SYMADDR_W_FUNC_INDOUBT,
	    SYMADDR_UNINITIALIZED_MEM_CONTENT,
	    SYMADDR_SYM_NOT_IN_GLOBAL_VALUTSET,
	    TB_PARENT_BLOCK_DOES_NOT_EXIST,
	    TB_BLOCK_DOES_NOT_EXIST,
	    TB_COUNT_EXCEEDS_LIMITATION
	}
	
	static {
		FLAG_CONDITIONS = new HashMap<String, String>();
		FLAG_CONDITIONS.put("a",  "CF==0 and ZF==0");
		FLAG_CONDITIONS.put("ae",  "CF==0");
		FLAG_CONDITIONS.put("b",  "CF==1");
		FLAG_CONDITIONS.put("be",  "CF==1 or ZF==1");
		FLAG_CONDITIONS.put("c",  "CF==1");
		FLAG_CONDITIONS.put("e",  "ZF==1");
		FLAG_CONDITIONS.put("g",  "ZF==0 and SF==OF");
		FLAG_CONDITIONS.put("ge",  "SF==OF");
		FLAG_CONDITIONS.put("l",  "SF<>OF");
		FLAG_CONDITIONS.put("le",  "ZF==1 or SF<>OF");
		FLAG_CONDITIONS.put("na",  "CF==1 or ZF==1");
		FLAG_CONDITIONS.put("nae",  "CF==1");
		FLAG_CONDITIONS.put("nb",  "CF==0");
		FLAG_CONDITIONS.put("nbe",  "CF==0 and ZF==0");
		FLAG_CONDITIONS.put("nc",  "CF==0");
		FLAG_CONDITIONS.put("ne",  "ZF==0");
		FLAG_CONDITIONS.put("ng",  "ZF==1 or SF<>OF");
		FLAG_CONDITIONS.put("nge",  "SF<>OF");
		FLAG_CONDITIONS.put("nl",  "SF==OF");
		FLAG_CONDITIONS.put("nle",  "ZF==0 and SF==OF");
		FLAG_CONDITIONS.put("no",  "OF==0");
		FLAG_CONDITIONS.put("np",  "PF==0");
		FLAG_CONDITIONS.put("ns",  "SF==0");
		FLAG_CONDITIONS.put("nz",  "ZF==0");
		FLAG_CONDITIONS.put("o",  "OF==1");
		FLAG_CONDITIONS.put("p",  "PF==1");
		FLAG_CONDITIONS.put("pe",  "PF==1");
		FLAG_CONDITIONS.put("po",  "PF==0");
		FLAG_CONDITIONS.put("s",  "SF==1");
		FLAG_CONDITIONS.put("z",  "ZF==1");
		
		REG_INFO_DICT = new HashMap<String, Triplet<String, Integer, Integer>>();
		REG_INFO_DICT.put("ah", new Triplet<String, Integer, Integer>("rax", 8, 8));
		REG_INFO_DICT.put("bh", new Triplet<String, Integer, Integer>("rbx", 8, 8));
		REG_INFO_DICT.put("ch", new Triplet<String, Integer, Integer>("rcx", 8, 8));
		REG_INFO_DICT.put("dh", new Triplet<String, Integer, Integer>("rdx", 8, 8));
		REG_INFO_DICT.put("eax", new Triplet<String, Integer, Integer>("rax", 0, 32));
		REG_INFO_DICT.put("ax", new Triplet<String, Integer, Integer>("rax", 0, 16));
		REG_INFO_DICT.put("al", new Triplet<String, Integer, Integer>("rax", 0, 8));
		REG_INFO_DICT.put("ebx", new Triplet<String, Integer, Integer>("rbx", 0, 32));
		REG_INFO_DICT.put("bx", new Triplet<String, Integer, Integer>("rbx", 0, 16));
		REG_INFO_DICT.put("bl", new Triplet<String, Integer, Integer>("rbx", 0, 8));
		REG_INFO_DICT.put("ecx", new Triplet<String, Integer, Integer>("rcx", 0, 32));
		REG_INFO_DICT.put("cx", new Triplet<String, Integer, Integer>("rcx", 0, 16));
		REG_INFO_DICT.put("cl", new Triplet<String, Integer, Integer>("rcx", 0, 8));
		REG_INFO_DICT.put("edx", new Triplet<String, Integer, Integer>("rdx", 0, 32));
		REG_INFO_DICT.put("dx", new Triplet<String, Integer, Integer>("rdx", 0, 16));
		REG_INFO_DICT.put("dl", new Triplet<String, Integer, Integer>("rdx", 0, 8));
		REG_INFO_DICT.put("esi", new Triplet<String, Integer, Integer>("rsi", 0, 32));
		REG_INFO_DICT.put("si", new Triplet<String, Integer, Integer>("rsi", 0, 16));
		REG_INFO_DICT.put("sil", new Triplet<String, Integer, Integer>("rsi", 0, 8));
		REG_INFO_DICT.put("edi", new Triplet<String, Integer, Integer>("rdi", 0, 32));
		REG_INFO_DICT.put("di", new Triplet<String, Integer, Integer>("rdi", 0, 16));
		REG_INFO_DICT.put("dil", new Triplet<String, Integer, Integer>("rdi", 0, 8));
		REG_INFO_DICT.put("ebp", new Triplet<String, Integer, Integer>("rbp", 0, 32));
		REG_INFO_DICT.put("bp", new Triplet<String, Integer, Integer>("rbp", 0, 16));
		REG_INFO_DICT.put("bpl", new Triplet<String, Integer, Integer>("rbp", 0, 8));
		REG_INFO_DICT.put("esp", new Triplet<String, Integer, Integer>("rsp", 0, 32));
		REG_INFO_DICT.put("sp", new Triplet<String, Integer, Integer>("rsp", 0, 16));
		REG_INFO_DICT.put("spl", new Triplet<String, Integer, Integer>("rsp", 0, 8));
		REG_INFO_DICT.put("r8d", new Triplet<String, Integer, Integer>("r8", 0, 32));
		REG_INFO_DICT.put("r8w", new Triplet<String, Integer, Integer>("r8", 0, 16));
		REG_INFO_DICT.put("r8b", new Triplet<String, Integer, Integer>("r8", 0, 8));
		REG_INFO_DICT.put("r9d", new Triplet<String, Integer, Integer>("r9", 0, 32));
		REG_INFO_DICT.put("r9w", new Triplet<String, Integer, Integer>("r9", 0, 16));
		REG_INFO_DICT.put("r9b", new Triplet<String, Integer, Integer>("r9", 0, 8));
		REG_INFO_DICT.put("r10d", new Triplet<String, Integer, Integer>("r10", 0, 32));
		REG_INFO_DICT.put("r10w", new Triplet<String, Integer, Integer>("r10", 0, 16));
		REG_INFO_DICT.put("r10b", new Triplet<String, Integer, Integer>("r10", 0, 8));
		REG_INFO_DICT.put("r11d", new Triplet<String, Integer, Integer>("r11", 0, 32));
		REG_INFO_DICT.put("r11w", new Triplet<String, Integer, Integer>("r11", 0, 16));
		REG_INFO_DICT.put("r11b", new Triplet<String, Integer, Integer>("r11", 0, 8));
		REG_INFO_DICT.put("r12d", new Triplet<String, Integer, Integer>("r12", 0, 32));
		REG_INFO_DICT.put("r12w", new Triplet<String, Integer, Integer>("r12", 0, 16));
		REG_INFO_DICT.put("r12b", new Triplet<String, Integer, Integer>("r12", 0, 8));
		REG_INFO_DICT.put("r13d", new Triplet<String, Integer, Integer>("r13", 0, 32));
		REG_INFO_DICT.put("r13w", new Triplet<String, Integer, Integer>("r13", 0, 16));
		REG_INFO_DICT.put("r13b", new Triplet<String, Integer, Integer>("r13", 0, 8));
		REG_INFO_DICT.put("r14d", new Triplet<String, Integer, Integer>("r14", 0, 32));
		REG_INFO_DICT.put("r14w", new Triplet<String, Integer, Integer>("r14", 0, 16));
		REG_INFO_DICT.put("r14b", new Triplet<String, Integer, Integer>("r14", 0, 8));
		REG_INFO_DICT.put("r15d", new Triplet<String, Integer, Integer>("r15", 0, 32));
		REG_INFO_DICT.put("r15w", new Triplet<String, Integer, Integer>("r15", 0, 16));
		REG_INFO_DICT.put("r15b", new Triplet<String, Integer, Integer>("r15", 0, 8));
		
		AUX_REG_INFO = new HashMap<Integer, Triplet<String, String, String>>();
		AUX_REG_INFO.put(8, new Triplet<String, String, String>("al", "ah", "ax"));
		AUX_REG_INFO.put(16, new Triplet<String, String, String>("ax", "dx", "dx:ax"));
		AUX_REG_INFO.put(32, new Triplet<String, String, String>("eax", "edx", "edx:eax"));
		AUX_REG_INFO.put(64, new Triplet<String, String, String>("rax", "rdx", "rdx:rax"));
		
		REG64_NAMES = new HashSet<String>(Arrays.asList(REG64_NAME_LIST));
		
		REG_NAMES = new HashSet<String>(REG64_NAMES);
		REG_NAMES.addAll(REG_INFO_DICT.keySet());
		
		CONDITIONAL_JMP_INST = new HashSet<String>();
		Set<String> f_conds = FLAG_CONDITIONS.keySet();
		for(String x : f_conds) {
			CONDITIONAL_JMP_INST.add("j" + x);
		}
				
		JMP_INST = new HashSet<String>(CONDITIONAL_JMP_INST);
		JMP_INST.add("jmp");
		JMP_INST.add("call");
		JMP_INST.add("ret");
		
		JMP_INST_WITHOUT_CALL = new HashSet<String>(CONDITIONAL_JMP_INST);
		JMP_INST_WITHOUT_CALL.add("jmp");
		JMP_INST_WITHOUT_CALL.add("ret");
		
		JMP_INST_WITH_ADDRESS = new HashSet<String>(CONDITIONAL_JMP_INST);
		JMP_INST_WITH_ADDRESS.add("jmp");
		JMP_INST_WITH_ADDRESS.add("call");
		
		CONDITIONAL_MOV_INST = new HashSet<String>();
		for(String x : f_conds) {
			CONDITIONAL_MOV_INST.add("cmov" + x);
		}
		
		CONDITIONAL_SET_INST = new HashSet<String>();
		for(String x : f_conds) {
			CONDITIONAL_SET_INST.add("set" + x);
		}
		
		TERMINATION_FUNCTIONS = new String[] {
			    "__stack_chk_fail",
			    "__overflow",
			    "err",
			    "error",
			    "error_at_line",
			    "errx",
			    "exit",
			    "_exit",
			    "abort",
			    "raise",
			    "__assert_fail",
			    "g_assertion_message_expr",
			    "g_assertion_message",
			    "g_abort",
			    "obstack_alloc_failed_handler",
			    "pthread_exit"
			};
		
		String[] general_insts_arr = new String[] {
				"mov", "lea", "push", "pop", "add", "sub", "xor",
			    "and", "or", "sar", "shr", "sal", "shl", "xchg",
			    "neg", "not", "test", "cmp", "imul", "mul", "idiv", "div",
			    "cmpxchg", "movzx", "movsx", "movsxd", "leave", "inc", "dec", "adc", "sbb",
			    "cbw", "cwde", "cdqe", "cwd", "cdq", "cqo", "ror", "rol", "nop", "hlt"
		};
		GENERAL_INSTRUCTIONS = new HashSet<String>(Arrays.asList(general_insts_arr));
		
		String[] insts_aff_flags_wo_cmp_test_arr =  new String[] {
				"add", "sub", "xor", "and", "or", "sar", "shr", "sal", "shl",
			    "neg", "not", "imul", "mul", "inc", "dec", "adc", "sbb", "ror", "rol"
		};
		INSTS_AFF_FLAGS_WO_CMP_TEST = new HashSet<String>(Arrays.asList(insts_aff_flags_wo_cmp_test_arr));
	}
}
