package common;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Set;
import java.util.HashSet;
import java.util.List;

public class Lib {
	public static final HashMap<String, String> FLAG_CONDITIONS;
	public static final HashMap<String, Tuple<Integer, Integer>> REG_INFO_DICT;
	public static final HashMap<Integer, Triplet<String, String, String>> AUX_REG_INFO;
	public static final List<String> TERMINATION_FUNCTIONS;
	
	public static final List<String> REG64_NAME_LIST = Arrays.asList(new String[] {
			"rax", "rbx", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15", "rsp", "rbp"});
	
	public static final HashSet<String> REG64_NAMES;
	public static final HashSet<String> REG_NAMES;
	
	public static final HashSet<String> CONDITIONAL_JMP_INST;
	public static final HashSet<String> JMP_INST;
	public static final HashSet<String> JMP_INST_WITHOUT_CALL;
	public static final HashSet<String> JMP_INST_WITH_ADDRESS;
	public static final HashSet<String> JMP_INST_WITH_JUMP;

	public static final HashMap<Integer, List<String>> CALLEE_NOT_SAVED_REGS;
	
	public static final String[] RFlags = new String[] {"CF", "ZF", "OF", "SF"};
	public static final HashSet<String> SEG_REGS = new HashSet<>(Arrays.asList("ss", "cs", "ds", "es", "fs", "gs"));
	
	public static String[] CODE_SECTIONS = new String[] {".plt.got", ".plt", ".text"};
	public static String[] DATA_SECTIONS = new String[] {".rodata", ".idata", ".data", ".bss", ".got", ".eh_frame", ".eh_frame_hdr"};
	public static String[] RODATA_SECTIONS = new String[] {".plt.got", ".plt", ".text", ".rodata", ".idata", ".got", ".eh_frame", ".eh_frame_hdr"};
	public static HashSet<String> RWDATA_SECTIONS = new HashSet<>(Arrays.asList(".data", ".bss"));
	
	public static String[] SECTIONS = new String[] {".plt.got", ".plt", ".text", ".rodata", ".idata", ".data", ".bss", ".got", "extern", ".eh_frame", ".eh_frame_hdr"};
	
	
	public static final String TEXTSEC = ".text";
	public static final String DATASEC = ".data";
	public static final String RODATASEC = ".idata";
	
	public static final String EXECUTABLE = "Executable";
	public static final String RELOCATABLE = "Relocatable";
			
			
	public static final HashSet<String> GENERAL_INSTRUCTIONS;
	public static final HashSet<String> INSTS_AFF_FLAGS_WO_CMP_TEST;
	
	public static final String REG = "register";
	public static final String MEM = "memory";
	public static final String FLAGS = "flags";
	public static final String FS = "fs";
	public static final String CS = "cs";
	public static final String GS = "gs";
	public static final String DS = "ds";
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
	public static final Set<String> SEG_STATE_NAMES = Set.of(FS, CS, GS, DS);
	
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
	    BUFFER_OVERFLOW,
	    UNINITIALIZED_CONTENT
	}


	public static enum TRACE_BACK_TYPE {
	    INDIRECT,
	    SYMBOLIC,
	}


	public static enum TRACE_BACK_RET_TYPE {
	    JT_UNRESOLVED,
	    JT_SUCCEED,
	    JT_NO_UPPERBOUND,
	    JT_NOT_CORRECT_ASSIGN_INST,
	    JT_NO_CORRECT_JMP_INST,
	    JT_UPPERBOUND_DISMATCH,
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
		FLAG_CONDITIONS.put("a",  "CF==0 && ZF==0");
		FLAG_CONDITIONS.put("ae",  "CF==0");
		FLAG_CONDITIONS.put("b",  "CF==1");
		FLAG_CONDITIONS.put("be",  "CF==1 || ZF==1");
		FLAG_CONDITIONS.put("c",  "CF==1");
		FLAG_CONDITIONS.put("e",  "ZF==1");
		FLAG_CONDITIONS.put("g",  "ZF==0 && SF==OF");
		FLAG_CONDITIONS.put("ge",  "SF==OF");
		FLAG_CONDITIONS.put("l",  "SF<>OF");
		FLAG_CONDITIONS.put("le",  "ZF==1 || SF<>OF");
		FLAG_CONDITIONS.put("na",  "CF==1 || ZF==1");
		FLAG_CONDITIONS.put("nae",  "CF==1");
		FLAG_CONDITIONS.put("nb",  "CF==0");
		FLAG_CONDITIONS.put("nbe",  "CF==0 && ZF==0");
		FLAG_CONDITIONS.put("nc",  "CF==0");
		FLAG_CONDITIONS.put("ne",  "ZF==0");
		FLAG_CONDITIONS.put("ng",  "ZF==1 || SF<>OF");
		FLAG_CONDITIONS.put("nge",  "SF<>OF");
		FLAG_CONDITIONS.put("nl",  "SF==OF");
		FLAG_CONDITIONS.put("nle",  "ZF==0 && SF==OF");
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
		
		
		REG_INFO_DICT = new HashMap<String, Tuple<Integer, Integer>>();
		REG_INFO_DICT.put("eax", new Tuple<Integer, Integer>(0, 32));
		REG_INFO_DICT.put("ax", new Tuple<Integer, Integer>(0, 16));
		REG_INFO_DICT.put("ah", new Tuple<Integer, Integer>(8, 8));
		REG_INFO_DICT.put("al", new Tuple<Integer, Integer>(0, 8));
		REG_INFO_DICT.put("ebx", new Tuple<Integer, Integer>(0, 32));
		REG_INFO_DICT.put("bx", new Tuple<Integer, Integer>(0, 16));
		REG_INFO_DICT.put("bh", new Tuple<Integer, Integer>(8, 8));
		REG_INFO_DICT.put("bl", new Tuple<Integer, Integer>(0, 8));
		REG_INFO_DICT.put("ecx", new Tuple<Integer, Integer>(0, 32));
		REG_INFO_DICT.put("cx", new Tuple<Integer, Integer>(0, 16));
		REG_INFO_DICT.put("ch", new Tuple<Integer, Integer>(8, 8));
		REG_INFO_DICT.put("cl", new Tuple<Integer, Integer>(0, 8));
		REG_INFO_DICT.put("edx", new Tuple<Integer, Integer>(0, 32));
		REG_INFO_DICT.put("dx", new Tuple<Integer, Integer>(0, 16));
		REG_INFO_DICT.put("dh", new Tuple<Integer, Integer>(8, 8));
		REG_INFO_DICT.put("dl", new Tuple<Integer, Integer>(0, 8));
		REG_INFO_DICT.put("esi", new Tuple<Integer, Integer>(0, 32));
		REG_INFO_DICT.put("si", new Tuple<Integer, Integer>(0, 16));
		REG_INFO_DICT.put("sil", new Tuple<Integer, Integer>(0, 8));
		REG_INFO_DICT.put("edi", new Tuple<Integer, Integer>(0, 32));
		REG_INFO_DICT.put("di", new Tuple<Integer, Integer>(0, 16));
		REG_INFO_DICT.put("dil", new Tuple<Integer, Integer>(0, 8));
		REG_INFO_DICT.put("ebp", new Tuple<Integer, Integer>(0, 32));
		REG_INFO_DICT.put("bp", new Tuple<Integer, Integer>(0, 16));
		REG_INFO_DICT.put("bpl", new Tuple<Integer, Integer>(0, 8));
		REG_INFO_DICT.put("esp", new Tuple<Integer, Integer>(0, 32));
		REG_INFO_DICT.put("sp", new Tuple<Integer, Integer>(0, 16));
		REG_INFO_DICT.put("spl", new Tuple<Integer, Integer>(0, 8));
		REG_INFO_DICT.put("r8d", new Tuple<Integer, Integer>(0, 32));
		REG_INFO_DICT.put("r8w", new Tuple<Integer, Integer>(0, 16));
		REG_INFO_DICT.put("r8b", new Tuple<Integer, Integer>(0, 8));
		REG_INFO_DICT.put("r9d", new Tuple<Integer, Integer>(0, 32));
		REG_INFO_DICT.put("r9w", new Tuple<Integer, Integer>(0, 16));
		REG_INFO_DICT.put("r9b", new Tuple<Integer, Integer>(0, 8));
		REG_INFO_DICT.put("r10d", new Tuple<Integer, Integer>(0, 32));
		REG_INFO_DICT.put("r10w", new Tuple<Integer, Integer>(0, 16));
		REG_INFO_DICT.put("r10b", new Tuple<Integer, Integer>(0, 8));
		REG_INFO_DICT.put("r11d", new Tuple<Integer, Integer>(0, 32));
		REG_INFO_DICT.put("r11w", new Tuple<Integer, Integer>(0, 16));
		REG_INFO_DICT.put("r11b", new Tuple<Integer, Integer>(0, 8));
		REG_INFO_DICT.put("r12d", new Tuple<Integer, Integer>(0, 32));
		REG_INFO_DICT.put("r12w", new Tuple<Integer, Integer>(0, 16));
		REG_INFO_DICT.put("r12b", new Tuple<Integer, Integer>(0, 8));
		REG_INFO_DICT.put("r13d", new Tuple<Integer, Integer>(0, 32));
		REG_INFO_DICT.put("r13w", new Tuple<Integer, Integer>(0, 16));
		REG_INFO_DICT.put("r13b", new Tuple<Integer, Integer>(0, 8));
		REG_INFO_DICT.put("r14d", new Tuple<Integer, Integer>(0, 32));
		REG_INFO_DICT.put("r14w", new Tuple<Integer, Integer>(0, 16));
		REG_INFO_DICT.put("r14b", new Tuple<Integer, Integer>(0, 8));
		REG_INFO_DICT.put("r15d", new Tuple<Integer, Integer>(0, 32));
		REG_INFO_DICT.put("r15w", new Tuple<Integer, Integer>(0, 16));
		REG_INFO_DICT.put("r15b", new Tuple<Integer, Integer>(0, 8));
		
		AUX_REG_INFO = new HashMap<Integer, Triplet<String, String, String>>();
		AUX_REG_INFO.put(8, new Triplet<String, String, String>("al", "ah", "ax"));
		AUX_REG_INFO.put(16, new Triplet<String, String, String>("ax", "dx", "dx:ax"));
		AUX_REG_INFO.put(32, new Triplet<String, String, String>("eax", "edx", "edx:eax"));
		AUX_REG_INFO.put(64, new Triplet<String, String, String>("rax", "rdx", "rdx:rax"));
		
		REG64_NAMES = new HashSet<String>(REG64_NAME_LIST);
		
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
		
		JMP_INST_WITH_JUMP = new HashSet<String>(CONDITIONAL_JMP_INST);
		JMP_INST_WITH_JUMP.add("jmp");
		
		CONDITIONAL_MOV_INST = new HashSet<String>();
		for(String x : f_conds) {
			CONDITIONAL_MOV_INST.add("cmov" + x);
		}
		
		CONDITIONAL_SET_INST = new HashSet<String>();
		for(String x : f_conds) {
			CONDITIONAL_SET_INST.add("set" + x);
		}
		
		CALLEE_NOT_SAVED_REGS = new HashMap<>();
		CALLEE_NOT_SAVED_REGS.put(64, Arrays.asList("rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11"));
		CALLEE_NOT_SAVED_REGS.put(32, Arrays.asList("eax", "ecx", "edx", "esi", "edi"));
		
		
		String[] t_functions = {
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
//			    "__imp_exit"
			};
		TERMINATION_FUNCTIONS = Arrays.asList(t_functions);
		
		
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
