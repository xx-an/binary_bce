package common;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;

public class Config {
	public static int MEM_ADDR_SIZE = 32;
	
	public static final int MAX_CYCLE_COUNT = 5;
	public static final int MAX_VISIT_COUNT = 25;

	public static final int MAX_TRACEBACK_COUNT = 15;
	public static final int MAX_INST_ADDR_GAP = 25;
	
	public static final HashMap<Integer, String> ADDR_SIZE_SP_MAP;
	public static final HashMap<Integer, Long> INIT_STACK_FRAME_POINTER;
	
	public static final HashMap<Integer, List<String>> ADDR_SIZE_REGS_MAP;
	public static final HashMap<String, String> REGS_PARENT64_MAP;
	public static final HashMap<String, String> REGS_PARENT32_MAP;
	
	
	public static final HashMap<Integer, Integer> HEAP_ADDR_INFO;
	
	static {
		ADDR_SIZE_SP_MAP = new HashMap<>();
		ADDR_SIZE_SP_MAP.put(16, "sp");
		ADDR_SIZE_SP_MAP.put(32, "esp");
		ADDR_SIZE_SP_MAP.put(64, "esp");
		
		ADDR_SIZE_REGS_MAP = new HashMap<Integer, List<String>>();
		ADDR_SIZE_REGS_MAP.put(64, Lib.REG64_NAME_LIST);
		ADDR_SIZE_REGS_MAP.put(32, Arrays.asList(new String[] {
				"eax", "ebx", "ecx", "edx", "esi", "edi", "esp", "ebp"}));
		ADDR_SIZE_REGS_MAP.put(16, Arrays.asList(new String[] {
				"ax", "bx", "cx", "dx", "si", "di", "sp", "bp"}));
		
		
		REGS_PARENT64_MAP = new HashMap<>();
		REGS_PARENT64_MAP.put("eax", "rax");
		REGS_PARENT64_MAP.put("ax", "rax");
		REGS_PARENT64_MAP.put("ah", "rax");
		REGS_PARENT64_MAP.put("al", "rax");
		REGS_PARENT64_MAP.put("ebx", "rbx");
		REGS_PARENT64_MAP.put("bx", "rbx");
		REGS_PARENT64_MAP.put("bh", "rbx");
		REGS_PARENT64_MAP.put("bl", "rbx");
		REGS_PARENT64_MAP.put("ecx", "rcx");
		REGS_PARENT64_MAP.put("cx", "rcx");
		REGS_PARENT64_MAP.put("ch", "rcx");
		REGS_PARENT64_MAP.put("cl", "rcx");
		REGS_PARENT64_MAP.put("edx", "rdx");
		REGS_PARENT64_MAP.put("dx", "rdx");
		REGS_PARENT64_MAP.put("dh", "rdx");
		REGS_PARENT64_MAP.put("dl", "rdx");
		REGS_PARENT64_MAP.put("esi", "rsi");
		REGS_PARENT64_MAP.put("si", "rsi");
		REGS_PARENT64_MAP.put("sil", "rsi");
		REGS_PARENT64_MAP.put("edi", "rdi");
		REGS_PARENT64_MAP.put("di", "rdi");
		REGS_PARENT64_MAP.put("dil", "rdi");
		REGS_PARENT64_MAP.put("ebp", "rbp");
		REGS_PARENT64_MAP.put("bp", "rbp");
		REGS_PARENT64_MAP.put("bpl", "rbp");
		REGS_PARENT64_MAP.put("esp", "rsp");
		REGS_PARENT64_MAP.put("sp", "rsp");
		REGS_PARENT64_MAP.put("spl", "rsp");
		REGS_PARENT64_MAP.put("r8d", "r8");
		REGS_PARENT64_MAP.put("r8w", "r8");
		REGS_PARENT64_MAP.put("r8b", "r8");
		REGS_PARENT64_MAP.put("r9d", "r9");
		REGS_PARENT64_MAP.put("r9w", "r9");
		REGS_PARENT64_MAP.put("r9b", "r9");
		REGS_PARENT64_MAP.put("r10d", "r10");
		REGS_PARENT64_MAP.put("r10w", "r10");
		REGS_PARENT64_MAP.put("r10b", "r10");
		REGS_PARENT64_MAP.put("r11d", "r11");
		REGS_PARENT64_MAP.put("r11w", "r11");
		REGS_PARENT64_MAP.put("r11b", "r11");
		REGS_PARENT64_MAP.put("r12d", "r12");
		REGS_PARENT64_MAP.put("r12w", "r12");
		REGS_PARENT64_MAP.put("r12b", "r12");
		REGS_PARENT64_MAP.put("r13d", "r13");
		REGS_PARENT64_MAP.put("r13w", "r13");
		REGS_PARENT64_MAP.put("r13b", "r13");
		REGS_PARENT64_MAP.put("r14d", "r14");
		REGS_PARENT64_MAP.put("r14w", "r14");
		REGS_PARENT64_MAP.put("r14b", "r14");
		REGS_PARENT64_MAP.put("r15d", "r15");
		REGS_PARENT64_MAP.put("r15w", "r15");
		REGS_PARENT64_MAP.put("r15b", "r15");
		
		REGS_PARENT32_MAP = new HashMap<>();
		REGS_PARENT32_MAP.put("eax", "eax");
		REGS_PARENT32_MAP.put("ax", "eax");
		REGS_PARENT32_MAP.put("ah", "eax");
		REGS_PARENT32_MAP.put("al", "eax");
		REGS_PARENT32_MAP.put("ebx", "ebx");
		REGS_PARENT32_MAP.put("bx", "ebx");
		REGS_PARENT32_MAP.put("bh", "ebx");
		REGS_PARENT32_MAP.put("bl", "ebx");
		REGS_PARENT32_MAP.put("ecx", "ecx");
		REGS_PARENT32_MAP.put("cx", "ecx");
		REGS_PARENT32_MAP.put("ch", "ecx");
		REGS_PARENT32_MAP.put("cl", "ecx");
		REGS_PARENT32_MAP.put("edx", "edx");
		REGS_PARENT32_MAP.put("dx", "edx");
		REGS_PARENT32_MAP.put("dh", "edx");
		REGS_PARENT32_MAP.put("dl", "edx");
		REGS_PARENT32_MAP.put("esi", "esi");
		REGS_PARENT32_MAP.put("si", "esi");
		REGS_PARENT32_MAP.put("sil", "esi");
		REGS_PARENT32_MAP.put("edi", "edi");
		REGS_PARENT32_MAP.put("di", "edi");
		REGS_PARENT32_MAP.put("dil", "edi");
		REGS_PARENT32_MAP.put("ebp", "ebp");
		REGS_PARENT32_MAP.put("bp", "ebp");
		REGS_PARENT32_MAP.put("bpl", "ebp");
		REGS_PARENT32_MAP.put("esp", "esp");
		REGS_PARENT32_MAP.put("sp", "esp");
		REGS_PARENT32_MAP.put("spl", "esp");
		
		
		INIT_STACK_FRAME_POINTER = new HashMap<Integer, Long>();
		INIT_STACK_FRAME_POINTER.put(16, (long) Math.pow(2, 12) - 3);
		INIT_STACK_FRAME_POINTER.put(32, (long) Math.pow(2, 24) - 5);
		INIT_STACK_FRAME_POINTER.put(64, (long) Math.pow(2, 48) - 9);
		
		HEAP_ADDR_INFO = new HashMap<Integer, Integer>();
		HEAP_ADDR_INFO.put(16, 0x4ff);
		HEAP_ADDR_INFO.put(32, 0x8fffff);
		HEAP_ADDR_INFO.put(64, 0x10000000);
    }

	public static final Long MIN_STACK_FRAME_POINTER = INIT_STACK_FRAME_POINTER.get(MEM_ADDR_SIZE);

//	public static final int MAX_MALLOC_SIZE = 16711568;
	public static final int MAX_MALLOC_SIZE = 1671;
	public static final long MIN_HEAP_ADDR = HEAP_ADDR_INFO.get(MEM_ADDR_SIZE);
	public static long MAX_HEAP_ADDR = MIN_HEAP_ADDR;

//	public static final long INIT_STACK_FRAME_POINTER = 2^48-9;
	public static final int MAX_DEVIATION = 5;
	public static final int SEGMENT_REG_INIT_VAL = 0;
	
	
	public static final int CMC_EXEC_RES_COUNT = 8;

	public static final int MAX_ARGC_NUM = 10;
	public static final int REBUILD_BRANCHES_NUM = 2;
	
	public static final String LOG_UNREACHABLE_INDICATOR = "Unreachable instructions:";
}
