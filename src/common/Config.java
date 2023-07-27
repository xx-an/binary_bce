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
	
	public static String SP_NAME;
	public static List<String> INIT_REGS_NAMES;
	public static long INIT_STACK_FRAME_POINTER;
	
	public static HashMap<String, String> REGS_PARENT_MAP = new HashMap<>();
	public static List<String> CALLEE_NOT_SAVED_REGS;
	
	public static final int MAX_MALLOC_SIZE = 1671;
	
	public static long INIT_HEAP_ADDR;
	public static long MAX_HEAP_ADDR;
	
	public static final int CMC_EXEC_RES_COUNT = 8;
	
	public static final int MAX_ARGC_NUM = 10;
	public static final int REBUILD_BRANCHES_NUM = 2;
	
	public static final String LOG_UNREACHABLE_INDICATOR = "Unreachable instructions:";
	
	public static void initConfig() {
		if(MEM_ADDR_SIZE == 16) {
			SP_NAME = "sp";
			INIT_REGS_NAMES = Arrays.asList(new String[] {
					"ax", "bx", "cx", "dx", "si", "di", "sp", "bp"});
			INIT_STACK_FRAME_POINTER = (long) Math.pow(2, 12) - 3;
			INIT_HEAP_ADDR = 0x4ff;
		}
		else if(MEM_ADDR_SIZE == 32) {
			SP_NAME = "esp";
			INIT_REGS_NAMES = Arrays.asList(new String[] {
					"eax", "ebx", "ecx", "edx", "esi", "edi", "esp", "ebp"});
			INIT_STACK_FRAME_POINTER = (long) Math.pow(2, 24) - 5;
			INIT_HEAP_ADDR = 0x8fffff;
			
			REGS_PARENT_MAP.put("eax", "eax");
			REGS_PARENT_MAP.put("ax", "eax");
			REGS_PARENT_MAP.put("ah", "eax");
			REGS_PARENT_MAP.put("al", "eax");
			REGS_PARENT_MAP.put("ebx", "ebx");
			REGS_PARENT_MAP.put("bx", "ebx");
			REGS_PARENT_MAP.put("bh", "ebx");
			REGS_PARENT_MAP.put("bl", "ebx");
			REGS_PARENT_MAP.put("ecx", "ecx");
			REGS_PARENT_MAP.put("cx", "ecx");
			REGS_PARENT_MAP.put("ch", "ecx");
			REGS_PARENT_MAP.put("cl", "ecx");
			REGS_PARENT_MAP.put("edx", "edx");
			REGS_PARENT_MAP.put("dx", "edx");
			REGS_PARENT_MAP.put("dh", "edx");
			REGS_PARENT_MAP.put("dl", "edx");
			REGS_PARENT_MAP.put("esi", "esi");
			REGS_PARENT_MAP.put("si", "esi");
			REGS_PARENT_MAP.put("sil", "esi");
			REGS_PARENT_MAP.put("edi", "edi");
			REGS_PARENT_MAP.put("di", "edi");
			REGS_PARENT_MAP.put("dil", "edi");
			REGS_PARENT_MAP.put("ebp", "ebp");
			REGS_PARENT_MAP.put("bp", "ebp");
			REGS_PARENT_MAP.put("bpl", "ebp");
			REGS_PARENT_MAP.put("esp", "esp");
			REGS_PARENT_MAP.put("sp", "esp");
			REGS_PARENT_MAP.put("spl", "esp");
			
			CALLEE_NOT_SAVED_REGS = Arrays.asList("eax", "ecx", "edx", "esi", "edi");

		}
		else if(MEM_ADDR_SIZE == 64) {
			SP_NAME = "rsp";
			INIT_REGS_NAMES = Lib.REG64_NAME_LIST;
			INIT_STACK_FRAME_POINTER = (long) Math.pow(2, 48) - 9;
			INIT_HEAP_ADDR = 0x10000000;
			
			REGS_PARENT_MAP.put("eax", "rax");
			REGS_PARENT_MAP.put("ax", "rax");
			REGS_PARENT_MAP.put("ah", "rax");
			REGS_PARENT_MAP.put("al", "rax");
			REGS_PARENT_MAP.put("ebx", "rbx");
			REGS_PARENT_MAP.put("bx", "rbx");
			REGS_PARENT_MAP.put("bh", "rbx");
			REGS_PARENT_MAP.put("bl", "rbx");
			REGS_PARENT_MAP.put("ecx", "rcx");
			REGS_PARENT_MAP.put("cx", "rcx");
			REGS_PARENT_MAP.put("ch", "rcx");
			REGS_PARENT_MAP.put("cl", "rcx");
			REGS_PARENT_MAP.put("edx", "rdx");
			REGS_PARENT_MAP.put("dx", "rdx");
			REGS_PARENT_MAP.put("dh", "rdx");
			REGS_PARENT_MAP.put("dl", "rdx");
			REGS_PARENT_MAP.put("esi", "rsi");
			REGS_PARENT_MAP.put("si", "rsi");
			REGS_PARENT_MAP.put("sil", "rsi");
			REGS_PARENT_MAP.put("edi", "rdi");
			REGS_PARENT_MAP.put("di", "rdi");
			REGS_PARENT_MAP.put("dil", "rdi");
			REGS_PARENT_MAP.put("ebp", "rbp");
			REGS_PARENT_MAP.put("bp", "rbp");
			REGS_PARENT_MAP.put("bpl", "rbp");
			REGS_PARENT_MAP.put("esp", "rsp");
			REGS_PARENT_MAP.put("sp", "rsp");
			REGS_PARENT_MAP.put("spl", "rsp");
			REGS_PARENT_MAP.put("r8d", "r8");
			REGS_PARENT_MAP.put("r8w", "r8");
			REGS_PARENT_MAP.put("r8b", "r8");
			REGS_PARENT_MAP.put("r9d", "r9");
			REGS_PARENT_MAP.put("r9w", "r9");
			REGS_PARENT_MAP.put("r9b", "r9");
			REGS_PARENT_MAP.put("r10d", "r10");
			REGS_PARENT_MAP.put("r10w", "r10");
			REGS_PARENT_MAP.put("r10b", "r10");
			REGS_PARENT_MAP.put("r11d", "r11");
			REGS_PARENT_MAP.put("r11w", "r11");
			REGS_PARENT_MAP.put("r11b", "r11");
			REGS_PARENT_MAP.put("r12d", "r12");
			REGS_PARENT_MAP.put("r12w", "r12");
			REGS_PARENT_MAP.put("r12b", "r12");
			REGS_PARENT_MAP.put("r13d", "r13");
			REGS_PARENT_MAP.put("r13w", "r13");
			REGS_PARENT_MAP.put("r13b", "r13");
			REGS_PARENT_MAP.put("r14d", "r14");
			REGS_PARENT_MAP.put("r14w", "r14");
			REGS_PARENT_MAP.put("r14b", "r14");
			REGS_PARENT_MAP.put("r15d", "r15");
			REGS_PARENT_MAP.put("r15w", "r15");
			REGS_PARENT_MAP.put("r15b", "r15");
			
			CALLEE_NOT_SAVED_REGS = Arrays.asList("rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11");
			
		}
		MAX_HEAP_ADDR = INIT_HEAP_ADDR;
	}
	
}
