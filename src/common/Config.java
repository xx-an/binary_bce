package common;

import java.util.HashMap;

public class Config {
	public static int MEM_ADDR_SIZE = 64;
	
	public static final int MAX_LOOP_COUNT = 5;
	public static final int MAX_VISIT_COUNT = 25;

	public static final int MAX_TRACEBACK_COUNT = 15;
	public static final int MAX_INST_ADDR_GAP = 25;
	
	public static final HashMap<Integer, String> ADDR_SIZE_SP_MAP;
	public static final HashMap<Integer, Long> INIT_STACK_FRAME_POINTER;
	
	public static final HashMap<Integer, Integer> HEAP_ADDR_INFO;
	
	static {
		ADDR_SIZE_SP_MAP = new HashMap<>();
		ADDR_SIZE_SP_MAP.put(16, "sp");
		ADDR_SIZE_SP_MAP.put(32, "esp");
		ADDR_SIZE_SP_MAP.put(64, "esp");
		
		INIT_STACK_FRAME_POINTER = new HashMap<Integer, Long>();
		INIT_STACK_FRAME_POINTER.put(16, (long) (2^12-3));
		INIT_STACK_FRAME_POINTER.put(32, (long) (2^24-5));
		INIT_STACK_FRAME_POINTER.put(64, (long) (2^48-9));
		
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
