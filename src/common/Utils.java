package common;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Stack;
import java.util.function.Function;
import java.util.logging.FileHandler;
import java.util.logging.Formatter;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import javax.script.ScriptEngine;
import javax.script.ScriptEngineManager;
import javax.script.ScriptException;

public class Utils {
	
	public static final List<String> UNVISITED_SECTION_LABELS = List.of("_init", "_fini", "__Libc_csu_init", "__Libc_csu_fini", "frame_dummy", "register_tm_clones", "deregister_tm_clones", "__do_global_dtors_aux");
	
	public static final Path PROJECT_DIR = Paths.get("").toAbsolutePath().getParent();
	
	public static final String LOG_NAMES[] = new String[]{"log", "output"};
	
	public static final Map<String, String> delimits = Map.of("(",")", "[", "]", "{", "}");
	
	public static final Pattern float_pat = Pattern.compile("^[0-9.]+$|^-[0-9.]+$");
	public static final Pattern imm_pat = Pattern.compile("^0x[0-9a-fA-F]+$|^[0-9]+$|^-[0-9]+$|^-0x[0-9a-fA-F]+$");
	public static final Pattern imm_start_pat = Pattern.compile("^0x[0-9a-fA-F]+|^[0-9]+|^-[0-9]+|^-0x[0-9a-fA-F]+");
	public static final Pattern imm_pat_wo_prefix = Pattern.compile("^[0-9a-fA-F]+$|^-[0-9a-fA-F]+$");
	
	public static int MAX_LOOP_COUNT = 5;
	public static int MAX_VISIT_COUNT = 25;
	public static int INIT_BLOCK_NO = -1;
	public static int TB_DEFAULT_BLOCK_NO = -2;
	public final static int WINCHECK_EXEC_RES_COUNT = 4;
	
	public static final String MEM_DATA_SEC_SUFFIX = "mem@";   
	public static final String LOG_UNREACHABLE_INDICATOR = "Unreachable instructions:";
	public static final String SOUNDNESS_EXCEPTION_INDICATOR = "ambiguous operand size";
			
	public static final String ASSEMBLY_FILE_NAME = "test.s";
	public static final String PREDEFINED_CONSTRAINT_FILE = "ext_env.config";
	
	public static int MAX_TRACEBACK_COUNT = 50;
	public static int MAX_INST_ADDR_GAP = 25;
	
	public static int MAX_ARGC_NUM = 10;
	public static int REBUILD_BRANCHES_NUM = 2;

	public static final Map<String, String> OPPOSITE_FLAG_MAP = Map.of("b", "ae", "be", "a", "l", "ge", "le", "g");

	public static Function<String, String> id_op;
	
//	HashMap<Integer, String> ADDR_SIZE_SP_MAP = (HashMap<Integer, String>) Map.of(16, "sp", 32, "esp", 64, "rsp");
//	
//	HashMap<Integer, Long> INIT_STACK_FRAME_POINTER = (HashMap<Integer, Long>) Map.of(16, (long) 2^12-3, 32, (long) 2^24-5, 64, (long) 2^48-9);
	
	static ScriptEngineManager engine_manager = new ScriptEngineManager();
	static ScriptEngine script_engine = engine_manager.getEngineByName("js");
	
	public static Logger logger = Logger.getLogger(LOG_NAMES[0]);
	public static Logger output_logger = Logger.getLogger(LOG_NAMES[1]);
	
	public static void setup_logger(String logName, String log_path, Level level) throws SecurityException, IOException {
		Handler fh = new FileHandler(log_path);
		Formatter fmt = new LogFormatter();
		fh.setFormatter(fmt);
        if(logName == LOG_NAMES[0]) {
        	logger.setUseParentHandlers(false);
        	logger.addHandler(fh);
            logger.setLevel(Level.ALL);
            
        }
        else {
        	output_logger.setUseParentHandlers(false);
        	output_logger.addHandler(fh);
        	output_logger.setLevel(Level.ALL);
        }
	}
	
	public static void close_logger(String logName) {
	    if(logName == LOG_NAMES[0]) {
	    	for(Handler handler : logger.getHandlers()) {
	            handler.close();
	            logger.removeHandler(handler);
	    	}
	    }
	    else{
	    	for(Handler handler : output_logger.getHandlers()) {
	            handler.close();
	            output_logger.removeHandler(handler);
	    	}
	    }
	}
	
	        
	public static long imm_str_to_int(String imm_str) {
		long res = 0;
	    Pattern pattern = Pattern.compile("[a-f]+");
	    Matcher matcher = pattern.matcher(imm_str);
	    if(imm_str.startsWith("0x") || imm_str.startsWith("-0x"))
	        res = Long.decode(imm_str);
	    else if(matcher.find()) {
	    	if(imm_str.endsWith("h")) {
	    		String tmp = imm_str.substring(0, imm_str.length() - 1);
	    		res = Long.valueOf(tmp, 16);
	    	}
	    	else {
	    		res = Long.valueOf(imm_str, 16);
	    	}
	    }
	    else 
	        res = Long.parseLong(imm_str, 16);
	    return res;
	}
	
	
	public static String toHexString(long imm) {
		String res = Long.toString(imm, 16);
		if(res.startsWith("-")) {
			res = res.split("-", 2)[1].strip();
			res = "-0x" + res;
		}
		else
			res = "0x" + res;
	    return res;
	}
	
	public static String toHexString(int imm) {
		String res = Integer.toString(imm, 16);
		if(res.startsWith("-")) {
			res = res.split("-", 2)[1].strip();
			res = "-0x" + res;
		}
		else
			res = "0x" + res;
	    return res;
	}
	
	public static boolean startsWith(String arg, String[] prefixes) {
		boolean res = false;
		for(String prefix : prefixes) {
			res = res || (arg.startsWith(prefix));
		}
		return res;
	}
	
	
	public static boolean contains(String arg, String[] regs) {
		boolean res = false;
		for(String reg : regs) {
			res = res || (arg.contains(reg));
		}
		return res;
	}
	

	void make_dir(String path) {
	    File f = new File(path);
	    f.mkdir();
	}
	
	int sign_extend(int value, int bits) {
	    int sign_bit = 1 << (bits - 1);
	    return (value & (sign_bit - 1)) - (value & sign_bit);
	}
	
	
	public static String ppCycle(Stack<Long> cycle) {
		String res = "[" + String.join(", ", cycle.stream().map(i -> Long.toHexString(i)).toList()) + "]";
		// System.out.println(res);
		return res;
    }


	public static String ppCycle(List<Long> cycle) {
		String res = "[" + String.join(", ", cycle.stream().map(i -> Long.toHexString(i)).toList()) + "]";
//		System.out.println(res);
		return res;
    }
	
	
	public static String[] rsplit(String arg, String regex) {
		String[] args = arg.split(regex);
		if(args.length > 1) {
			String[] res = new String[2];
			res[0] = String.join(regex, Arrays.copyOf(args, args.length - 1));
			res[1] = args[args.length - 1];
			return res;
		}
		else
			return args;
	}
	
	public static String extract_content(String expr, String left_delimit) {
	    String right_delimit = delimits.get(left_delimit);
	    String res = expr.split("\\" + left_delimit, 2)[1];
	    right_delimit = "\\" + right_delimit;
	    res = rsplit(res, right_delimit)[0].strip();
	    return res;
	}
	
	
	public static String getFileName(String path) {
		String fileName = null;
		String[] fileNameSplit = rsplit(path, "/")[1].split("\\.");
		if(fileNameSplit.length > 2) {
			fileName = String.join(".", Arrays.copyOf(fileNameSplit, fileNameSplit.length - 1));
		}
		else
			fileName = fileNameSplit[0];
		return fileName;
	}


	//	input: "(123) 45 (678(42) 235) 56 [78 9]", " "
	//	output: ["(123)", "45", "(678(42) 235)", "56", "[78 9]"]
	public static ArrayList<String> split_sep_bks(String data, String sep) {
		char sep_first = sep.charAt(0);
		int sep_len = sep.length();
	    ArrayList<String> result = new ArrayList<String>();
	    ArrayList<Character> left = new ArrayList<>(List.of('(', '[', '{', '<'));
	    ArrayList<Character> right = new ArrayList<>(List.of(')', ']', '}', '>'));
	    StringBuilder sb = new StringBuilder();
	    boolean to_continue = false;
	    int idx = 0;
	    int length = data.length();
	    int bk_len = left.size();
	    int[] bk_count = new int[bk_len];
	    while(idx < length) {
	        char c = data.charAt(idx);
	        if(left.contains(c)) {
	        	int c_idx = left.indexOf(c);
	            bk_count[c_idx] += 1;
	            sb.append(c);
	            to_continue = true;
	            idx += 1;
	        }
	        else if(right.contains(c)) {
	        	int c_idx = right.indexOf(c);
	        	sb.append(c);
	            bk_count[c_idx] -= 1;
	            boolean ans = Arrays.stream(bk_count).allMatch(elem -> elem == 0);
	            if(ans)
	                to_continue = false;
	            idx += 1;
	        }
	        else if(c == sep_first && data.length()-idx >= sep_len && data.substring(idx, idx + sep_len).equals(sep)) {
	        	if(to_continue) {
	        		sb.append(c);
	    	        idx += 1;
	        	}   
	            else {
	                String curr = sb.toString().strip();
	                if(curr != "") {
	                    result.add(curr);
	                }
	                sb.setLength(0);
	                idx += sep_len;
	            }
	        }
	        else {
	        	sb.append(c);
	            idx += 1;
	        }
	    }
	    String curr = sb.toString();
	    result.add(curr.strip());
	    return result;
	}


	public static String execute_command(String command) {
		String res = "";
        try {
            // Create ProcessBuilder
			ProcessBuilder processBuilder = new ProcessBuilder("/bin/sh", "-c", command);
			
            // Redirect error stream to output stream
            processBuilder.redirectErrorStream(true);

            // Start the process
            Process process = processBuilder.start();

            // Read the output of the command
            try (InputStream inputStream = process.getInputStream();
                 Scanner scanner = new Scanner(inputStream)) {

                while (scanner.hasNextLine()) {
					String tmp = scanner.nextLine();
					res += tmp + "\n";
                    // System.out.println(tmp);
                }
            }

            process.waitFor();

        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
        }
		return res;
    }

	
	public static String bytes_to_hex(ArrayList<Byte> bytes) {
		StringBuilder sb = new StringBuilder();
		for(int i = bytes.size() - 1; i >= 0; i--) {
			Byte b = bytes.get(i);
			sb.append(String.format("%02x", b));
		}
	    return sb.toString();
	}


	public static long bytes_to_int(ArrayList<Byte> bytes) {
		StringBuilder sb = new StringBuilder();
	    for(Byte bs : bytes) {
	    	sb.append(String.format("%02x", bs));
	    }
	    return Long.valueOf(sb.toString(), 16);
	}


	    
	int get_bytes_len(String bytes_rep) {
		return bytes_rep.length() / 2;
	}
	    

	public static String remove_multiple_spaces(String line) {
		return String.join(" ", line.trim().split("\\s+"));
	}


	String id_op(String arg) {
		return arg;
	}
	
	
	String get_bin_rep(int arg) {
		String res = "";
		if(arg <= 1)
			res = String.valueOf(arg);
		else
			res = get_bin_rep(arg>>1) + String.valueOf(arg&1);
		return res;
	}
	
	
	//	Automatically generate a string using a given number
	public static String generate_sym_expr(int num) {
		int tmp = num;
		char start_char = 'a';
		int start = (int) start_char;
		int curr = start + num % 26;
		String res = Character.toString((char)curr);
		while(tmp > 25) {
			tmp = tmp / 26;
	        curr = start + tmp % 26;
	        res += Character.toString((char)curr);
		}
		return res;
	}
	
	public static boolean check_branch_inst(String inst) {
		String inst_name = inst.strip().split(" ", 2)[0];
		return Lib.JMP_INST.contains(inst_name) || inst.endsWith(" ret") || inst.startsWith("ret");
	}
	    
	public static boolean check_branch_inst_wo_call(String inst) {
		String inst_name = inst.strip().split(" ", 2)[0];
		return Lib.JMP_INST_WITHOUT_CALL.contains(inst_name) || inst.endsWith(" ret") || inst.startsWith("ret");
	}
	    
	public static boolean check_not_single_branch_inst(String inst) {
		String inst_name = inst.strip().split(" ", 2)[0];
		return Lib.CONDITIONAL_JMP_INST.contains(inst_name);
	}
	    

	public static boolean check_jmp_with_address(String line) {
		String inst_name = line.strip().split(" ", 2)[0];
		return Lib.JMP_INST_WITH_ADDRESS.contains(inst_name);
	}
	
	public static boolean check_jmp_with_jump_instr(String line) {
		String inst_name = line.strip().split(" ", 2)[0];
	    return Lib.JMP_INST_WITH_JUMP.contains(inst_name);
	}

	static int get_mem_sym_length(String sym_name) {
		int res = 128;
	    if(sym_name.startsWith("qword ")) res = 64;
	    else if(sym_name.startsWith("dword ")) res = 32;
	    else if(sym_name.startsWith("word ")) res = 16;
	    else if(sym_name.startsWith("byte ")) res = 8;
	    return res;
	}
	    

	public static int getSymLength(String sym_name, int length) {
		int res = length;
		if(Lib.REG64_NAMES.contains(sym_name)) res = 64;
		else if(Lib.REG_INFO_DICT.containsKey(sym_name))
			res = Lib.REG_INFO_DICT.get(sym_name).y;
		else if(sym_name.endsWith("]") || sym_name.contains(" ptr " ))
	        res = get_mem_sym_length(sym_name);
		// sym_name: "rax:rdx"
		else if(sym_name.contains(":")) {
			String[] regs = sym_name.split(":");
	        int left_len = getSymLength(regs[0], length / 2);
	        int right_len = getSymLength(regs[1], length / 2);
	        res = left_len + right_len;
		}
	    return res;
	}
	
	public static void convertDotToPng(String filePath) {
	    String cmd = "dot -Tpng " + filePath + ".dot > " + filePath + ".png";
	    execute_command(cmd);
	}
	
	
	public static void writeToFile(String filePath, String content) { 
		Path path = Paths.get(filePath);
		try(BufferedWriter writer = Files.newBufferedWriter(path, StandardCharsets.UTF_8)) {
			writer.write(content);
		}
		catch (IOException e) {
			e.printStackTrace();
		}
    } 

	
	public static int getSymLength(String sym_name) {
		return getSymLength(sym_name, Config.MEM_ADDR_SIZE);
	}
	
	
	public static boolean match(String expr, String regex) {
		Pattern pattern = Pattern.compile(regex);
	    Matcher matcher = pattern.matcher(expr);
	    return matcher.find();
	}
	

	public static ArrayList<String> parse_inst_args(String[] inst_split) {
		ArrayList<String> inst_args = new ArrayList<String>();
	    if(inst_split.length > 1) {
	    	String[] tmp = inst_split[1].strip().split(",");
	    	for(int i = 0; i < tmp.length; i++)
	    		inst_args.add(tmp[i].strip());
	    }
	    return inst_args;
	}

	
	public static ArrayList<String> extract_inst_args(String[] inst_split) {
		ArrayList<String> inst_args = new ArrayList<String>();
	    if(inst_split.length > 1) {
	    	inst_args = split_sep_bks(inst_split[1].strip(), ",");
	    	for(int i = 0; i < inst_args.size(); i++) {
	    		String s = inst_args.get(i);
	    		inst_args.set(i, s);
	    	}
	    } 
	    return inst_args;
	}
	
	
	public static Object eval(String expr) {
		Object result = null;
		try {
			result = script_engine.eval(expr);
		} catch (ScriptException e) {
			e.printStackTrace();
		}
		return result;	
	}
	
	
	public static String rmUnusedSpaces(String content) {
	    String res = content.strip();
	    res = res.replaceAll("[ ]*\\+[ ]*", "\\+");
	    res = res.replaceAll("[ ]*-[ ]*", "-");
	    res = res.replaceAll("[ ]*\\*[ ]*", "*");
	    res = res.replaceAll("\\+-", "-");
	    return res;
	}

	
	public static ArrayList<String> getASMFiles(String fileDir, String disasmType) {
		String cmd = "ls -d -1 \"" + fileDir + "/\"*." + disasmType;
		String out = execute_command(cmd);
		String[] outSplit = out.split("\n");
		ArrayList<String> files = new ArrayList<String>();
		for(String filePath : outSplit) {
	        if(filePath.strip() != null)
	            files.add(filePath);
		}
		return files;
	}
	
}
