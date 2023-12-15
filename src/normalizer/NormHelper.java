package normalizer;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.regex.Pattern;

import common.Config;
import common.Tuple;
import common.Utils;

public class NormHelper {
	
	public static Pattern simple_op_split_pat = Pattern.compile("((?<=\\+)|(?=\\+)|(?<=-)|(?=-)|(?<=\\*)|(?=\\*))");
	public static Pattern simple_operator_pat = Pattern.compile("(\\+|-|\\*)");
	
	public static HashMap<String, String> BYTE_LEN_REPS;
	public static HashMap<Integer, String> BYTELEN_REP_MAP;
	public static HashMap<String, String> IDA_BYTEREP_PTR_MAP;
	
	public static String[] IDAWordTypes = new String[]{" db ", " dq ", " dw ", " dd ", " dt ", " xmmword "};
	
	static {
		BYTE_LEN_REPS = new HashMap<>();
		BYTE_LEN_REPS.put("byte", "byte");
		BYTE_LEN_REPS.put("dword", "dword");
		BYTE_LEN_REPS.put("fword", "fword");
		BYTE_LEN_REPS.put("qword", "qword");
		BYTE_LEN_REPS.put("word", "word");
		BYTE_LEN_REPS.put("tbyte", "tbyte");
		BYTE_LEN_REPS.put("tword", "tbyte");
		BYTE_LEN_REPS.put("xword", "tbyte");
		BYTE_LEN_REPS.put("xmmword", "xmmword");
				
		
		IDA_BYTEREP_PTR_MAP = new HashMap<>();
		IDA_BYTEREP_PTR_MAP.put("dq", "qword ptr");
		IDA_BYTEREP_PTR_MAP.put("dd", "dword ptr");
		IDA_BYTEREP_PTR_MAP.put("dw", "word ptr");
		IDA_BYTEREP_PTR_MAP.put("db", "byte ptr");
		IDA_BYTEREP_PTR_MAP.put("dt", "tbyte ptr");
		IDA_BYTEREP_PTR_MAP.put("xmmword", "xmmword ptr");
		
		
		BYTELEN_REP_MAP = new HashMap<>();
		BYTELEN_REP_MAP.put(64, "qword ptr");
		BYTELEN_REP_MAP.put(32, "dword ptr");
		BYTELEN_REP_MAP.put(16, "word ptr");
		BYTELEN_REP_MAP.put(8, "byte ptr");
	}
	
	public static void disassemble_to_asm(String execPath, String disasmPath, String disasmType) throws Exception {
		if(Files.exists(Paths.get(disasmPath))) return;
	    if(disasmType.equals("objdump")) {
	        String cmd = "objdump -M intel -d " + execPath + " > " + disasmPath;
	        Utils.execute_command(cmd);
	    }
	    else
	    	throw new Exception("The assembly file has not been generated");
	}
	
	

	public static String convertImmEndHToHex(String imm) {
	    String tmp = Utils.rsplit(imm, "h")[0].strip();
	    String res = Utils.toHexString(Long.parseLong(tmp, 16));
	    return res;
	}
	
	public static long convertImmToLong(String imm) {
		String tmp = Utils.rsplit(imm, "h")[0].strip();
	    long res = Long.parseLong(tmp, 16);
	    return res;
	}
	
	
	public static HashMap<String, HashMap<String, Tuple<Integer, String>>> init_ida_struct_info() throws FileNotFoundException {
		HashMap<String, HashMap<String, Tuple<Integer, String>>> idaStructTable = new HashMap<>();
	    Path idaInfoPath = Paths.get(Utils.PROJECT_DIR.toString(), "ida_struct.info");
	    String itemName = null;
	    String offsetStr = null;
	    String itemType = null;
	    String structName = null;
	    int offset;
	    HashMap<String, Tuple<Integer, String>> structEntry = null;
	    Tuple<Integer, String> itemInfo = null;
	    File f = new File(idaInfoPath.toString());
	    try (BufferedReader br = new BufferedReader(new FileReader(f))) {
    	    String line;
    	    while ((line = br.readLine()) != null) {
    	    	line = line.strip();
	            if(line != "" && !line.startsWith("#")) {
	            	String[] lineSplit = line.split(":", 2);
	                if(lineSplit[1].strip() != "") {
	                	itemName = lineSplit[0];
	                	String[] ls = lineSplit[1].strip().split(",", 2);
	                	offsetStr = ls[0];
	                	itemType = ls[1];
	                    offset = Integer.decode(offsetStr.strip());
	                    structEntry = idaStructTable.get(structName);
	                    itemInfo = new Tuple<>(offset, itemType.strip());
	                    structEntry.put(itemName, itemInfo);
	                }
	                else {
	                	structName = lineSplit[0];
	                	structEntry = new HashMap<>();
	                    idaStructTable.put(structName, structEntry);
	                }
	            }
    	    }
    	} 
	    catch (IOException e) {
			e.printStackTrace();
		}
	    return idaStructTable;
	}
	    		


	String convert_to_hex(String line) {
		String res = "";
		if(Pattern.matches("^[0-9a-f]+$", line)) {
			res = "0x" + line.strip();
		}
	    return res;
	}
	
	
	String to_hex(int num, int bits) {
		int res = (num + (1 << bits)) % (1 << bits);
		return Utils.toHexString(res);
	}
	
	public static String getIdaPtrRepFromItemType(String itemType) {
	    String res = null;
	    if(itemType.equals("dd") || itemType.equals("dq") || itemType.equals("db") || itemType.equals("dw") || itemType.equals("dt") || itemType.equals("xmmword")) {
	        res = IDA_BYTEREP_PTR_MAP.get(itemType);
	    }
	    return res;
	}

	
	public static String convertToHexRep(String arg) {
	    String res = arg;
	    if(arg.matches("^[0-9a-f]+$|^-[0-9a-f]+$"))
	        res = Utils.toHexString(Long.valueOf(arg, 16));
	    return res;
	}
	
	public static String generateIdaPtrRep(String name, String inst, int length) {
	    String wordPtrRep = null;
	    if(name.startsWith("jmp"))
	        wordPtrRep = BYTELEN_REP_MAP.get(Config.MEM_ADDR_SIZE);
	    else if(name.equals("call"))
	        wordPtrRep = BYTELEN_REP_MAP.get(Config.MEM_ADDR_SIZE);
	    else if(name.equals("mov") || name.equals("cmp")) {
	        if(length != 0)
	        	wordPtrRep = BYTELEN_REP_MAP.get(length);
	    }
	    else if(name.startsWith("j"))
	        wordPtrRep = BYTELEN_REP_MAP.get(Config.MEM_ADDR_SIZE);
	    else if(name.startsWith("set"))
	        wordPtrRep = "byte ptr";
	    else if(name.equals("subs") || name.equals("movs") || name.equals("ucomis"))
	        wordPtrRep = "dword ptr";
	    else if(name.equals("movdqu") || name.equals("movaps") || name.equals("movdqa") || name.equals("movups"))
	        wordPtrRep = "xmmword ptr";
	    else if(name.equals("movq") && inst.contains("xmm")) {}
	    else if(name.equals("movsxd")) {
	        if(length == 16 || length == 32)
	            wordPtrRep = BYTELEN_REP_MAP.get(length);
	        else
	            wordPtrRep = "dword ptr";
	    }
	    else if(name.equals("movss"))
	        wordPtrRep = "dword ptr";
	    return wordPtrRep;
	}
	
	
	String calculate_relative_address(String line, int address) {
		String res = "";
	    if(Pattern.matches("^0x[0-9a-f]+$|^[0-9a-f]+$", line)) {
	        int relative_address = Integer.decode(line) - address;
	        if(relative_address >= 0)
	            res = String.format("0x%x", relative_address);
	        else
	            res = to_hex(relative_address, 64);
	    }
	    return res;
	}
	
	String calculate_absolute_address(String line, int rip) {
		String res = "";
	    if(Pattern.matches("^0x[0-9a-f]+$|^-0x[0-9a-f]+$", line)) {
	        int absolute_address = Integer.decode(line) + rip;
	        if(absolute_address >= 0)
	            res = String.format("0x%x", absolute_address);
	        else
	            res = to_hex(absolute_address, 64);
	    }
	    return res;
	}
	
	
	boolean check_section_start(String line, String disassembler) {
		boolean result = false;
		if(disassembler.equals("objdump"))
	        result = line.startsWith("Disassembly of section");
	    return result;
	}
	
	
	String normalize_arg(int address, String name, String arg) {
		String res = arg.replaceAll("[+-]0x0\\b|\\*1\\b", "");
		if(Utils.check_jmp_with_address(name))
			res = calculate_relative_address(res, address);
		return res;
	}
	

	String rewrite_absolute_address_to_relative(String arg, int rip) {
	    String res = arg;
	    if(arg.endsWith("]") && !arg.contains("s:")) {
	        String[] arg_split = arg.strip().split("\\[");
	        String arg_content = arg_split[1].split("]")[0].strip();
	        if(Pattern.matches("^0x[0-9a-f]+$|^-0x[0-9a-f]+$", arg_content)) {
	            int relative_address = Integer.decode(arg_content) - rip;
	            if(relative_address >= 0)
	                res = String.format("[rip+0x%x]", relative_address);
	            else
	                res = "[rip+" + to_hex(relative_address, 64) + "]";
	            if(arg.startsWith("qword") || arg.startsWith("dword") || arg.startsWith("word") || arg.startsWith("byte") || arg.startsWith("tbyte") || arg.startsWith("xmmword"))
	                res = arg_split[0] + res;
	        }
	    }
	    else if(Pattern.matches("^0x[0-9a-f]+$|^-0x[0-9a-f]+$", arg)) {
	    	res = Utils.toHexString(Utils.imm_str_to_int(arg));
	    }
	    return res;
	}


	public static String convert_to_hex_rep(String arg) {
	    String res = arg;
	    if(Pattern.matches("^[0-9a-f]+$|^-[0-9a-f]+$", arg))
	        res = Utils.toHexString(Integer.decode(arg));
	    return res;
	}


	public static String norm_objdump_arg(String name, String arg) {
	    String res = arg;
	    if(name.equals("fdivrp") && arg.equals("st"))
	        res = "st(0)";
	    return res;
	}
	
	
	public static void construct_func_call_map(String label, String inst, HashMap<String, ArrayList<Long>> func_addr_call_map) {
		if(inst.startsWith("call ")) {
            String address_str = inst.split(" ", 2)[1].strip();
            if(Utils.imm_start_pat.matcher(address_str).matches()) {
                long address = Long.decode(address_str);
                if(func_addr_call_map.containsKey(label)) {
                	ArrayList<Long> address_list = func_addr_call_map.get(label);
                	address_list.add(address);
                }
                else {
                	ArrayList<Long> address_list = new ArrayList<Long>();
                	address_list.add(address);
                	func_addr_call_map.put(label, address_list);
                }
            }
		}
	}
	
	public static void replace_addr_w_label(HashMap<String, ArrayList<Long>> func_addr_call_map, HashMap<Long, String> address_func_map, HashMap<String, ArrayList<String>> func_call_map) {
		for(String label : func_addr_call_map.keySet()) {
			ArrayList<String> called_functions = new ArrayList<String>();
			func_call_map.put(label, called_functions);
			ArrayList<Long> address_list = func_addr_call_map.get(label);
        	for(int i = 0; i < address_list.size(); i++) {
        		long address = address_list.get(i);
        		if(address_func_map.containsKey(address)) {
        			called_functions.add(address_func_map.get(address));
        		}
        	}
		}
	}
	
	
	public static void create_func_call_order(HashMap<String, ArrayList<String>> func_call_map, ArrayList<String> func_call_order) {
		ArrayList<String> func_stack = new ArrayList<String>();
		func_stack.add("main");
		while(!func_stack.isEmpty()) {
			String func_name = func_stack.remove((func_stack.size()- 1));
			if(func_call_map.containsKey(func_name)) {
				int idx = func_call_order.size();
				ArrayList<String> called_func_list = func_call_map.get(func_name);
				for(String called_func : called_func_list) {
					if(called_func != "") {
						if(func_call_order.contains(called_func)) {
							int curr_idx = func_call_order.indexOf(called_func);
							if(curr_idx < idx)
								idx = curr_idx;
						}
						else if(called_func != func_name)
							func_stack.add(called_func);
					}
				}
				if(!func_call_order.contains(func_name)) {
                    func_call_order.add(idx, func_name);
				}
			}
			else if(!func_call_order.contains(func_name))
				func_call_order.add(func_name);
		}
	}
	
	
	static long evalSimpleFormula(ArrayList<Long> stack, ArrayList<String> opStack) {
	    long res = stack.get(0);
	    int opNum = opStack.size();
	    for(int idx = 0; idx < opNum; idx++) {
	    	String op = opStack.get(idx);
	        if(op.equals("+"))
	            res = res + stack.get(idx + 1);
	        else if(op.equals("-")) {
	            res = res - stack.get(idx + 1);
	        }
	    }
	    return res;
	}


	static String reconstructFormulaExpr(ArrayList<String> stack, ArrayList<String> opStack, ArrayList<Integer> idxList, long immVal) {
	    String res = "";
	    int stackSize = stack.size();
	    for(int idx = 0; idx < stackSize; idx++) {
	    	String val = stack.get(idx);
	    	if(!idxList.contains(idx)) {
	            if(idx > 0)
	                res += opStack.get(idx - 1) + val;
	            else
	                res += val;
	    	}
	    }
	    if(res != "")
	        res += "+" + Utils.toHexString(immVal);
	    else
	        res = Utils.toHexString(immVal);
	    res = res.replace("+-", "-");
	    return res;
	}


	public static String reconstructFormula(ArrayList<String> stack, ArrayList<String> opStack) {
	    String res = "";
	    int stackSize = stack.size();
	    for(int idx = 0; idx < stackSize; idx++) {
	    	String val = stack.get(idx);
	        if(idx > 0) {
	            String op = opStack.get(idx - 1);
	            res += op;
	            if((op.equals("+") || op.equals("-")) && Utils.imm_start_pat.matcher(val).matches())
	                res += Utils.toHexString(Utils.imm_str_to_int(val));
	            else
	                res += val;
	        }
	        else
	            res += val;
	    }
	    res = res.replace("+-", "-");
	    return res;
	}


	public static String calcFormulaExpr(ArrayList<String> stack, ArrayList<String> opStack, String content) {
	    String res = content;
	    ArrayList<Integer> idxList = new ArrayList<>();
	    ArrayList<Long> valList = new ArrayList<>();
	    ArrayList<String> opList = new ArrayList<>();
	    long val, numVal = 0;
	    String valStr, op;
	    int stackSize = stack.size();
	    for(int idx = 0; idx < stackSize; idx++) {
	    	valStr = stack.get(idx);
	    	if(Utils.imm_pat.matcher(valStr).matches()) {
	    		if(idx > 0) {
			    	op = opStack.get(idx - 1);
			    	if(op.equals("+") || op.equals("-")) {
			    		val = Utils.imm_str_to_int(valStr);
			    		numVal = val;
			            if(valList != null && valList.size() > 0)
			            	opList.add(op);
			            else
			                numVal = (op.equals("+")) ? val : -val;
			            idxList.add(idx);
				        valList.add(numVal);
			    	}
	    		}
	    		else {
	    			numVal = Utils.imm_str_to_int(valStr);
	    			idxList.add(idx);
			        valList.add(numVal);
	    		}
	    	}	    
	    }
	    if(valList.size() > 1) {
	        long immVal = evalSimpleFormula(valList, opList);
	        res = reconstructFormulaExpr(stack, opStack, idxList, immVal);
	    }
	    else
	        res = reconstructFormula(stack, opStack);
	    return res;
	}
	

	public static String simulateEvalExpr(String content) {
		ArrayList<String> stack = new ArrayList<String>();
		ArrayList<String> opStack = new ArrayList<String>();
	    String line = Utils.rmUnusedSpaces(content);
	    String[] lineSplit = simple_op_split_pat.split(line);
	    String val;
	    for(String lsi : lineSplit) {
	        lsi = lsi.strip();
	        if(simple_operator_pat.matcher(lsi).matches())
	            opStack.add(lsi);
	        else {
	            val = lsi;
	            stack.add(val);
	        }
	    }
	    String res = calcFormulaExpr(stack, opStack, content);
	    return res;
	}

	
}
