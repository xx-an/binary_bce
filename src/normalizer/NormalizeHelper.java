package normalizer;

import java.io.File;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.regex.Pattern;

import common.Utils;

public class NormalizeHelper {
	
	Pattern remote_addr_pat = Pattern.compile("0x2[0-9a-fA-F]{5}");
	
	NormalizeHelper() {}
	
	void disassemble_to_asm(String exec_path, String disasm_path, String disasm_type) throws Exception {
		File f = new File(disasm_path);
	    if(f.exists()) return;
	    if(disasm_type == "objdump") {
	        String cmd = "objdump -M intel -d " + exec_path + " > " + disasm_path;
	        Utils.execute_command(cmd);
	    }
	    else
	    	throw new Exception("The assembly file has not been generated");
	}


//	void disassemble_angr(String exec_path, String asm_path) {
//	    proj = angr.Project(exec_path, auto_load_libs=False, load_options={"main_opts": {"base_addr": 0x000000}})
//	    cfg = proj.analyses.CFGFast()
//	    nodes = cfg.graph.nodes()
//	    sys.stdout = open(asm_path, "w+")
//	    for node in nodes:
//	        if(node and node.block:
//	            node.block.pp()
//	        print("\n")
//	    sys.stdout.close()
//	}


	String convert_to_hex(String line) {
		String res = "";
		if(Pattern.matches("^[0-9a-f]+$", line)) {
			res = "0x" + line.strip();
		}
	    return res;
	}
	
	
	String to_hex(int num, int bits) {
		int res = (num + (1 << bits)) % (1 << bits);
		return Integer.toHexString(res);
	}
	
	String calculate_relative_address(String line, int address) {
		String res = "";
	    if(Pattern.matches("^0x[0-9a-f]+$|^[0-9a-f]+$", line)) {
	        int relative_address = Integer.valueOf(line, 16) - address;
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
	        int absolute_address = Integer.valueOf(line, 16) + rip;
	        if(absolute_address >= 0)
	            res = String.format("0x%x", absolute_address);
	        else
	            res = to_hex(absolute_address, 64);
	    }
	    return res;
	}
	
	
	boolean check_section_start(String line, String disassembler) {
		boolean result = false;
		if(disassembler == "objdump")
	        result = line.startsWith("Disassembly of section");
	    return result;
	}
	
	
	String normalize_arg(int address, String name, String arg) {
		String res = arg.replaceAll("[+-]0x0\\b|\\*1\\b", "");
		if(Utils.check_jmp_with_address(name))
			res = calculate_relative_address(res, address);
		return res;
	}
	
	
	String remove_att_prefix(String arg) {
	    String res = arg;
	    if(arg.startsWith("%"))
	        res = arg.split("%", 1)[1].strip();
	    else if(arg.startsWith("*%"))
	        res = arg.split("*%", 1)[1].strip();
	    else if(arg.startsWith("$0x") || arg.startsWith("$-0x"))
	        res = arg.split("$", 1)[1].strip();
	    return res;
	}
	
	
	String reconstruct_att_memory_rep(String inst_name, String arg) {
		StringBuilder sb = new StringBuilder();
		sb.append("[");
	    String[] arg_split = arg.split("(", 1);
	    String[] arg_split_1 = Utils.rsplit(arg_split[1].strip(), ")")[0].split(",");
	    String arg_split_1_0 = arg_split_1[0].strip();
	    sb.append(remove_att_prefix(arg_split_1_0));
	    if(arg_split_1.length > 1) {
	        if(arg_split_1_0 != "")
	        	sb.append("+");
	        sb.append(remove_att_prefix(arg_split_1[1]));
	        if(arg_split_1.length == 3)
	        	sb.append("*" + remove_att_prefix(arg_split_1[2]));
	    }
	    if(arg_split[0].strip() != "")
	        sb.append("+" + remove_att_prefix(arg_split[0].strip()));
	    sb.append("]");
	    return sb.toString();
	}
	

	String rewrite_att_memory_rep(String inst_name, String arg) {
	    String res = arg;
	    if(arg.startsWith("*"))
	        res = arg.split("*", 1)[1].strip();
	    // %cs:(%rax,%rax)
	    if(arg.contains("(")) {
	        if(arg.contains("%st"))
	            res = arg.split("%", 1)[1].strip();
	        else if(arg.contains(":")) {
	            String[] arg_split = arg.split(":");
	            res = remove_att_prefix(arg_split[0]) + ":";
	            res += reconstruct_att_memory_rep(inst_name, arg_split[1].strip());
	        }
	        else
	            res = reconstruct_att_memory_rep(inst_name, arg);
	    }
	    // %fs:0x28
	    else if(arg.contains(":")) {    
	        String[] arg_split = arg.split(":");
	        res = remove_att_prefix(arg_split[0]) + ":" + remove_att_prefix(arg_split[1]);
	    }
	    else
	        res = remove_att_prefix(arg);
	    if(res.endsWith("]"))
	        res = res.replace("+-", "-");
	    return res;
	}


	String rewrite_absolute_address_to_relative(String arg, int rip) {
	    String res = arg;
	    if(arg.endsWith("]") && !arg.contains("s:")) {
	        String[] arg_split = arg.strip().split("[");
	        String arg_content = arg_split[1].split("]")[0].strip();
	        if(Pattern.matches("^0x[0-9a-f]+$|^-0x[0-9a-f]+$", arg_content)) {
	            int relative_address = Integer.valueOf(arg_content, 16) - rip;
	            if(relative_address >= 0)
	                res = String.format("[rip+0x%x]", relative_address);
	            else
	                res = "[rip+" + to_hex(relative_address, 64) + "]";
	            if(arg.startsWith("qword") || arg.startsWith("dword") || arg.startsWith("word") || arg.startsWith("byte") || arg.startsWith("tbyte") || arg.startsWith("xmmword"))
	                res = arg_split[0] + res;
	        }
	    }
	    else if(Pattern.matches("^0x[0-9a-f]+$|^-0x[0-9a-f]+$", arg)) {
	    	res = Integer.toHexString(Utils.imm_str_to_int(arg));
	    }
	    return res;
	}


	public static String convert_to_hex_rep(String arg) {
	    String res = arg;
	    if(Pattern.matches("^[0-9a-f]+$|^-[0-9a-f]+$", arg))
	        res = Integer.toHexString(Integer.valueOf(arg, 16));
	    return res;
	}


	public static String norm_objdump_arg(String name, String arg) {
	    String res = arg;
	    if(name == "fdivrp" && arg == "st")
	        res = "st(0)";
	    return res;
	}
	
	
	public static void construct_func_call_map(String label, String inst, HashMap<String, ArrayList<Long>> func_addr_call_map) {
		if(inst.startsWith("call ")) {
            String address_str = inst.split(" ", 1)[1].strip();
            if(Utils.imm_start_pat.matcher(address_str).matches()) {
                long address = Long.valueOf(address_str, 16);
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
	
}
