package normalizer;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Scanner;
import java.util.regex.Pattern;

import common.InstElement;
import common.Triplet;
import common.Tuple;
import common.Utils;

public class NormalizeObjdump implements Normalize {
	
	String disasm_path;
	HashMap<Long, String> address_inst_map = new HashMap<Long, String>();
	HashMap<Long, Long> address_next_map = new HashMap<Long, Long>();
	HashMap<Long, String> address_label_map = new HashMap<Long, String>();
	HashMap<Long, String> address_func_map = new HashMap<Long, String>();
	HashMap<Long, String> address_ext_func_map = new HashMap<Long, String>(); 
	ArrayList<String> func_call_order = new ArrayList<String>();
	HashMap<String, ArrayList<Long>> func_addr_call_map = new HashMap<String, ArrayList<Long>>(); 
	HashMap<String, ArrayList<String>> func_call_map = new HashMap<String, ArrayList<String>>(); 
	int valid_address_no = 0;
	
	Pattern label_address_pattern = Pattern.compile("^[0-9a-f]+ <[A-Za-z_@.0-9]+>:");
	Pattern address_inst_pattern = Pattern.compile("^[0-9a-f]+:[0-9a-f\t ]+");
	

	public NormalizeObjdump(String disasmPath, String exec_path) throws FileNotFoundException {
		disasm_path = disasmPath;
		func_call_order.add("_start");
		read_asm_info();
	}

	void _handle_new_label(long address, String label) {
		if(Utils.UNVISITED_SECTION_LABELS.contains(label)) {
        	String new_label = label.strip();
        	address_label_map.put(address, new_label);
        	if(!label.contains("@")) {
        		address_func_map.put(address, new_label);
        	}
        	else
        		address_ext_func_map.put(address, new_label);
        }
	}
	
	@Override
	public void read_asm_info() throws FileNotFoundException {
		File f = new File(disasm_path);
		Scanner sn = new Scanner(f);
		String label = "";
		int bin_len = 0;
		while (sn.hasNextLine()) {
	        String line = sn.nextLine();
	        line = line.strip();
	        if(line != "" ) {
	        	if(label_address_pattern.matcher(line).matches()) {
	        		Tuple<Integer, String> tmp = _parse_address_label(line);
	        		int address = tmp.x;
	        		label = tmp.y;
                    _handle_new_label(address, label);
	        	}
	        	else if(address_inst_pattern.matcher(line).matches()) {
	        		Triplet<Integer, String, Integer> tmp = _parse_line(line);
	        		long address = tmp.x;
	        		String inst = tmp.y;
	        		bin_len = tmp.z;
                    if(inst != "") {
                    	if(inst.startsWith("addr32 ")) {
                    		inst = inst.split("addr32", 1)[1].strip();
                    	}
                        inst = _format_inst(address, inst);
                        NormalizeHelper.construct_func_call_map(label, inst, func_addr_call_map);
                        address_inst_map.put(address, inst);
                        valid_address_no += 1;
                    }
                }
        	}
		}
		ArrayList<Long> inst_addresses = new ArrayList<Long>(address_inst_map.keySet());
	    inst_addresses.sort(null);
        int inst_num = inst_addresses.size();
        NormalizeHelper.replace_addr_w_label(func_addr_call_map, address_func_map, func_call_map);
        NormalizeHelper.create_func_call_order(func_call_map, func_call_order);
        for(int idx = 0; idx < inst_addresses.size(); idx++) {
        	long address = inst_addresses.get(idx);
        	int n_idx = idx + 1; 
        	if(n_idx < inst_num) {
        		long rip = inst_addresses.get(n_idx);
        		address_next_map.put(address, rip);
        	}
        	else {
        		long rip = address + bin_len;
        		address_next_map.put(address, rip);
        	}
        }
	}

	@Override
	public HashMap<Long, String> get_address_inst_map() {
		return address_inst_map;
	}
	
	
	Triplet<Integer, String, Integer> _parse_line(String line) {
		int address = -1;
		String inst = "";
		String[] line_split = line.split("\t", 2);
		int bin_len = 0;
		if(line_split.length == 3) {
			String address_str = line_split[0].split(":")[0].strip();
			address = Integer.valueOf(address_str, 16);
		    bin_len = line_split[1].strip().split(" ").length;
		    inst = line_split[2].split("#")[0].split("<")[0].strip();
		}
		return new Triplet<Integer, String, Integer>(address, inst, bin_len);
	}


    Tuple<Integer, String> _parse_address_label(String line) {
        String[] line_split = line.strip().split(" ", 1);
        int address = Integer.valueOf(line_split[0].strip(), 16);
        String label = line_split[1].split("<")[1].split(">")[0].strip();
        return new Tuple<Integer, String>(address, label);
    }


    String _format_inst(long address, String inst) {
    	InstElement inst_elem = new InstElement(inst);
    	ArrayList<String> inst_args = inst_elem.inst_args;
    	for(int i = 0; i < inst_args.size(); i++) {
    		String arg = inst_args.get(i);
    		inst_args.set(i, _format_arg(address, inst_elem.inst_name, arg));
    	}
        return inst_elem.normalize(address, Utils.id_op);
    }
    
    String _format_arg(long address, String inst_name, String arg) {
        String res = arg.toLowerCase();
        res = NormalizeHelper.convert_to_hex_rep(res);
        res = NormalizeHelper.norm_objdump_arg(inst_name, res);
        if(Utils.check_jmp_with_address(inst_name)) {
            if(Utils.imm_pat_wo_prefix.matcher(res).matches())
                res = "0x" + res;
        }
        return res;
    }

}
