package normalizer;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.regex.Pattern;

import com.microsoft.z3.BitVecExpr;

import common.InstElement;
import common.Triplet;
import common.Tuple;
import common.Utils;

public class NormObjdump implements Normalizer {

	Pattern label_address_pattern = Pattern.compile("^[0-9a-f]+ <[A-Za-z_@.0-9]+>:");
	Pattern address_inst_pattern = Pattern.compile("^[0-9a-f]+:[0-9a-f\t ]+");

	String disasmPath;
	HashMap<Long, String> addressInstMap;
	HashMap<Long, Long> addressNextMap;
	HashMap<Long, String> addressLabelMap;
	HashMap<Long, String> address_func_map;
	HashMap<Long, String> addressExtFuncMap;
	
	ArrayList<String> funcCallOrder;
	HashMap<String, ArrayList<Long>> funcAddrCallMap; 
	HashMap<String, ArrayList<String>> funcCallMap; 
	
	
	public NormObjdump(String disasmPath) throws FileNotFoundException  {
		this.disasmPath = disasmPath;
        addressInstMap = new HashMap<>();
        addressNextMap = new HashMap<>();
        addressLabelMap = new HashMap<>();
        addressExtFuncMap = new HashMap<>();
        
        funcCallOrder = new ArrayList<String>();
        funcCallOrder.add("_start");
        funcAddrCallMap = new HashMap<String, ArrayList<Long>>(); 
        funcCallMap = new HashMap<String, ArrayList<String>>(); 
        
        readASMInfo();
	}


	HashMap<Long, String> get_addressInstMap() {
        return addressInstMap;
	}


	public void readASMInfo() throws FileNotFoundException {
		File f = new File(disasmPath);
    	ArrayList<String> lines = new ArrayList<>();
    	try (BufferedReader br = new BufferedReader(new FileReader(f))) {
    	    String line;
    	    while ((line = br.readLine()) != null) {
    	    	line = line.strip();
                lines.add(line);
    	    }
    	} 
    	catch (IOException e) {
			e.printStackTrace();
		}
		String label = "";
		int bin_len = 0;
		for(String line : lines) {
	        if(line != "" ) {
	        	if(label_address_pattern.matcher(line).matches()) {
	        		Tuple<Long, String> tmp = parseAddressLabel(line);
	        		long address = tmp.x;
	        		label = tmp.y;
                    handleNewLabel(address, label);
	        	}
	        	else if(address_inst_pattern.matcher(line).matches()) {
	        		Triplet<Long, String, Integer> tmp = parseLine(line);
	        		long address = tmp.x;
	        		String inst = tmp.y;
	        		bin_len = tmp.z;
                    if(inst != "") {
                    	if(inst.startsWith("addr32 ")) {
                    		inst = inst.split("addr32", 2)[1].strip();
                    	}
                        inst = formatInst(address, inst);
                        NormHelper.construct_func_call_map(label, inst, funcAddrCallMap);
                        addressInstMap.put(address, inst);
                    }
                }
        	}
		}
		ArrayList<Long> inst_addresses = new ArrayList<Long>(addressInstMap.keySet());
	    inst_addresses.sort(null);
        int inst_num = inst_addresses.size();
        NormHelper.replace_addr_w_label(funcAddrCallMap, address_func_map, funcCallMap);
        NormHelper.create_func_call_order(funcCallMap, funcCallOrder);
        for(int idx = 0; idx < inst_addresses.size(); idx++) {
        	long address = inst_addresses.get(idx);
        	int n_idx = idx + 1; 
        	if(n_idx < inst_num) {
        		long rip = inst_addresses.get(n_idx);
        		addressNextMap.put(address, rip);
        	}
        	else {
        		long rip = address + bin_len;
        		addressNextMap.put(address, rip);
        	}
        }
	}
    
    @Override
	public HashMap<Long, String> getAddressInstMap() {
		return addressInstMap;
	}


    Triplet<Long, String, Integer> parseLine(String line) {
    	long address = -1;
		String inst = "";
		String[] line_split = line.split("\t", 3);
		int bin_len = 0;
		if(line_split.length == 3) {
			String address_str = line_split[0].split(":")[0].strip();
			address = Integer.valueOf(address_str, 16);
		    bin_len = line_split[1].strip().split(" ").length;
		    inst = line_split[2].split("#")[0].split("<")[0].strip();
		}
		return new Triplet<Long, String, Integer>(address, inst, bin_len);
    }
    
    void handleNewLabel(long address, String label) {
		if(Utils.UNVISITED_SECTION_LABELS.contains(label)) {
        	String new_label = label.strip();
        	addressLabelMap.put(address, new_label);
        	if(!label.contains("@")) {
        		address_func_map.put(address, new_label);
        	}
        	else
        		addressExtFuncMap.put(address, new_label);
        }
	}


    Tuple<Long, String> parseAddressLabel(String line) {
    	String[] line_split = line.strip().split(" ", 2);
        long address = Long.parseLong(line_split[0].strip(), 16);
        String label = line_split[1].split("<")[1].split(">")[0].strip();
        return new Tuple<Long, String>(address, label);
    }


    String formatInst(long address, String inst) {
    	InstElement instElem = new InstElement (inst);
    	ArrayList<String> instArgs = new ArrayList<>();
    	String arg;
//    	System.out.println(inst);
    	for(String s : instElem.inst_args) {
    		arg = formatArg(address, instElem.inst_name, s);
    		instArgs.add(arg);
    	}
        String result = instElem.inst_name + " " + String.join(",", instArgs);
        result = result.strip();
        return result;
    }


    String formatArg(long address, String inst_name, String arg) {
        String res = arg.toLowerCase();
        res = NormHelper.convert_to_hex_rep(res);
        res = NormHelper.norm_objdump_arg(inst_name, res);
        if(Utils.check_jmp_with_address(inst_name)) {
            if(Utils.imm_pat_wo_prefix.matcher(res).matches())
                res = "0x" + res;
        }
        return res;
    }

	@Override
	public HashMap<Long, Long> getAddressNextMap() {
		return addressNextMap;
	}


	@Override
	public HashMap<Long, String> getAddressExtFuncMap() {
		return addressExtFuncMap;
	}


	@Override
	public HashMap<Long, ArrayList<BitVecExpr>> readGlobalJPTEntriesMap() {
		return null;
	}


	@Override
	public HashSet<Long> getFuncEndAddrSet() {
		return null;
	}


	@Override
	public Long getMainAddress() {
		return null;
	}


	@Override
	public Long getEntryAddress() {
		return null;
	}


	@Override
	public HashMap<Long, String> getAddressSymTbl() {
		return null;
	}


	@Override
	public HashMap<String, Long> getSymTbl() {
		return null;
	}


	@Override
	public HashMap<String, Long> getSecStartAddr() {
		return null;
	}


	@Override
	public HashMap<String, Long> getSecEndAddr() {
		return null;
	}


	@Override
	public HashMap<String, Long> getSecBaseAddr() {
		return null;
	}

}