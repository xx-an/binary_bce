package binary;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.regex.Pattern;

import com.microsoft.z3.BitVecExpr;

import common.Utils;
import common.Config;
import common.Helper;

public class BinaryInfo {
	
	public String src_path;
	public ArrayList<String> section_list = new ArrayList<String>();
	public HashMap<String, Integer> section_address_map = new HashMap<String, Integer>();
	public HashMap<String, BitVecExpr> sym_table = new HashMap<String, BitVecExpr>();
	public HashMap<String, Integer> function_addr_table = new HashMap<String, Integer>();
	public HashMap<String, Integer> sym_name_count = new HashMap<String, Integer>();
	public HashMap<BitVecExpr, ArrayList<String>> address_sym_table = new HashMap<BitVecExpr, ArrayList<String>>();
	public HashMap<Long, String> dllFuncInfo = new HashMap<>();
	public long data_start_addr = Long.MAX_VALUE;
	public long data_base_addr = Long.MAX_VALUE;
	public long data_end_addr = Long.MIN_VALUE;
	public long rodata_start_addr = Long.MAX_VALUE;
	public long rodata_base_addr = Long.MAX_VALUE;
	public long rodata_end_addr = Long.MIN_VALUE;
	public long text_start_addr = Long.MAX_VALUE;
	public long text_base_addr = Long.MAX_VALUE;
	public long text_end_addr = Long.MIN_VALUE;
	public long max_bin_header_address = Long.MIN_VALUE;
	public Long entry_address = null;
	public long main_address = -1;
	
	
	public BinaryInfo(String srcPath) {
		src_path = srcPath;
		read_binary_info();
	}
	
	void read_binary_info() {
		String binary_header = Utils.execute_command("objdump -f " + src_path);
		parse_entry_address(binary_header);
		String section_headers = Utils.execute_command("objdump -h " + src_path);
		parse_section_headers(section_headers);
		String symtable = Utils.execute_command("objdump -t " + src_path);
		parse_sym_table(symtable);
		String relocation = Utils.execute_command("objdump -R " + src_path);
		parse_relocation(relocation);
		reverse_sym_table();
		String external_info = Utils.execute_command("objdump -x " + src_path);
		parse_external_info(external_info);
	}
	
	long get_entry_address() {
		return entry_address;
	}


	void parse_entry_address(String binary_header) {
	    String[] lines = binary_header.split("\n");
	    for(String line : lines) {
	    	line = line.strip();
            if(line.startsWith("start address "))
                entry_address = Long.valueOf(Utils.rsplit(line, " ")[1], 16);
	    }   
	    if(entry_address == null) {
            Utils.logger.info("The executable file cannot be correctly disassembled");
            System.exit(0);
	    }
	}

	// line: "[ 1] .interp           PROGBITS         0000000000000238  00000238"
	void parse_section_headers(String section_headers) {
		String[] lines = section_headers.split("\n");
	    for(String line : lines) {
	        line = line.strip();
	        if(line != "" && Utils.imm_start_pat.matcher(line).matches()) {
                String[] line_split = Utils.remove_multiple_spaces(line).split(" ");
                String section_name = line_split[1];
                int section_size = Integer.valueOf(line_split[2], 16);
                int section_address = Integer.valueOf(line_split[3], 16);
                max_bin_header_address = Math.max(max_bin_header_address, section_address + section_size + 1);
                int section_offset = Integer.valueOf(line_split[5], 16);
                section_address_map.put(section_name, section_address);
                sym_table.put(section_name, Helper.gen_bv_num(section_address, Config.MEM_ADDR_SIZE));
                if(section_name == ".data") {
                    data_start_addr = section_address;
                    data_base_addr = section_address - section_offset;
                    data_end_addr = section_address + section_size + 1;
                }
                else if(section_name == ".rodata") {
                    rodata_start_addr = section_address;
                    rodata_base_addr = section_address - section_offset;
                    rodata_end_addr = section_address + section_size + 1;
                }
                else if(section_name == ".text") {
                    text_start_addr = section_address;
                    text_base_addr = section_address - section_offset;
                    text_end_addr = section_address + section_size + 1;
                }
	        }
	    }
	}
	        

	// line: "58: 000000000000063a    23 FUNC    GLOBAL DEFAULT   14 main"
	void parse_sym_table(String sym_list_str) {
	        String[] lines = sym_list_str.split("\n");
	        for(String line : lines) {
	            line = line.strip();
	            if(line != "" && Utils.imm_start_pat.matcher(line).matches() && !line.contains("*ABS*")) {
                    String[] line_split = Utils.remove_multiple_spaces(line).split(" ");
                    int sym_val = Integer.valueOf(line_split[0], 16);
                    String sym_type = line_split[line_split.length-4];
                    String sym_name = line_split[line_split.length-1];
                    if(sym_type == "F")
                        if(!sym_name.contains("@") && !Utils.UNVISITED_SECTION_LABELS.contains(sym_name))
                           function_addr_table.put(sym_name, sym_val);
                    sym_name = correctify_sym_name(sym_name);
                    if(!section_address_map.containsKey(sym_name)) {
	                    if(!sym_table.containsKey(sym_name)) {
	                        sym_table.put(sym_name, Helper.gen_bv_num(sym_val, Config.MEM_ADDR_SIZE));
	                        sym_name_count.put(sym_name, 1);
	                    }
	                    else {
	                        String new_sym_name = sym_name + "_" + String.valueOf(sym_name_count.get(sym_name));
	                        sym_table.put(new_sym_name, Helper.gen_bv_num(sym_val, Config.MEM_ADDR_SIZE));
	                        int prev_count = sym_name_count.get(sym_name);
	                        sym_name_count.put(sym_name, prev_count + 1);
	                    }
                    }
                }
	        }
	        if(sym_table.containsKey("main"))
	        	main_address = Helper.long_of_sym(sym_table.get("main"));
	}
	
	String correctify_sym_name(String sym_name) {
		String res = sym_name;
		if(sym_name.contains("@"))
			res = sym_name.split("@", 1)[0];
	    return res;
	}

	// line: "000000200fe0  000300000006 R_X86_64_GLOB_DAT 0000000000000000 __libc_start_main@GLIBC_2.2.5 + 0"
	void parse_relocation(String relocation) {
		String[] lines = relocation.split("\n");
		for(String line : lines) {
			line = line.strip();
			if(line != "" && !line.contains("*ABS*") && Utils.imm_start_pat.matcher(line).matches()) {
				line = Utils.remove_multiple_spaces(line);
				String[] line_split = line.split(" ");
				parse_reloc(line_split);
			}
		}
	}
//				if(line_split.length != 4) {
//					if(line_split[line_split.length - 2] == "+") {
//						String[] line_split_sub = Arrays.copyOf(line_split, line_split.length - 2);
//						_parse_reloc(line_split_sub);
//					}
//					else
//						_parse_reloc(line_split);
//				}
//			}
//			else if(line.startsWith("Relocation section ") && line.contains("at offset")) {
//                String sym_name = line.split("\"", 1)[1].split("\"", 1)[0].strip();
//                String sym_addr = line.split("at offset ", 1)[1].split(" ", 1)[0].strip();
//                int sym_val = Integer.valueOf(sym_addr, 16);
//                sym_table.put(sym_addr, Helper.gen_bv_num(sym_val, Config.MEM_ADDR_SIZE));
//			}
//		}
//	}


	// line: "000000200fe0  000300000006 R_X86_64_GLOB_DAT 0000000000000000 __libc_start_main@GLIBC_2.2.5"
	void parse_reloc(String[] line_split) {
		String sym_name = line_split[-1];
	    BitVecExpr sym_addr = Helper.gen_spec_sym("mem@" + Integer.toHexString(Integer.valueOf(line_split[0], 16)), Config.MEM_ADDR_SIZE);
	    if(sym_name.contains("GLIBC"))
	    	sym_name = sym_name.split("@", 1)[0];
	    if(sym_table.containsKey(sym_name))
	         sym_table.put(sym_name, sym_addr);
	}
	
	void reverse_sym_table() {
		for(String sym : sym_table.keySet()) {
			BitVecExpr address = sym_table.get(sym);
			if(address != null) {
				if(address_sym_table.containsKey(address)) {
					address_sym_table.get(address).add(sym);
				}
				else {
					ArrayList<String> sym_list = new ArrayList<String>();
					sym_list.add(sym);
					address_sym_table.put(address, sym_list);
				}
			}
		}
	}
	
	void parse_external_info(String external_info) {
        String[] lines = external_info.split("\n");
        boolean parse_start = false;
        boolean vma_addr_parsed = false;
        int vma_count = 0;
        int dll_count = 0;
        Long base_addr = null;
        int first_chunk = 0;
        Long start_address = null;
        Long vma_addr = null;
        Pattern import_table_pattern = Pattern.compile("^[0-9a-f \t]+$");
        for(String ln : lines) {
        	String line = ln.strip();
        	if(line != "") {
                if(parse_start) {
                    if(!line.startsWith("vma:  ")) {
                        String[] line_split = Utils.remove_multiple_spaces(line).split(" ");
                        String ext_name = line_split[line_split.length - 1];
                        if(ext_name != "<none>") {
                        	String extName = "dll_" + ext_name;
                            long vma = Long.valueOf(line_split[0], 16);
                            dllFuncInfo.put(vma, extName);
                        }
                        dll_count += 1;
                    }
                }
                else if(vma_addr_parsed) {
                    if(import_table_pattern.matcher(line).matches()) {
                        String[] line_split = line.split("\\s+");
                        if(vma_count == 0) {
                            vma_addr = Long.valueOf(line_split[0], 16);
                            base_addr = start_address - vma_addr;
                            first_chunk = Integer.valueOf(line_split[line_split.length-1], 16);
                        }
                        else
                            first_chunk = Integer.valueOf(line_split[line_split.length-1], 16);
                        vma_count += 1;
                    }
                }
                if(line.contains("There is an import table in "))
                    start_address = Long.valueOf(Utils.rsplit(line, " ")[1], 16);
                else if(line.startsWith("The Import Tables "))
                    vma_addr_parsed = true;
                else if(line.startsWith("DLL Name")) {
                    parse_start = true;
                    dll_count = 0;
                }
                else if(line.startsWith("PE File Base Relocation"))
                    vma_addr_parsed = false;
                else if(line.endsWith("bit words")) {
                    if(Utils.imm_pat.matcher(line).matches()) {
                        String[] line_split = line.split(" ", 1);
                        if(line_split[1] == "bit words") {
                            int addr_size = Integer.valueOf(line_split[0]);
                            Config.MEM_ADDR_SIZE = addr_size;
                        }
                    }
                }
        	}
            else
                parse_start = false;
        }
	}
}
