package normalizer;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import com.microsoft.z3.BitVecExpr;

import common.Config;
import common.Helper;
import common.InstElement;
import common.Lib;
import common.Tuple;
import common.Utils;

public class NormIDAPro implements Normalizer {
	
	String disasmPath;
	HashMap<Long, String> addressInstMap;
	HashMap<Long, Long> addressNextMap;
	HashMap<Long, String> addressLabelMap;
	HashMap<Long, String> address_func_map;
	HashMap<Long, String> addressExtFuncMap;
	HashMap<Long, ArrayList<BitVecExpr>> globalJPTEntriesMap;
	
	HashMap<String, HashMap<String, Tuple<Integer, String>>> idaStructTable;
	
	ArrayList<String> funcCallOrder;
	HashMap<String, ArrayList<Long>> func_addr_call_map = new HashMap<>(); 
	HashMap<String, ArrayList<String>> func_call_map = new HashMap<>(); 
	HashMap<String, Long> varOffsetMap;
	HashMap<String, Long> varValueMap;
	HashMap<String, Long> procValueMap;
	HashMap<String, String> varPtrRepMap;
	HashMap<Long, Boolean> addedPtrRepMap;
	HashMap<Long, String> addressLineMap;
	HashMap<String, String> varIdaStructTypeMap;
	ArrayList<String> idaStructTypes;
	HashSet<String> globalDataName;
	int valid_address_no;
	String currPtrRep;
	
	Pattern addrInstPat = Pattern.compile("^[.a-zA-Z]+:[0-9a-zA-Z]+[ ]{17}[a-zA-Z]");
	Pattern immPat = Pattern.compile("^0x[0-9a-fA-F]+$|^[0-9]+$|^-[0-9]+$|^-0x[0-9a-fA-F]+$|^[0-9a-fA-F]+$|^-[0-9a-fA-F]+$");

	Pattern varExprPat = Pattern.compile("^[.a-zA-Z_0-9]+:[0-9a-zA-Z]{16} [a-zA-Z0-9_@?$]+|^[.a-zA-Z_0-9]+:[0-9a-zA-Z]{8} [a-zA-Z0-9_@?$]+");
	Pattern idaImmPat = Pattern.compile("^[0-9A-F]+h$|^[0-9]$");
	Pattern jptStartPat = Pattern.compile("^[.a-zA-Z_0-9]+:[0-9a-zA-Z]{16} jpt_[a-zA-Z0-9_@?$]+|^[.a-zA-Z_0-9]+:[0-9a-zA-Z]{8} jpt_[a-zA-Z0-9_@?$]+");
	Pattern jptEndPat = Pattern.compile("^[.a-zA-Z_0-9]+:[0-9a-zA-Z]{16} ; [-]+|^[.a-zA-Z_0-9]+:[0-9a-zA-Z]{8} ; [-]+");

	Pattern subtractHexPat = Pattern.compile("-[0-9a-fA-F]+h");

	String[] nonInstPrefix = new String[]{"dd ", "dw", "db", "text ", "align", "assume", "public", "start", "type"};
	String[] offsetSpecPrefix = new String[]{"off_", "loc_", "byte_", "stru_", "dword_", "qword_", "unk_", "sub_", "asc_", "def_"};

	
	public NormIDAPro(String disasmPath) throws FileNotFoundException {
		this.disasmPath = disasmPath;
        addressInstMap = new HashMap<>();
        addressNextMap = new HashMap<>();
        addressLabelMap = new HashMap<>();
        addressExtFuncMap = new HashMap<>();
        varOffsetMap = new HashMap<>();
        varValueMap = new HashMap<>();
        procValueMap = new HashMap<>();
        varPtrRepMap = new HashMap<>();
        valid_address_no = 0;
        currPtrRep = null;
        globalDataName = new HashSet<>();
        globalJPTEntriesMap = new HashMap<>();
        addedPtrRepMap = new HashMap<>();
        idaStructTable = NormHelper.init_ida_struct_info();
        varIdaStructTypeMap = new HashMap<>();
        addressLineMap = new HashMap<>();
        idaStructTypes = new ArrayList<>();
        for(String s : idaStructTable.keySet()) {
        	idaStructTypes.add(s);
        }
        read_asm_info();
	}
	
	
	void readInstInfo(ArrayList<String> lines) {
		for(String line : lines) {
            if(line.contains(" extrn "))
                storeExtFuncInfo(line);
            else if(varExprPat.matcher(line).find()) {
                readVariableValue(line);
            }
            else if(locatedAtCodeSegments(line)) {
                if(!line.contains("UnwindMapEntry")) {
                    if(addrInstPat.matcher(line).find()) {
                    	Tuple<Long, String> lineInfo = parseLine(line);
                    	long address = lineInfo.x;
                    	String inst = lineInfo.y;
                        if(inst != null && !Utils.startsWith(inst, nonInstPrefix)) {
                            inst = replaceInstVarArg(address, inst, line);
                            addressInstMap.put(address, inst);
                            addressLineMap.put(address, line);
                            valid_address_no += 1;
                        }
                    }
                }
            }
		}
	}
	
	
	public HashMap<Long, ArrayList<BitVecExpr>> readGlobalJPTEntriesMap() {
		return globalJPTEntriesMap;
	}
	        

    public void read_asm_info() throws FileNotFoundException {
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
    	for(String line : lines) {
            if(locatedAtDataSegments(line)) {
                if(varExprPat.matcher(line).find()) {
                    String varName = retrieveVarName(line);
                    globalDataName.add(varName);
                }
            }
    	}
    	readInstInfo(lines);
		ArrayList<Long> instAddrs = new ArrayList<Long>(addressInstMap.keySet());
		Collections.sort(instAddrs);
		int instNum = instAddrs.size();
		long address, rip;
		String inst, instTail;
		for(int idx = 0; idx < instNum; idx++) {
			address = instAddrs.get(idx);
            int nIdx = idx + 1;
            if(nIdx < instNum)
                rip = instAddrs.get(nIdx);
            else
                rip = -1;
            inst = addressInstMap.get(address);
            if(inst.startsWith("lock ")) {
            	instTail = inst.split(" ", 2)[1].strip();
                inst = "lock " + formatInst(address, instTail);
            }
            else
                inst = formatInst(address, inst);
            addressInstMap.put(address, inst);
            addressNextMap.put(address, rip);
        }
		readGlobalJPTInfo(lines);
    }
    
    
	void readGlobalJPTInfo(ArrayList<String> lines) {
		boolean jptInfoStart = false;
    	ArrayList<BitVecExpr> jtpEntryList = null;
    	Long jptStartAddr = null;
		for(String line : lines) {
            if(jptInfoStart) {
            	if(jptEndPat.matcher(line).find()) {
            		jptInfoStart = false;
            		globalJPTEntriesMap.put(jptStartAddr, jtpEntryList);
            	}
            	else {
//            		.text:00402D34                 dd offset loc_403675
            		String[] lineSplit = Utils.remove_multiple_spaces(line).split(" ", 2);
            		readJPTEntryAddr(lineSplit[1].strip(), jtpEntryList);
            	}
            }
//            .text:004031FC jpt_4031F2      dd offset loc_403274
            if(jptStartPat.matcher(line).find()) {
            	jptInfoStart = true;
            	jtpEntryList = new ArrayList<>();
            	String[] lineSplit = Utils.remove_multiple_spaces(line).split(" ", 3);
            	jptStartAddr = Long.valueOf(lineSplit[0].split(":", 2)[1].strip(), 16);
            	readJPTEntryAddr(lineSplit[2].strip(), jtpEntryList);
            }
		}
//		System.out.println(globalJPTEntriesMap.toString());
	}

        

    void storeExtFuncInfo(String arg) {
        String line = Utils.remove_multiple_spaces(arg).strip();
        line = line.split(";", 2)[0].strip();
        String[] lineSplit = line.split(" ", 2);
        String addressStr = Utils.rsplit(lineSplit[0], ":")[1].strip();
        long address = Long.valueOf(addressStr, 16);
        String varStr = lineSplit[1].strip();
        String[] varSplit = varStr.split(" ", 2);
        String varName = Utils.rsplit(varSplit[1], ":")[0].strip();
        varValueMap.put(varName, address);
    }


    // line: .text:0000000000002050 var_E0          = dword ptr -0E0h
    void readVariableValue(String arg) {
        String line = Utils.remove_multiple_spaces(arg).strip();
        line = line.split(";", 2)[0].strip();
        String[] lineSplit = line.split(" ", 2);
        String addressStr = Utils.rsplit(lineSplit[0], ":")[1].strip();
        long address = Long.valueOf(addressStr, 16);
        String varStr = lineSplit[1].strip();
        String[] varSplit = varStr.split(" ", 2);
        String varName = varSplit[0];
        String varValue;
        if(varName.equals("LOAD")) {}
        else if(varStr.contains(" db ") || varStr.contains(" dq ") || varStr.contains(" dw ") || varStr.contains(" dd ") || varStr.contains(" dt ")) {
            String varSuffix = varSplit[1].strip().split(" ", 2)[0].strip();
            char suffix = varSuffix.charAt(varSuffix.length() - 1);
            varOffsetMap.put(varName, address);
            varValueMap.put(varName, address);
            varPtrRepMap.put(varName, NormHelper.BYTE_REP_PTR_MAP.get(suffix));
        }
        else if(varStr.contains("= "))
            parseVarValueInAssignExpr(line, varStr, address);
        else if(varName.startsWith("xmmword_")) {
            varOffsetMap.put(varName, address);
            String[] varNameSplit = Utils.rsplit(Utils.rsplit(varName, ":")[0].strip(), "_");
            if(varNameSplit.length == 2) {
                varValue = varNameSplit[1].strip();
                long value = Long.decode(varValue);
                varValueMap.put(varName, value);
                varPtrRepMap.put(varName, "xmmword ptr");
            }
        }
        else if(varStr.contains(" proc ") || varStr.contains("xmmword")) {
            varOffsetMap.put(varName, address);
            varValueMap.put(varName, address);
            if(varStr.contains(" proc "))
                procValueMap.put(varName, address);
        }
        else if(varName.endsWith(":")) {
            varName = Utils.rsplit(varName, ":")[0].strip();
            varOffsetMap.put(varName, address);
            varValueMap.put(varName, address);
        }
        else if(varSplit[0] != "" && varSplit[0].contains("stru_")) {
        	for(String idaStructType : idaStructTypes) {
            	String typeRep = " " + idaStructType + " ";
                if(varStr.contains(typeRep)) {
                    varOffsetMap.put(varName, address);
                    varValueMap.put(varName, address);
                    varIdaStructTypeMap.put(varName, idaStructType);
                    break;
                }
            }
        }
        else if(varSplit[1].strip() != "" && !varSplit[1].contains("endp") && !varSplit[1].contains("ends")) {
        	varOffsetMap.put(varName, address);
            varValueMap.put(varName, address);
        }
        else {
            for(String idaStructType : idaStructTypes) {
            	String typeRep = " " + idaStructType + " ";
                if(varStr.contains(typeRep)) {
                    varOffsetMap.put(varName, address);
                    varValueMap.put(varName, address);
                    varIdaStructTypeMap.put(varName, idaStructType);
                    break;
                }
            }
        }
    }


    Tuple<Long, String> parseLine(String line) {
    	Long address = null;
    	String inst = null;
        if(line != null) {
            String line0 = Utils.remove_multiple_spaces(line);
            String line1 = line0.split(";", 2)[0];
            String[] lineSplit = line1.split(" ", 2);
            if(lineSplit.length == 2) {
                String addressStr = Utils.rsplit(lineSplit[0], ":")[1].strip();
                address = Long.valueOf(addressStr, 16);
                inst = lineSplit[1].strip();
            }
        }
        return new Tuple<Long, String>(address, inst);
    }

    
    String replaceInstVarArg(long address, String inst, String line) {
        InstElement instElem = new InstElement(inst);
        ArrayList<String> instArgs = new ArrayList<>();
        String instName = instElem.inst_name;
        for(String arg : instElem.inst_args) {
        	instArgs.add(replaceSymbolwValue(address, instName, arg, 1));
        }
        String result = instName + " " + String.join(",", instArgs);
        result = preprocessFormatInst(result);
        return result;
    }
    
    
    String preprocessFormatInst(String inst) {
        String res = inst;
        if(inst.contains(" short "))
            res = inst.replace(" short ", " ");
        else if(inst.startsWith("lea ") && !inst.endsWith("]")) {
            String[] instSplit = Utils.rsplit(inst, ",");
            res = instSplit[0].strip() + ", " + "[" + instSplit[1] + "]";
        }
        return res;
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
        String result = postprocessFormatInst(address, inst, instElem.inst_name, instArgs);
        return result;
    }


    String replaceSymbol(String instName, String arg) {
        String symbol = arg.strip();
        String res = symbol;
        if(symbol.contains(".")) {
        	if(arg.startsWith("(") && arg.endsWith(")")) {
            	res = Utils.extract_content(symbol, "(");
            	res = handleOffsetOperation(res);
            }
            else if(arg.startsWith("offset ")) {
            	res = handleOffsetOperation(symbol);
            }
            else {
            	res = replaceIdaStructItemSymbol(symbol);
            }
        }
        else if(this.idaImmPat.matcher(symbol).matches()) {
            res = NormHelper.convertImmEndHToHex(symbol);
        }
        else if(Utils.check_jmp_with_address(instName)) {
            if(procValueMap.containsKey(symbol))
                res = Utils.num_to_hex_string(procValueMap.get(symbol));
            else if(varValueMap.containsKey(symbol)) {
                res = Utils.num_to_hex_string(varValueMap.get(symbol));
                if(varPtrRepMap.containsKey(symbol))
                    currPtrRep = varPtrRepMap.get(symbol);
            }
            else if(symbol.startsWith("loc_")) {
                String remaining = symbol.split("loc_", 2)[1].strip();
                if(immPat.matcher(remaining).matches()) {
                    res = Utils.num_to_hex_string(Long.valueOf(remaining, 16));
                }
            }
        }
        else if(varValueMap.containsKey(symbol)) {
            res = Utils.num_to_hex_string(varValueMap.get(symbol));
            if(varPtrRepMap.containsKey(symbol))
                currPtrRep = varPtrRepMap.get(symbol);
        }
        else if(symbol.startsWith("loc_")) {
        	String remaining = symbol.split("loc_", 2)[1].strip();
            if(immPat.matcher(remaining).matches()) {
                res = Utils.num_to_hex_string(Long.decode(remaining));
            }
        }
        return res;
    }


    String replaceEachSymbol(String instName, ArrayList<String> stack, ArrayList<String> opStack) {
        String res = "";
        int stackSize = stack.size();
        for(int idx = 0; idx < stackSize; idx++) {
        	String lsi = stack.get(idx);
            if(!(Lib.REG_NAMES.contains(lsi) || Utils.imm_pat.matcher(lsi).matches())) {
            	stack.set(idx, replaceSymbol(instName, lsi));
            }
        }
        res = NormHelper.reconstructFormula(stack, opStack);
        return res;
    }


    String replaceEachExpr(String instName, String content) {
        ArrayList<String> stack = new ArrayList<>();
        ArrayList<String> opStack = new ArrayList<>();
        String line = NormHelper.rmUnusedSpaces(content);
        String[] lineSplit = NormHelper.simple_op_split_pat.split(line);
        for(String lsi : lineSplit) {
            if(NormHelper.simple_operator_pat.matcher(lsi).matches()) {
                opStack.add(lsi);
            }
            else
                stack.add(lsi);
        }
        String res = replaceEachSymbol(instName, stack, opStack);
        return res;
    }


    String replaceSymbolwValue(long address, String instName, String arg, int count) {
        String res = arg;
        currPtrRep = null;
        if(arg.endsWith("]")) {
            String[] argSplit = arg.split("\\[", 2);
            String prefix = argSplit[0].strip();
            String memAddrStr = Utils.rsplit(argSplit[1].strip(), "]")[0].strip();
            String memAddr = replaceEachExpr(instName, memAddrStr);
            if(prefix.contains("ptr"))
                res = prefix + " [" + memAddr + "]";
            else if(prefix.contains("s:")) {
                String[] prefixSplit = prefix.split(":", 2);
                if(prefixSplit.length == 2) {
                    String prefixSuffix = prefixSplit[1].strip();
                    if(Utils.imm_pat.matcher(prefixSuffix).matches()) {
                        res = "[" + memAddr + "+" + prefixSuffix + "]";
                    }
                    else {
                        if(prefixSuffix.startsWith("(") && prefixSuffix.endsWith(")")) {
                            res = "[" + memAddr + "+" + Utils.extract_content(prefixSuffix, "(") + "]";
                        }
                        else if(prefixSuffix != null && prefixSuffix != "")
                            res = "[" + memAddr + "+" + prefixSuffix + "]";
                        else
                            res = "[" + memAddr + "]";
                    }
                }
                else
                    res = "[" + memAddr + "]";
            }
            else if(currPtrRep != null && currPtrRep != "") {
                addedPtrRepMap.put(address, true);
                res = currPtrRep + " [" + memAddr + "]";
            }
            else if(Utils.startsWith(prefix, offsetSpecPrefix)) {
                res = "[" + prefix + "+" + memAddr + "]";
            }
            else
                res = "[" + memAddr + "]";
        }
        else if(globalDataName.contains(arg)) {
            if(count == 2)
                res = "[" + Utils.num_to_hex_string(varValueMap.get(arg)) + "]";
        }
        else if(arg.contains(" near ptr ")) {
        	String[] argSplit = arg.split(" ptr ", 2);
        	res = replaceEachExpr(instName, argSplit[1].strip());
        }
        else if(arg.contains(" ptr ")) {
            String[] argSplit = arg.split(" ptr ", 2);
            String ptrRep = argSplit[0] + " ptr ";
            res = ptrRep + "[" + replaceEachExpr(instName, argSplit[1].strip()) + "]";
        }
        else
            res = replaceEachExpr(instName, arg);
        return res;
    }
    

    String movSegmentRep(String arg) {
        String res = arg;
        if(arg.endsWith("]") && arg.contains(":")) {
            String[] argSplit = arg.split("\\[", 2);
            String prefix = argSplit[0].strip();
            String memAddr = Utils.rsplit(argSplit[1].strip(), "]")[0].strip();
            if(memAddr.contains(":")) {
                String[] memAddrSplit = memAddr.split(":", 2);
                res = prefix + " " + memAddrSplit[0] + ":[" + memAddrSplit[1] + "]";
            }
        }
        return res.strip();
    }


    String execEval(String arg) {
        String res = arg;
        String content;
        if(arg.endsWith("]")) {
            String[] argSplit = arg.split("\\[", 2);
            String prefix = argSplit[0];
            String memAddr = Utils.rsplit(argSplit[1].strip(), "]")[0].strip();
            memAddr = NormHelper.simulateEvalExpr(memAddr);
            if(!prefix.contains("("))
                res = prefix + "[" + memAddr + "]";
            else
                res = "[" + memAddr + "]";
        }
        else if(arg.startsWith("(") && arg.endsWith(")")) {
        	content = Utils.extract_content(arg, "(");
        	content = handleOffsetOperation(content);
            res = NormHelper.simulateEvalExpr(content);
        }
        else if(arg.startsWith("offset ")) {
        	content = handleOffsetOperation(arg);
            res = NormHelper.simulateEvalExpr(content);
        }
        else {
            res = NormHelper.simulateEvalExpr(arg);
        }
        return res;
    }

    
    String removeUnusedSegReg(long address, String arg) {
        String res = arg;
        if(arg.contains("s:") && !arg.endsWith("]")) {
            String[] argSplit = arg.strip().split(":", 2);
            String prefix = argSplit[0].strip();
            String remaining = argSplit[1].strip();
            if(idaImmPat.matcher(remaining).matches()) {
                if(prefix.startsWith("large ")) {
                    if(prefix.contains(" ptr")) {
                        prefix = prefix.split(" ", 2)[1].strip();
                        String[] prefixSplit = Utils.rsplit(prefix, " ");
                        String ptrRep = prefixSplit[0];
                        String segName = prefixSplit[1];
                        res = ptrRep.strip() + " [" + segName + ":" + NormHelper.convertImmEndHToHex(remaining) + "]";
                    }
                    else {
                        prefix = prefix.split(" ", 2)[1].strip();
                        res = "[" + prefix + ":" + NormHelper.convertImmEndHToHex(remaining) + "]";
                    }
                }
                else
                    res = prefix + ":" + NormHelper.convertImmEndHToHex(remaining);
            }
            else {
                if(prefix.contains(" ptr ")) {
                    String[] prefixSplit = Utils.rsplit(prefix, " ");
                    String ptrRep = prefixSplit[0].strip();
                    res = ptrRep + " [" + remaining + "]";
                }
                else
                    res = "[" + remaining + "]";
            }
        }
        else {
            if(arg.startsWith("large ") && arg.contains(" ptr "))
                res = arg.split(" ", 2)[1].strip();
        }
        return res;
    }


    String replaceTailHexwSuffixH(String inst) {
        String res = inst;
        Matcher m = subtractHexPat.matcher(inst);
        if(m.find()) {
            String hexStr = m.group(0);
            String newHexRep = NormHelper.convertImmEndHToHex(hexStr);
            res = inst.replace(hexStr, newHexRep);
        }
        return res;
    }


    String rewriteSpecJumpInst(String instName, long address, String arg) {
        String res = arg.strip();
        if(Utils.check_jmp_with_address(instName)) {
            if(res.startsWith("$")) {
                res = res.split("$", 2)[1].strip();
                long newAddr = address + Long.decode(res);
                res = Utils.num_to_hex_string(newAddr);
            }
        }
        return res;
    }



    String postprocessFormatInst(long address, String inst, String instName, ArrayList<String> instArgs) {
        int length = 0;
        int instNum = instArgs.size();
        String arg;
        for(int idx = 0; idx < instNum; idx++) {
        	arg = instArgs.get(idx);
        	if(Lib.REG_NAMES.contains(arg)) {
                length = Utils.get_sym_length(arg);
                break;
        	}
        }
        for(int idx = 0; idx < instNum; idx++) {
        	arg = instArgs.get(idx);
            if(arg.endsWith("]") || arg.contains("s:"))
                handleIdaPtrRep(address, inst, length, instName, instArgs, idx, arg);
        }
        String newInst = instName + " " + String.join(",", instArgs);
        newInst = newInst.strip();
        newInst = replaceTailHexwSuffixH(newInst);
        return newInst;
    }


    String formatArg(long address, String instName, String arg) {
        String res = removeUnusedSegReg(address, arg);
        res = rewriteSpecJumpInst(instName, address, res);
        res = replaceSymbolwValue(address, instName, res, 2);
        res = res.replace("+-", "-");
        res = movSegmentRep(res);
        res = execEval(res);
        res = removeLeaPtrRep(instName, res);
        res = res.toLowerCase();
        res = NormHelper.convertToHexRep(res);
        return res;
    }

    String removeLeaPtrRep(String instName, String arg) {
        String res = arg;
        if(instName.equals("lea")) {
            if(arg.endsWith("]")) {
                res = "[" + arg.split("\\[", 2)[1].strip();
            }
        }
        return res;
    }
    
    
    public BitVecExpr readEachEntryAddr(String arg) {
    	BitVecExpr res = null;
    	String tmp = arg;
    	if(tmp.contains("offset")) {
			String[] aSplit = tmp.split("offset", 2);
			String a2s = aSplit[1].strip();
			if(this.varOffsetMap.containsKey(a2s)) {
				long addr = varOffsetMap.get(a2s);
				res = Helper.gen_bv_num(addr, Config.MEM_ADDR_SIZE);
			}
			else if(Utils.startsWith(a2s, offsetSpecPrefix)) {
				String addrStr = a2s.split("_", 2)[1].strip();
				res = Helper.gen_bv_num(Long.valueOf(addrStr, 16), Config.MEM_ADDR_SIZE);
			}
    	}
    	return res;
    }
	
//	dd offset def_402DF5, offset def_402DF5, offset def_402DF5 ; jump table for switch statement
    // dd offset def_402DF5
	public void readJPTEntryAddr(String arg, ArrayList<BitVecExpr> jptEntryList) {
		BitVecExpr res = null;
		String tmp = arg;
		if(arg.contains(";")) {
			tmp = tmp.split(";", 2)[0].strip();
		}
		String[] aSplit = tmp.split(",");
		for(String as : aSplit) {
			as = as.strip();
			if(as != "") {
				res = readEachEntryAddr(as);
				jptEntryList.add(res);
			}
		}
	}


    void handleIdaPtrRep(long address, String inst, int length, String instName, ArrayList<String> instArgs, int idx, String arg) {
        if(!arg.contains(" ptr ") || addedPtrRepMap.containsKey(address)) {
            String ptrRep = NormHelper.generateIdaPtrRep(instName, inst, length);
            if(ptrRep == null) {
                if(!instName.equals("lea") && !addedPtrRepMap.containsKey(address)) {
                    if(arg.endsWith("]") && !arg.contains(" ptr ") || arg.contains("s:")) {
                        if(length != 0)
                            ptrRep = NormHelper.BYTELEN_REP_MAP.get(length);
                        else if(instName.equals("movsx") || instName.equals("movzx")) {
                            ptrRep = "word ptr";
                        }
                        else
                            ptrRep = "dword ptr";
                        instArgs.set(idx, ptrRep + " " + arg);
                    }
                }
            }
            else {
                if(arg.contains("s:"))
                	instArgs.set(idx, ptrRep + " " + arg);
                else
                	instArgs.set(idx, ptrRep + " [" + arg.split("\\[", 2)[1].strip());
            }
        }
    }
      

    String replaceIdaStructItemSymbol(String symbol) {
        String res = symbol;
        String[] symbolSplit = symbol.split("\\.", 2);
        String symbolName = symbolSplit[0].strip();
        if(varIdaStructTypeMap.containsKey(symbolName)) {
            String symbolType = varIdaStructTypeMap.get(symbolName);
            String itemEntry = symbolSplit[1].strip();
            if(varValueMap.containsKey(symbolName)) {
                if(idaStructTable.containsKey(symbolType)) {
                	Tuple<Integer, String> idaOffType = retrieveIdaTypeOffsetType(symbolType, itemEntry);
                	int offset = idaOffType.x;
                	String itemType  = idaOffType.y;
                    res = Utils.num_to_hex_string(varValueMap.get(symbolName) + offset);
                    String ptrRep = NormHelper.getIdaPtrRepFromItemType(itemType);
                    if(ptrRep != null)
                        currPtrRep = ptrRep;
                }
                else {
                	System.out.println("We have not recorded the specific information for ida type " + symbolType);
                    System.exit(1);
                }
            }
        }
        return res;
    }


    void parseVarValueInAssignExpr(String line, String var_str, long address) {
        String[] varSplit = var_str.split("=", 2);
        String varName = varSplit[0].strip();
        varOffsetMap.put(varName, address);
        String varValue = varSplit[1].strip();
        String[] varValueSplit = Utils.rsplit(varValue, " ");
        String ptrRep = varValueSplit[0].strip();
        String typeSpec = ptrRep.split("ptr", 2)[0].strip();
        if(!NormHelper.BYTE_LEN_REPS.containsKey(typeSpec)) {
            if(idaStructTable.containsKey(typeSpec)) {
                varIdaStructTypeMap.put(varName, typeSpec);
            }
            else if(typeSpec.equals("LARGE_INTEGER") || typeSpec.equals("_LARGE_INTEGER")) {
                varPtrRepMap.put(varName, ptrRep);
            }
            else {
                System.out.println(line);
                System.out.println("We have not recorded the specific information for ida type " + typeSpec);
                System.exit(1);
            }
        }
        else
            varPtrRepMap.put(varName, ptrRep);
        varValue = varValueSplit[varValueSplit.length - 1].strip();
        if(varValue.endsWith("h")) {
        	long value = Long.valueOf(Utils.rsplit(varValue, "h")[0].strip(), 16);
            varValueMap.put(varName, value);
        }
        else if(Utils.imm_pat.matcher(varValue).matches()) {
            long value = Long.decode(varValue);
            varValueMap.put(varName, value);
        }
    }
        

    boolean locatedAtCodeSegments(String line) {
        return Utils.startsWith(line, Lib.CODE_SEGMENTS);
    }


    boolean locatedAtDataSegments(String line) {
        return Utils.startsWith(line, Lib.DATA_SEGMENTS);
    }


    String retrieveVarName(String arg) {
        String line = Utils.remove_multiple_spaces(arg).strip();
        String varName = line.split(" ", 3)[1].strip();
        return varName;
    }

    
    String handleOffsetOperation(String arg) {
        String content = arg;
        if(content.contains("offset ")) {
            String original = null;
            String newVar = null;
            String[] contentSplit = content.split("((?<=[^a-zA-Z0-9_.@?$]+)|(?=[^a-zA-Z0-9_.@?$]+))");
            int cNum = contentSplit.length;
            String variable, var;
            for(int idx = 0; idx < cNum; idx++) {
            	String ci = contentSplit[idx];
                if(ci.equals("offset")) {
                    if(cNum > idx + 2) {
                        variable = contentSplit[idx + 2];
                        original = "offset " + variable;
                        if(varOffsetMap.containsKey(variable))
                            newVar = Utils.num_to_hex_string(varOffsetMap.get(variable));
                        else if(variable.contains("."))
                            newVar = replaceIdaStructItemSymbol(variable);
                        else if(Utils.startsWith(variable, offsetSpecPrefix)) {
                            var = variable.split("_", 2)[1];
                            if(Utils.imm_start_pat.matcher(var).matches()) {
                                newVar = Utils.num_to_hex_string(Long.decode(var));
                            }
                        }
                    }
                    break;
                }
            }
            if(newVar != null)
                content = content.replace(original, newVar);
        }
        return content;
    }


    Tuple<Integer, String> retrieveIdaTypeOffsetType(String symbolType, String itemEntry) {
        if(itemEntry.contains(".")) {
        	String[] itemEntrySplit = itemEntry.split(".", 2);
        	String newSymType = itemEntrySplit[0];
        	String newItemEntry = itemEntrySplit[1];
        	Tuple<Integer, String> newItemInfo = idaStructTable.get(symbolType).get(newSymType);
        	int offset = newItemInfo.x;
        	String itemType = newItemInfo.y;
        	Tuple<Integer, String> idaOffsetInfo = retrieveIdaTypeOffsetType(itemType, newItemEntry);
        	int newOffset = idaOffsetInfo.x;
        	itemType = idaOffsetInfo.y;
            return new Tuple<>(offset + newOffset, itemType);
        }
        else {
        	Tuple<Integer, String> itemInfo = idaStructTable.get(symbolType).get(itemEntry);
        	int offset = itemInfo.x;
        	String itemType = itemInfo.y;
            return new Tuple<>(offset, itemType);
        }
    }


	@Override
	public HashMap<Long, String> getAddressLabelMap() {
		return this.addressLabelMap;
	}


	@Override
	public HashMap<Long, Long> getAddressNextMap() {
		return addressNextMap;
	}

	@Override
	public HashMap<Long, String> getAddressInstMap() {
		return this.addressInstMap;
	}


	@Override
	public HashMap<Long, String> getAddressExtFuncMap() {
		return this.addressExtFuncMap;
	}
            		
}
