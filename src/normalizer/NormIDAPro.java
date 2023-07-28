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

import common.Config;
import common.InstElement;
import common.Lib;
import common.Tuple;
import common.Utils;

public class NormIDAPro implements Normalizer {
	
	String disasmPath;
	static HashMap<Long, String> addressInstMap;
	static HashMap<Long, Long> addressNextMap;
	static HashMap<Long, String> addressSymTable;
	static HashMap<String, Long> symTable;
	static HashMap<Long, String> addressExtFuncMap;
	static HashSet<Long> funcEndAddressSet;
	static HashMap<Long, ArrayList<Long>> globalJPTEntriesMap;
	
	static Long entryAddress = null; 
	static Long mainAddress = null;
	
	static HashMap<String, Long> secStartAddrMap;
	
	HashMap<String, HashMap<String, Tuple<Integer, String>>> idaStructTable;
	
	HashMap<String, Long> varOffsetMap;
	HashMap<String, Long> varValueMap;
	HashMap<String, Long> procValueMap;
	HashMap<String, String> varPtrRepMap;
	HashSet<Long> addedPtrRepMap;
	HashMap<String, String> varIdaStructTypeMap;
	ArrayList<String> idaStructTypes;
	HashSet<String> globalDataName;
	String currPtrRep;
	
	Pattern addrInstPat = Pattern.compile("^[.a-zA-Z0-9_]+:[0-9a-fA-F]+[ ]{17}[a-zA-Z]");
	Pattern immPat = Pattern.compile("^0x[0-9a-fA-F]+$|^[0-9]+$|^-[0-9]+$|^-0x[0-9a-fA-F]+$|^[0-9a-fA-F]+$|^-[0-9a-fA-F]+$");

	Pattern varExprPat = Pattern.compile("^[.a-zA-Z_0-9]+:[0-9a-fA-F]{16} [a-zA-Z0-9_@?$]+|^[.a-zA-Z_0-9]+:[0-9a-fA-F]{8} [a-zA-Z0-9_@?$]+");
	Pattern idaImmPat = Pattern.compile("^[0-9A-F]+h$|^[0-9]$");
	Pattern jptStartPat = Pattern.compile("^[.a-zA-Z_0-9]+:[0-9a-zA-Z]{16} jpt_[a-zA-Z0-9_@?$]+|^[.a-zA-Z_0-9]+:[0-9a-zA-Z]{8} jpt_[a-zA-Z0-9_@?$]+");
	Pattern jptEndPat = Pattern.compile("^[.a-zA-Z_0-9]+:[0-9a-zA-Z]{16} ; [-]+|^[.a-zA-Z_0-9]+:[0-9a-zA-Z]{8} ; [-]+");
	Pattern idaWordRepPat = Pattern.compile("^byte_[0-9a-fA-F]+$|^word_[0-9a-fA-F]+$|^dword_[0-9a-fA-F]+$|^qword_[0-9a-fA-F]+$|^tbyte_[0-9a-fA-F]+$|^xmmword_[0-9a-fA-F]+$");
	
	Pattern subtractHexPat = Pattern.compile("-[0-9a-fA-F]+h");

	String[] nonInstPrefix = new String[]{"dd ", "dw ", "db ", "dq ", "dt ", "text ", "align", "_start", "start", "type"};
	String[] offsetSpecPrefix = new String[]{"off_", "loc_", "byte_", "stru_", "dword_", "qword_", "unk_", "sub_", "asc_", "def_", "xmmword_", "word_"};
	String[] nonValidInstInfo = new String[]{"UnwindMapEntry", " assume ", " public "};	
	String[] preProcKeyword = new String[] {" extrn ", " proc "};
	
	public NormIDAPro(String disasmPath) throws FileNotFoundException {
		this.disasmPath = disasmPath;
        addressInstMap = new HashMap<>();
        addressNextMap = new HashMap<>();
        addressSymTable = new HashMap<>();
        symTable = new HashMap<>();
        addressExtFuncMap = new HashMap<>();
        funcEndAddressSet = new HashSet<>();
        globalJPTEntriesMap = new HashMap<>();
        
        secStartAddrMap = new HashMap<>();
        
        varOffsetMap = new HashMap<>();
        varValueMap = new HashMap<>();
        procValueMap = new HashMap<>();
        varPtrRepMap = new HashMap<>();
        currPtrRep = null;
        globalDataName = new HashSet<>();
        addedPtrRepMap = new HashSet<>();
        idaStructTable = NormHelper.init_ida_struct_info();
        varIdaStructTypeMap = new HashMap<>();
        idaStructTypes = new ArrayList<>();
        for(String s : idaStructTable.keySet()) {
        	idaStructTypes.add(s);
        }
        readASMInfo();
        readBinaryInfo();
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
    	for(String line : lines) {
    		if(line.contains("; Segment type:")) {
    			storeSecStartAddr(line);
    		}
    		// line: extern:000000000021C718                 extrn abort:near        ; CODE XREF: _abort↑j
    		else if(line.contains(" extrn ")) {
    			storeFuncInfo(line, "extrn");
    		}
    		// line: .text:08000034 free_g2         proc near
            else if(line.contains(" proc ")) {
            	storeFuncInfo(line, "proc");
            }
    		else if(locatedAtDataSegments(line)) {
                if(varExprPat.matcher(line).find()) {
                	saveGlobalVarInfo(line);
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
//            System.out.println(inst);
            addressInstMap.put(address, inst);
            addressNextMap.put(address, rip);
        }
		readGlobalJPTInfo(lines);
    }
    
    
    void saveGlobalVarInfo(String arg) {
		String line = Utils.remove_multiple_spaces(arg).strip();
        line = line.split(";", 2)[0].strip();
        String[] lineSplit = line.split(" ", 2);
        long address = Long.valueOf(Utils.rsplit(lineSplit[0], ":")[1].strip(), 16);
        String varName = lineSplit[1].strip().split(" ", 2)[0];
        globalDataName.add(varName);
        varOffsetMap.put(varName, address);	
	}


	void readBinaryInfo() {
		if(procValueMap.containsKey("_start")) {
    		entryAddress = procValueMap.get("_start");
        }
		else if(procValueMap.containsKey("start")) {
    		entryAddress = procValueMap.get("start");
        }
        if(procValueMap.containsKey("main")) {
        	mainAddress = procValueMap.get("main");
        }
	}
    
	// line: .text:00401000 ; Segment type: Pure code
	// Read the start address information for .text section
	void storeSecStartAddr(String line) {
		String[] lineSplit = line.strip().split(" ", 2);
		String[] secNameAddrSplit = Utils.rsplit(lineSplit[0].strip(), ":");
		String secName = secNameAddrSplit[0].strip();
		String addrStr = secNameAddrSplit[1].strip();
        long address = Long.valueOf(addrStr, 16);
        secStartAddrMap.put(secName, address);
	}
	
	
	void readInstInfo(ArrayList<String> lines) {
		for(String line : lines) {
            if(Utils.contains(line, preProcKeyword)) {}
            else if(varExprPat.matcher(line).find()) {
                readVariableValue(line);
            }
            else if(locatedAtCodeSegments(line) && !Utils.contains(line, nonValidInstInfo)) {
                if(addrInstPat.matcher(line).find()) {
                	parseInstInfo(line);
                }
            }
		}
	}
	
	
	void parseInstInfo(String line) {
		Tuple<Long, String> lineInfo = parseLine(line);
    	long address = lineInfo.x;
    	String inst = lineInfo.y;
        if(inst != null && !Utils.startsWith(inst, nonInstPrefix)) {
            inst = replaceInstVarArg(address, inst, line);
            addressInstMap.put(address, inst);
        }
	}
    
    
	void readGlobalJPTInfo(ArrayList<String> lines) {
		boolean jptInfoStart = false;
    	ArrayList<Long> jtpEntryList = null;
    	Long jptStartAddr = null;
		for(String line : lines) {
            if(jptInfoStart) {
            	if(jptEndPat.matcher(line).find()) {
            		jptInfoStart = false;
            		globalJPTEntriesMap.put(jptStartAddr, jtpEntryList);
            	}
            	else {
            		// line: .text:00402D34                 dd offset loc_403675
            		String[] lineSplit = Utils.remove_multiple_spaces(line).split(" ", 2);
            		if(lineSplit.length > 1 && lineSplit[1].strip() != "")
            			readJPTEntryAddr(lineSplit[1].strip(), jtpEntryList);
            	}
            }
            // line: .text:004031FC jpt_4031F2      dd offset loc_403274
            if(jptStartPat.matcher(line).find()) {
            	jptInfoStart = true;
            	jtpEntryList = new ArrayList<>();
            	String[] lineSplit = Utils.remove_multiple_spaces(line).split(" ", 3);
            	jptStartAddr = Long.valueOf(lineSplit[0].split(":", 2)[1].strip(), 16); //0x4031FC
            	readJPTEntryAddr(lineSplit[2].strip(), jtpEntryList);
            }
		}
	}    
    
	
	// arg: extern:000000000021C718                 extrn abort:near
    void storeFuncInfo(String arg, String funcType) {
        String line = Utils.remove_multiple_spaces(arg).strip();
        line = line.split(";", 2)[0].strip();
        String[] lineSplit = line.split(" ", 2);
        long address = Long.valueOf(Utils.rsplit(lineSplit[0], ":")[1].strip(), 16);
        String varName = null;
        if(funcType == "extrn") {
        	varName = lineSplit[1].strip().split("extrn ", 2)[1].strip();
        	varName = Utils.rsplit(varName, ":")[0].strip();
        	addressExtFuncMap.put(address, varName);
        }
        else if(line.startsWith(".plt")) {
        	//arg: .plt:00001060 _malloc         proc near
        	varName = lineSplit[1].strip().split(" ", 2)[0].strip();
        	addressExtFuncMap.put(address, varName);
        }
        else {
        	//arg: .text:0000000000012720 rpl_fts_open    proc near
        	varName = lineSplit[1].strip().split(" ", 2)[0].strip();
        	procValueMap.put(varName, address);
        }
        varValueMap.put(varName, address);
        varOffsetMap.put(varName, address);
        addressSymTable.put(address, varName);
        symTable.put(varName, address);
    }

    
    // Read local or global variable information
    // line: .text:0000000000002050 var_E0          = dword ptr -0E0h
    // line: .got:0800026C _GLOBAL_OFFSET_TABLE_ dd 0
    void readVariableValue(String arg) {
        String line = Utils.remove_multiple_spaces(arg).strip();
        line = line.split(";", 2)[0].strip();
        String[] lineSplit = line.split(" ", 2);
        String[] secNameAddrSplit = Utils.rsplit(lineSplit[0], ":");	//.text:0000000000002050
        String addressStr = secNameAddrSplit[1].strip();		//0000000000002050
        long address = Long.valueOf(addressStr, 16);
        String varStr = lineSplit[1].strip();		//_GLOBAL_OFFSET_TABLE_ dd 0
        String[] varSplit = varStr.split(" ", 2);
        String varName = varSplit[0];
        if(varName.equals("LOAD") || varStr.contains("segment dword ")) {}
        // line: .got:0800026C _GLOBAL_OFFSET_TABLE_ dd 0
        // line: .bss:08000144 g               dd ?
        else if(Utils.contains(varStr, NormHelper.IDAWordTypes))
        	parseIDATypeVarValue(secNameAddrSplit[0].strip(), varName, varSplit[1], address);
        // line: .text:08000034 var_4           = dword ptr -4
        else if(varStr.contains("= "))
            parseVarValueInAssignExpr(line, varStr, address);
        // line: .text:0000000000005CEE loc_5CEE:
        else if(varName.endsWith(":")) {
            varName = Utils.rsplit(varName, ":")[0].strip();
            varOffsetMap.put(varName, address);
            varValueMap.put(varName, address);
        }
        // line: .text:004012EF stru_4012EF     FILE <65736162h, 656D616Eh, 65002B00h>
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
        // line: .text:0800013F main            endp
        else if(varSplit[1].strip() != "" && varSplit[1].contains("endp")) {
        	funcEndAddressSet.add(address);
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

    
    // Preprocess the IDAPro instructions
    String replaceInstVarArg(long address, String inst, String line) {
        InstElement instElem = new InstElement(inst);
        ArrayList<String> instArgs = new ArrayList<>();
        String instName = instElem.inst_name;
        for(String arg : instElem.inst_args) {
        	// Replace symbolic operand with local concrete value
        	instArgs.add(replaceSymbolWValue(address, instName, arg, 1));
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


    String replaceSymbol(long address, String instName, String arg) {
    	String symbol = arg.strip();
        String res = symbol;
        // symbol is IDA struct type
        // symbol: offset stru_4012EF._base
        if(symbol.contains(".")) {
        	// (offset stru_4012EF._base+1)
        	if(arg.startsWith("(") && arg.endsWith(")")) {
            	res = Utils.extract_content(symbol, "(");
            	res = handleOffsetOperation(res);
            }
        	// offset stru_4012EF
            else if(arg.startsWith("offset ")) {
            	res = handleOffsetOperation(symbol);
            }
            else {
            	res = replaceIdaStructItemSymbol(symbol);
            }
        }
        // symbol: 38h
        else if(idaImmPat.matcher(symbol).matches()) {
            res = NormHelper.convertImmEndHToHex(symbol);
        }
        // symbol: offset dword_406140
        else if(arg.startsWith("offset ")) {
        	res = handleOffsetOperation(symbol);
        }
        else if(Utils.check_jmp_with_address(instName)) {
        	// The symbol represents an internal function name
            if(procValueMap.containsKey(symbol))
                res = Utils.toHexString(procValueMap.get(symbol)); //Replace the symbol with the function address
            // The symbol is parsed and stored in varValueMap
            else if(varValueMap.containsKey(symbol)) {
                res = Utils.toHexString(varValueMap.get(symbol));
                if(varPtrRepMap.containsKey(symbol))
                    currPtrRep = varPtrRepMap.get(symbol);
            }
            else if(symbol.startsWith("loc_")) {
                String remaining = symbol.split("loc_", 2)[1].strip();
                if(immPat.matcher(remaining).matches()) {
                    res = Utils.toHexString(Long.valueOf(remaining, 16));
                }
            }
        }
        else if(varValueMap.containsKey(symbol)) {
            res = Utils.toHexString(varValueMap.get(symbol));
            if(varPtrRepMap.containsKey(symbol))
                currPtrRep = varPtrRepMap.get(symbol);
        }
        else if(symbol.startsWith("loc_")) {
        	String remaining = symbol.split("loc_", 2)[1].strip();
            if(immPat.matcher(remaining).matches()) {
                res = Utils.toHexString(Long.decode(remaining));
            }
        }
        else if(symbol.equals("$")) {
        	res = "0x" + Long.toHexString(address);
        }
        return res;
    }


    String replaceEachSymbol(long address, String instName, ArrayList<String> stack, ArrayList<String> opStack) {
        String res = "";
        int stackSize = stack.size();
        for(int idx = 0; idx < stackSize; idx++) {
        	String lsi = stack.get(idx);
            if(!(Lib.REG_NAMES.contains(lsi) || Utils.imm_pat.matcher(lsi).matches())) {
            	stack.set(idx, replaceSymbol(address, instName, lsi));
            }
        }
        res = NormHelper.reconstructFormula(stack, opStack);
        return res;
    }


    String replaceEachExpr(long address, String instName, String content) {
        ArrayList<String> stack = new ArrayList<>();
        ArrayList<String> opStack = new ArrayList<>();
        String line = Utils.rmUnusedSpaces(content);
        String[] lineSplit = NormHelper.simple_op_split_pat.split(line);
        for(String lsi : lineSplit) {
            if(NormHelper.simple_operator_pat.matcher(lsi).matches()) {
                opStack.add(lsi);
            }
            else
                stack.add(lsi);
        }
        String res = replaceEachSymbol(address, instName, stack, opStack);
        return res;
    }


    /***
     * Replace some of the symbols with concrete values
     * @param address: the address of the instruction
     * @param instName: instruction operator
     * @param arg: the operand of the instruction that needs to be handled
     * @param count: a counter that indicates the time that the instruction is processed (pre- or post- processed)
     * @return the handled instruction operand
     */
    String replaceSymbolWValue(long address, String instName, String arg, int count) {
        String res = arg;
        currPtrRep = null;
        if(arg.endsWith("]")) {
            String[] argSplit = arg.split("\\[", 2);
            String prefix = argSplit[0].strip();
            String memAddrStr = Utils.rsplit(argSplit[1].strip(), "]")[0].strip();
            String memAddr = replaceEachExpr(address, instName, memAddrStr);
            // arg: byte ptr [edi]
            if(prefix.contains("ptr") && !prefix.contains("s:"))
                res = prefix + " [" + memAddr + "]";
            // arg: byte ptr gs:[esi]
            else if(prefix.contains("ptr") && prefix.contains("s:"))
                res = prefix + "[" + memAddr + "]";
            // arg: ds:jpt_402D2D[edx*4]
            else if(prefix.contains("s:")) {
                String[] prefixSplit = prefix.split(":", 2);
                if(prefixSplit.length == 2) {
                    String prefixSuffix = prefixSplit[1].strip();
                    // prefixSuffix: 314320,
                    if(Utils.imm_pat.matcher(prefixSuffix).matches()) {
                        res = "[" + memAddr + "+" + prefixSuffix + "]";
                    }
                    else {
                    	// prefixSuffix: (n - _GLOBAL_OFFSET_TABLE_)
                        if(prefixSuffix.startsWith("(") && prefixSuffix.endsWith(")")) {
                            res = "[" + memAddr + "+" + Utils.extract_content(prefixSuffix, "(") + "]";
                        }
                        // prefixSuffix: jpt_402D2D
                        else if(prefixSuffix != null && prefixSuffix != "")
                            res = "[" + memAddr + "+" + prefixSuffix + "]";
                        else
                            res = "[" + memAddr + "]";
                    }
                }
                // arg: fs:[ecx+ebp*2+6Fh]
                else
                    res = "[" + memAddr + "]";
            }
            // The value of currPtrRep will be set when replaceSymbol function (the same instruction) is called
            else if(currPtrRep != null && currPtrRep != "") {
                addedPtrRepMap.add(address);
                res = currPtrRep + " [" + memAddr + "]";
            }
            else if(Utils.startsWith(prefix, offsetSpecPrefix)) {
                res = "[" + prefix + "+" + memAddr + "]";
            }
            else if(prefix.startsWith("(") && prefix.endsWith(")"))
                res = "[" + memAddr + "+" + Utils.extract_content(prefix, "(") + "]";
            else
                res = "[" + memAddr + "]";
        }
        else if(globalDataName.contains(arg)) {
            if(count == 2)
                res = "[" + Utils.toHexString(varValueMap.get(arg)) + "]";
        }
        else if(arg.contains(" near ptr ")) {
        	String[] argSplit = arg.split(" ptr ", 2);
        	res = replaceEachExpr(address, instName, argSplit[1].strip());
        }
        else if(arg.contains(" ptr ")) {
            String[] argSplit = arg.split(" ptr ", 2);
            String ptrRep = argSplit[0] + " ptr ";
            res = ptrRep + "[" + replaceEachExpr(address, instName, argSplit[1].strip()) + "]";
        }
        else if(arg.startsWith("(") && arg.endsWith(")")) {
        	String argContent = Utils.extract_content(arg, "(");
        	res = replaceEachExpr(address, instName, argContent);
        }
        else
            res = replaceEachExpr(address, instName, arg);
        return res;
    }
    

    String movSegmentRep(String arg) {
        String res = arg;
        if(res.endsWith("]") && res.contains(":")) {
            String[] argSplit = res.split("\\[", 2);
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
                else {
                	if(prefix.contains(" ptr")) {
                        String[] prefixSplit = Utils.rsplit(prefix, " ");
                        String ptrRep = prefixSplit[0];
                        String segName = prefixSplit[1];
                        res = ptrRep.strip() + " [" + segName + ":" + NormHelper.convertImmEndHToHex(remaining) + "]";
                    }
                	else
                		res = prefix + ":" + NormHelper.convertImmEndHToHex(remaining);
                }
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
            if(res.startsWith("$+")) {
                res = res.split("$", 2)[1].strip();
                long newAddr = address + Long.decode(res);
                res = Utils.toHexString(newAddr);
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
                length = Utils.getSymLength(arg);
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
        newInst = removeSegRep(newInst);
        return newInst;
    }
    
    
    String removeSegRep(String inst) {
    	String res = inst;
	    if(inst.contains("s:")) {
	    	res = res.replace("ss:", "");
	    	res = res.replace("es:", "");
	    	res = res.replace("cs:", "");
	    	res = res.replace("ds:", "");
    	}
    	return res;
    }


    String formatArg(long address, String instName, String arg) {
        String res = removeUnusedSegReg(address, arg);
        res = rewriteSpecJumpInst(instName, address, res);
        res = replaceSymbolWValue(address, instName, res, 2);
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
    
    
    public Long readEachEntryAddr(String arg) {
    	Long res = null;
    	String tmp = arg;
    	if(tmp.contains("offset")) {
			String[] aSplit = tmp.split("offset", 2);
			String a2s = aSplit[1].strip();
			if(this.varOffsetMap.containsKey(a2s)) {
				long addr = varOffsetMap.get(a2s);
				res = addr;
			}
			else if(Utils.startsWith(a2s, offsetSpecPrefix)) {
				String addrStr = a2s.split("_", 2)[1].strip();
				res = Long.valueOf(addrStr, 16);
			}
    	}
    	return res;
    }
	
//	dd offset def_402DF5, offset def_402DF5, offset def_402DF5 ; jump table for switch statement
    // dd offset def_402DF5
	public void readJPTEntryAddr(String arg, ArrayList<Long> jptEntryList) {
		Long res = null;
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
        if(!arg.contains(" ptr ") || addedPtrRepMap.contains(address)) {
            String ptrRep = NormHelper.generateIdaPtrRep(instName, inst, length);
            if(ptrRep == null) {
                if(!instName.equals("lea") && !addedPtrRepMap.contains(address)) {
                    if((arg.endsWith("]") || arg.contains("s:")) && !arg.contains(" ptr ")) {
                        if(length != 0)
                            ptrRep = NormHelper.BYTELEN_REP_MAP.get(length);
                        else if(instName.equals("movsx") || instName.equals("movzx")) {
                            ptrRep = "word ptr";
                        }
                        else
                            ptrRep = NormHelper.BYTELEN_REP_MAP.get(Config.MEM_ADDR_SIZE);
                    }
                }
            }
            if(ptrRep != null) {
            	if(arg.contains("s:") && !arg.endsWith("]")) {
            		String[] argSplit = arg.split(":", 2);
            		instArgs.set(idx, ptrRep + " " + argSplit[0].strip() + ":[" + argSplit[1].strip() + "]");
            	}
                else if(arg.contains("s:"))
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
                    res = Utils.toHexString(varValueMap.get(symbolName) + offset);
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
    
    
    // secName:.got, varName: _GLOBAL_OFFSET_TABLE_, varInfo: dd 0, address: 0x0800026C
    // secName:.bss, varName: g, varInfo: dd ?, address: 0x08000124    
    void parseIDATypeVarValue(String secName, String varName, String varInfo, long address) {
    	String[] varInfoSplit = varInfo.strip().split(" ", 2);
    	String varType = varInfoSplit[0].strip();
        String varValue = varInfoSplit[1].strip();
        if(varValue.contains(",")) {
        	String[] varValueSplit = varValue.split(",");
        	varValue = varValueSplit[0];
        }
        varOffsetMap.put(varName, address);
        // varValue: 0
        // varInfo: dd 0FA0h
        if(idaImmPat.matcher(varValue).find())
        	varValueMap.put(varName, NormHelper.convertImmToLong(varValue));
        // line: .text:00401290 off_401290      dd offset dword_401280
        else if(varValue.startsWith("offset ") && !varName.startsWith("jpt_")) {
    		String tmp = varValue.split(" ", 2)[1].strip();
    		if(varOffsetMap.containsKey(tmp)) {
    			varValueMap.put(varName, varOffsetMap.get(tmp));
    		}
    		else
	    		varValueMap.put(varName, address);
    	}
        else if(varValue.startsWith("'") && varValue.endsWith("'")) {
        	varValueMap.put(varName, (long) varValue.charAt(0));
        }
        // varName: xmmword_24F9E
        else if(idaWordRepPat.matcher(varName).find()) {
    		String[] varNameSplit = Utils.rsplit(varName, "_");
			varValue = varNameSplit[1].strip();
			varValueMap.put(varName, Utils.imm_str_to_int(varValue));
    	}
        else {
	    		// In doubt, could be modified later
	    		varValueMap.put(varName, address);
    	}
        varPtrRepMap.put(varName, NormHelper.IDA_BYTEREP_PTR_MAP.get(varType));
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
        return Utils.startsWith(line, Lib.CODE_SECTIONS);
    }


    boolean locatedAtDataSegments(String line) {
        return Utils.startsWith(line, Lib.DATA_SECTIONS);
    }

    
    // Replace the offset of a symbol with the concrete offset value
    String handleOffsetOperation(String arg) {
        String content = arg;
        if(content.contains("offset ")) {
            String original = null;
            String newVar = null;
            // Split the content according to specific operators, such as +, -, *
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
                            newVar = Utils.toHexString(varOffsetMap.get(variable));
                        // variable: stru_4012EF._base
                        else if(variable.contains("."))
                            newVar = replaceIdaStructItemSymbol(variable);
                        // variable: off_40502C
                        else if(Utils.startsWith(variable, offsetSpecPrefix)) {
                            var = variable.split("_", 2)[1];
                            if(Utils.imm_start_pat.matcher(var).matches()) {
                                newVar = Utils.toHexString(Long.decode(var));
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
        	String[] itemEntrySplit = itemEntry.split("\\.", 2);
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
	public HashMap<Long, Long> getAddressNextMap() {
		return addressNextMap;
	}

	@Override
	public HashMap<Long, String> getAddressInstMap() {
		return addressInstMap;
	}


	@Override
	public HashMap<Long, String> getAddressExtFuncMap() {
		return addressExtFuncMap;
	}
	
	@Override
	public HashMap<Long, ArrayList<Long>> readGlobalJPTEntriesMap() {
		return globalJPTEntriesMap;
	}
	
	@Override
	public HashSet<Long> getFuncEndAddrSet() {
		return funcEndAddressSet;
	}

	
	@Override
	public Long getMainAddress() {
		return mainAddress;
	}


	@Override
	public Long getEntryAddress() {
		return entryAddress;
	}


	@Override
	public HashMap<Long, String> getAddressSymTbl() {
		return addressSymTable;
	}


	@Override
	public HashMap<String, Long> getSymTbl() {
		return symTable;
	}


	@Override
	public HashMap<String, Long> getSecStartAddrMap() {
		return secStartAddrMap;
	}
            		
}
