package normalizer;

import java.io.File;
import java.io.FileNotFoundException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Scanner;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import common.InstElement;
import common.Lib;
import common.Tuple;
import common.Utils;
import common.Helper;

public class NormalizerIDAPro implements Normalizer {
	
	String disasmPath;
	HashMap<Long, String> addressInstMap;
	HashMap<Long, Long> addressNextMap;
	HashMap<Long, String> addressLabelMap;
	HashMap<Long, String> address_func_map;
	HashMap<Long, String> addressExtFuncMap;
	
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

	Pattern subtractHexPat = Pattern.compile("-[0-9a-fA-F]+h");

	String[] nonInstPrefix = new String[]{"dd ", "dw", "db", "text ", "align", "assume", "public", "start", "type"};
	String[] offsetSpecPrefix = new String[]{"off_", "loc_", "byte_", "stru_", "dword_", "qword_", "unk_", "sub_", "asc_", "def_"};

	
	public NormalizerIDAPro(String disasmPath) throws FileNotFoundException {
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
        addedPtrRepMap = new HashMap<>();
        idaStructTable = Utils.init_ida_struct_info();
        varIdaStructTypeMap = new HashMap<>();
        addressLineMap = new HashMap<>();
        idaStructTypes = (ArrayList<String>) idaStructTable.keySet();
        read_asm_info();
	}
	        

    public void read_asm_info() throws FileNotFoundException {
    	File f = new File(disasmPath);
		Scanner sn = new Scanner(f);
		ArrayList<String> lines = new ArrayList<>();
		while (sn.hasNextLine()) {
	        String line = sn.nextLine();
            line = line.strip();
            lines.add(line);
		}
		for(String line : lines) {
            if(locatedAtDataSegments(line)) {
                if(varExprPat.matcher(line).matches()) {
                    String varName = retrieveVarName(line);
                    globalDataName.add(varName);
                }
            }
		}
		for(String line : lines) {
            if(line.contains(" extrn "))
                storeExtFuncInfo(line);
            else if(varExprPat.matcher(line).matches()) {
                readVariableValue(line);
            }
            else if(locatedAtCodeSegments(line)) {
                if(!line.contains("UnwindMapEntry")) {
                    if(addrInstPat.matcher(line).matches()) {
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
		ArrayList<Long> instAddrs = (ArrayList<Long>) addressInstMap.keySet();
		Collections.sort(instAddrs);
		int instNum = instAddrs.size();
		long address, rip;
		String inst, line, instTail;
		for(int idx = 0; idx < instNum; idx++) {
			address = instAddrs.get(idx);
            int nIdx = idx + 1;
            if(nIdx < instNum)
                rip = instAddrs.get(nIdx);
            else
                rip = -1;
            inst = addressInstMap.get(address);
            line = addressLineMap.get(address);
            if(inst.startsWith("lock ")) {
            	instTail = inst.split(" ", 1)[1].strip();
                inst = "lock " + formatInst(address, instTail);
            }
            else
                inst = formatInst(address, inst);
            addressInstMap.put(address, inst);
            addressNextMap.put(address, rip);
        }
    }

        

    void storeExtFuncInfo(String arg) {
        String line = Utils.remove_multiple_spaces(arg).strip();
        line = line.split(";", 1)[0].strip();
        String[] lineSplit = line.split(" ", 1);
        String addressStr = Utils.rsplit(lineSplit[0], ":")[1].strip();
        long address = Long.valueOf(addressStr, 16);
        String varStr = lineSplit[1].strip();
        String[] varSplit = varStr.split(" ", 1);
        String varName = Utils.rsplit(varSplit[1], ":")[0].strip();
        varValueMap.put(varName, address);
    }


    // line: .text:0000000000002050 var_E0          = dword ptr -0E0h
    void readVariableValue(String arg) {
        String line = Utils.remove_multiple_spaces(arg).strip();
        line = line.split(";", 1)[0].strip();
        String[] lineSplit = line.split(" ", 1);
        String addressStr = Utils.rsplit(lineSplit[0], ":")[1].strip();
        long address = Long.valueOf(addressStr, 16);
        String varStr = lineSplit[1].strip();
        String[] varSplit = varStr.split(" ", 1);
        String varName = varSplit[0];
        String varValue;
        if(varName == "LOAD") {}
        else if(varStr.contains(" db ") || varStr.contains(" dq ") || varStr.contains(" dw ") || varStr.contains(" dd ") || varStr.contains(" dt ")) {
            String varSuffix = varSplit[1].strip().split(" ", 1)[0].strip();
            char suffix = varSuffix.charAt(varSuffix.length() - 1);
            varOffsetMap.put(varName, address);
            varValueMap.put(varName, address);
            varPtrRepMap.put(varName, Helper.BYTE_REP_PTR_MAP.get(suffix));
        }
        else if(varStr.contains("= "))
            parseVarValueInAssignExpr(line, varStr, address);
        else if(varName.startsWith("xmmword_")) {
            varOffsetMap.put(varName, address);
            String[] varNameSplit = Utils.rsplit(Utils.rsplit(varName, ":")[0].strip(), "_");
            if(varNameSplit.length == 2) {
                varValue = varNameSplit[1].strip();
                long value = Long.valueOf(varValue, 16);
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
            String line1 = line0.split(";", 1)[0];
            String[] lineSplit = line1.split(" ", 1);
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
        if(symbol.contains("."))
            res = replaceIdaStructItemSymbol(symbol);
        else if(this.idaImmPat.matcher(symbol).matches()) {
            res = Utils.convertImmEndHToHex(symbol);
        }
        else if(Utils.check_jmp_with_address(instName)) {
            if(procValueMap.containsKey(symbol))
                res = Long.toHexString(procValueMap.get(symbol));
            else if(varValueMap.containsKey(symbol)) {
                res = Long.toHexString(varValueMap.get(symbol));
                if(varPtrRepMap.containsKey(symbol))
                    currPtrRep = varPtrRepMap.get(symbol);
            }
            else if(symbol.startsWith("loc_")) {
                String remaining = symbol.split("loc_", 1)[1].strip();
                if(immPat.matcher(remaining).matches()) {
                    res = Integer.toHexString(Integer.valueOf(remaining, 16));
                }
            }
        }
        else if(varValueMap.containsKey(symbol)) {
            res = Long.toHexString(varValueMap.get(symbol));
            if(varPtrRepMap.containsKey(symbol))
                currPtrRep = varPtrRepMap.get(symbol);
        }
        else if(symbol.startsWith("loc_")) {
        	String remaining = symbol.split("loc_", 1)[1].strip();
            if(immPat.matcher(remaining).matches()) {
                res = Integer.toHexString(Integer.valueOf(remaining, 16));
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
                stack.add(idx, replaceSymbol(instName, lsi));
            }
        }
        res = Helper.reconstructFormula(stack, opStack);
        return res;
    }


    String replaceEachExpr(String instName, String content) {
        ArrayList<String> stack = new ArrayList<>();
        ArrayList<String> opStack = new ArrayList<>();
        String line = Helper.rmUnusedSpaces(content);
        String[] lineSplit = Helper.simple_operator_pat.split(line);
        for(String lsi : lineSplit) {
            if(Helper.simple_operator_pat.matcher(lsi).matches()) {
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
        String currPtrRep = null;
        if(arg.endsWith("]")) {
            String[] argSplit = arg.split("[", 1);
            String prefix = argSplit[0].strip();
            String memAddrStr = Utils.rsplit(argSplit[1].strip(), "]")[0].strip();
            String memAddr = replaceEachExpr(instName, memAddrStr);
            if(prefix.contains("ptr"))
                res = prefix + " [" + memAddr + "]";
            else if(prefix.contains("s:")) {
                String[] prefixSplit = prefix.split(":", 1);
                if(prefixSplit.length == 2) {
                    String prefixSuffix = prefixSplit[1].strip();
                    if(Utils.imm_pat.matcher(prefixSuffix).matches()) {
                        res = "[" + memAddr + "+" + prefixSuffix + "]";
                    }
                    else {
                        if(prefixSuffix.startsWith("(") && prefixSuffix.endsWith(")")) {
                            res = "[" + memAddr + "+" + Utils.extract_content(prefixSuffix, "(") + "]";
                        }
                        else if(prefixSuffix != null)
                            res = "[" + memAddr + "+" + prefixSuffix + "]";
                        else
                            res = "[" + memAddr + "]";
                    }
                }
                else
                    res = "[" + memAddr + "]";
            }
            else if(currPtrRep != null) {
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
                res = "[" + Long.toHexString(varValueMap.get(arg)) + "]";
        }
        else if(arg.contains(" ptr ")) {
            String[] argSplit = arg.split(" ptr ", 1);
            String ptrRep = argSplit[0] + " ptr ";
            res = ptrRep + "[" + replaceSymbol(instName, argSplit[1].strip()) + "]";
        }
        else
            res = replaceSymbol(instName, arg);
        return res;
    }
    

    String movSegmentRep(String arg) {
        String res = arg;
        if(arg.endsWith("]") && arg.contains(":")) {
            String[] argSplit = arg.split("[", 1);
            String prefix = argSplit[0].strip();
            String memAddr = Utils.rsplit(argSplit[1].strip(), "]")[0].strip();
            if(memAddr.contains(":")) {
                String[] memAddrSplit = memAddr.split(":", 1);
                res = prefix + " " + memAddrSplit[0] + ":[" + memAddrSplit[1] + "]";
            }
        }
        return res.strip();
    }


    String execEval(String arg) {
        String res = arg;
        String content;
        if(arg.endsWith("]")) {
            String[] argSplit = arg.split("[", 1);
            String prefix = argSplit[0];
            String memAddr = Utils.rsplit(argSplit[1].strip(), "]")[0].strip();
            memAddr = Helper.simulateEvalExpr(memAddr);
            if(!prefix.contains("("))
                res = prefix + "[" + memAddr + "]";
            else
                res = "[" + memAddr + "]";
        }
        else if(arg.startsWith("(") && arg.endsWith(")")) {
            content = Utils.extract_content(arg, "(");
            content = handleOffsetOperation(content);
            res = Helper.simulateEvalExpr(content);
        }
        else if(arg.startsWith("offset ")) {
            content = handleOffsetOperation(arg);
            res = Helper.simulateEvalExpr(content);
        }
        else
            res = Helper.simulateEvalExpr(arg);
        return res;
    }
        

    String removeUnusedSegReg(long address, String arg) {
        String res = arg;
        if(arg.contains("s:") && !arg.endsWith("]")) {
            String[] argSplit = arg.strip().split(":", 1);
            String prefix = argSplit[0].strip();
            String remaining = argSplit[1].strip();
            if(idaImmPat.matcher(remaining).matches()) {
                if(prefix.startsWith("large ")) {
                    if(prefix.contains(" ptr")) {
                        prefix = prefix.split(" ", 1)[1].strip();
                        String[] prefixSplit = Utils.rsplit(prefix, " ");
                        String ptrRep = prefixSplit[0];
                        String segName = prefixSplit[1];
                        res = ptrRep.strip() + " [" + segName + ":" + Utils.convertImmEndHToHex(remaining) + "]";
                    }
                    else {
                        prefix = prefix.split(" ", 1)[1].strip();
                        res = "[" + prefix + ":" + Utils.convertImmEndHToHex(remaining) + "]";
                    }
                }
                else
                    res = prefix + ":" + Utils.convertImmEndHToHex(remaining);
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
                res = arg.split(" ", 1)[1].strip();
        }
        return res;
    }


    String replaceTailHexwSuffixH(String inst) {
        String res = inst;
        Matcher m = subtractHexPat.matcher(inst);
        if(m.matches()) {
            String hexStr = m.group(0);
            String newHexRep = Utils.convertImmEndHToHex(hexStr);
            res = inst.replace(hexStr, newHexRep);
        }
        return res;
    }


    String rewriteSpecJumpInst(String instName, long address, String arg) {
        String res = arg.strip();
        if(Utils.check_jmp_with_address(instName)) {
            if(res.startsWith("$")) {
                res = res.split("$", 1)[1].strip();
                long newAddr = address + Long.valueOf(res);
                res = Long.toHexString(newAddr);
            }
        }
        return res;
    }



    String postprocessFormatInst(long address, String inst, String instName, ArrayList<String> instArgs) {
        Integer length = null;
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
        res = Helper.convertToHexRep(res);
        return res;
    }

    String removeLeaPtrRep(String instName, String arg) {
        String res = arg;
        if(instName == "lea") {
            if(arg.endsWith("]")) {
                res = "[" + arg.split("[", 1)[1].strip();
            }
        }
        return res;
    }


    void handleIdaPtrRep(long address, String inst, int length, String instName, ArrayList<String> instArgs, int idx, String arg) {
        if(!arg.contains(" ptr ") || addedPtrRepMap.containsKey(address)) {
            String ptrRep = Helper.generateIdaPtrRep(instName, inst, length);
            if(ptrRep == null) {
                if(instName != "lea" && !addedPtrRepMap.containsKey(address)) {
                    if(arg.endsWith("]") && !arg.contains(" ptr ") || arg.contains("s:")) {
                        if(length != 0)
                            ptrRep = Helper.BYTELEN_REP_MAP.get(length);
                        else if(instName == "movsx" || instName == "movzx") {
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
                	instArgs.set(idx, ptrRep + " [" + arg.split("[", 1)[1].strip());
            }
        }
    }
      

    String replaceIdaStructItemSymbol(String symbol) {
        String res = symbol;
        String[] symbolSplit = symbol.split(".", 1);
        String symbolName = symbolSplit[0].strip();
        if(varIdaStructTypeMap.containsKey(symbolName)) {
            String symbolType = varIdaStructTypeMap.get(symbolName);
            String itemEntry = symbolSplit[1].strip();
            if(varValueMap.containsKey(symbolName)) {
                if(idaStructTable.containsKey(symbolType)) {
                	Tuple<Integer, String> idaOffType = retrieveIdaTypeOffsetType(symbolType, itemEntry);
                	int offset = idaOffType.x;
                	String itemType  = idaOffType.y;
                    res = Long.toHexString(varValueMap.get(symbolName) + offset);
                    String ptrRep = Helper.getIdaPtrRepFromItemType(itemType);
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
        String[] varSplit = var_str.split("=", 1);
        String varName = varSplit[0].strip();
        varOffsetMap.put(varName, address);
        String varValue = varSplit[1].strip();
        String[] varValueSplit = Utils.rsplit(varValue, " ");
        String ptrRep = varValueSplit[0].strip();
        String typeSpec = ptrRep.split("ptr", 1)[0].strip();
        if(!Helper.BYTE_LEN_REPS.containsKey(typeSpec)) {
            if(idaStructTable.containsKey(typeSpec))
                varIdaStructTypeMap.put(varName, typeSpec);
            else if(typeSpec == "LARGE_INTEGER" || typeSpec == "_LARGE_INTEGER") {
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
        	long value = Integer.valueOf(Utils.rsplit(varValue, "h")[0].strip(), 16);
            varValueMap.put(varName, value);
        }
        else if(Utils.imm_pat.matcher(varValue).matches()) {
            long value = Integer.valueOf(varValue);
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
        String varName = line.split(" ", 2)[1].strip();
        return varName;
    }

    
    String handleOffsetOperation(String arg) {
        String content = arg;
        if(content.contains("offset ")) {
            String original = null;
            String newVar = null;
            String[] contentSplit = content.split("[^a-zA-Z0-9_.@?$]+");
            int cNum = contentSplit.length;
            String variable, var;
            for(int idx = 0; idx < cNum; idx++) {
            	String ci = contentSplit[idx];
                if(ci == "offset") {
                    if(cNum > idx + 1) {
                        variable = contentSplit[idx + 1];
                        original = "offset " + variable;
                        if(varOffsetMap.containsKey(variable))
                            newVar = Long.toHexString(varOffsetMap.get(variable));
                        else if(variable.contains("."))
                            newVar = replaceIdaStructItemSymbol(variable);
                        else if(Utils.startsWith(variable, offsetSpecPrefix)) {
                            var = variable.split("_", 1)[1];
                            if(Utils.imm_start_pat.matcher(var).matches()) {
                                newVar = Integer.toHexString(Integer.valueOf(var, 16));
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
        	String[] itemEntrySplit = itemEntry.split(".", 1);
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
