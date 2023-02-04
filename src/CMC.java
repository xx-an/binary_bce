import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.concurrent.TimeUnit;
import java.util.logging.Level;

import com.microsoft.z3.BitVecExpr;
import org.apache.commons.cli.*;

import common.Config;
import common.GlobalVar;
import common.Helper;
import common.Utils;
import controlflow.ControlFlow;
import normalizer.Normalizer;
import normalizer.NormalizerFactory;

public class CMC {
	
	final String[] CHECK_RESULTS;
	static long mainAddress;
	static HashMap<String, BitVecExpr> symTable;
	static HashMap<BitVecExpr, ArrayList<String>> addressSymTable;
	static HashMap<Long, String> addressInstMap;
	static HashMap<Long, String> addressLableMap;
	
	public CMC() {
		CHECK_RESULTS = new String[] {"", "$\\\\times$"};
	}
	
	static ControlFlow constructCF(Normalizer norm) {
		mainAddress = GlobalVar.binary_info.main_address;
		symTable = GlobalVar.binary_info.sym_table;
		addressSymTable = GlobalVar.binary_info.address_sym_table;
		addressInstMap = norm.getAddressInstMap();
		addressLableMap = norm.getAddressLabelMap();
		for(long address : addressLableMap.keySet()) {
			BitVecExpr bvAddr = Helper.gen_bv_num(address, 64);
			if(addressSymTable.containsKey(bvAddr)) {
				addressSymTable.get(bvAddr).add(addressLableMap.get(address));
			}
			else {
				ArrayList<String> symList = new ArrayList<>();
				symList.add(addressLableMap.get(address));
				addressSymTable.put(bvAddr, symList);
			}
		}
	    String funcName = "_start";
	    long startAddress = GlobalVar.binary_info.entry_address;
	    Path constraintConfigPath = Paths.get(Utils.PROJECT_DIR.toString(), Utils.PREDEFINED_CONSTRAINT_FILE);
	    HashMap<String, ArrayList<String>> preConstraint = Helper.parse_predefined_constraint(constraintConfigPath);
	    // print(GlobalVar.binary_info.dll_func_info)
	    // print(disasm_asm.valid_address_no)
	    ControlFlow cfg = new ControlFlow(symTable, addressSymTable, addressInstMap, norm.getAddressNextMap(), startAddress, mainAddress, funcName, norm.getAddressExtFuncMap(), preConstraint, GlobalVar.binary_info.dllFuncInfo);
	    return cfg;
	}
	
    

	static void set_logger(String normPath, String normType, boolean verbose) throws SecurityException, IOException {
	    for(String logName : Utils.LOG_NAMES) {
	        String loggerPath = normPath.replace("." + normType, "." + logName);
	        Utils.setup_logger(logName, loggerPath, verbose, Level.WARNING);
	    }
	}


	static void close_logger() {
		for(String logName : Utils.LOG_NAMES) {
	        Utils.close_logger(logName);
		}
	}
	
	
	static void write_results(ControlFlow cfg) {
		int numPaths = cfg.cmcExecInfo[0];
		int numNegPaths = cfg.cmcExecInfo[1];
		int numUnresolvedIndirects = cfg.cmcExecInfo[2];
		int numUninitialized = cfg.cmcExecInfo[3];
	    int numReachableAddrs = cfg.reachable_addresses_num();
	    Utils.output_logger.info("// of reached instructions: " + Integer.toString(numReachableAddrs));
	    Utils.output_logger.info("// of paths: " + Integer.toString(numPaths));
	    Utils.output_logger.info("// of (possibly) negative paths: " + Integer.toString(numNegPaths));
	    Utils.output_logger.info("// of uninitialized content: " + Integer.toString(numUninitialized));
	    Utils.output_logger.info("// of unresolved indirects: " + Integer.toString(numUnresolvedIndirects));
	}
	    
	
	static void cmc_main(String execPath, String disasmPath, String disasmType, boolean verbose) throws Exception {
	    set_logger(disasmPath, disasmType, verbose);
	    GlobalVar.get_binary_info(execPath);
	    Helper.disassemble_to_asm(disasmPath);
	    NormalizerFactory normFactory = new NormalizerFactory(disasmPath, disasmType);
	    Normalizer norm = normFactory.get_disasm();
	    long startTime = System.nanoTime();
	    ControlFlow cfg = constructCF(norm);
	    long duration = TimeUnit.NANOSECONDS.toSeconds(System.nanoTime() - startTime);
	    write_results(cfg);
	    Utils.output_logger.info("Execution time (s) : " + Long.toString(duration));
	    close_logger();
	}
	
	
	static void cmc_batch(String execDir, String disasmDir, String disasmType, boolean verbose) throws Exception {
	    ArrayList<String> execFiles = Utils.get_executable_files(execDir);
	    Collections.sort(execFiles);
	    for(String execPath : execFiles) {
	        String fileName = Utils.get_file_name(execPath);
	        // if file_name in ["cp.exe", "cut.exe", "dir.exe", "fmt.exe", "grmdir.exe", "gsort.exe", "id.exe", "ls.exe", "md5sum.exe", "mv.exe", "nl.exe", "pathchk.exe", "readlink.exe", "rmdir.exe", "sha1sum.exe", "shred.exe", "sort.exe", "split.exe", "su.exe", "uname.exe", "vdir.exe", "who.exe"]:
	        System.out.println(fileName);
	        String disasmPath = Paths.get(disasmDir, fileName + "." + disasmType).toString();
	        try {
	            cmc_main(execPath, disasmPath, disasmType, verbose);
	            Thread.sleep(15);
	        }
	        catch(InterruptedException e) {
	            close_logger();
	            Thread.sleep(15);
	            continue;
	        }
	    }
	}
	
	
	void cmc_specified(String[] fileNames, String execDir, String disasmDir, String disasmType, boolean verbose) throws Exception {
	    for(String file_name : fileNames) {
	        String execPath = Paths.get(execDir, file_name).toString();
	        String disasmPath = Paths.get(disasmDir, file_name + "." + disasmType).toString();
	        try {
	            cmc_main(execPath, disasmPath, disasmType, verbose);
	            Thread.sleep(15);
	        }
	        catch(InterruptedException e) {
	            close_logger();
	            Thread.sleep(15);
	            continue;
	        }
        }
	}
	
	
	public static void main(String[] args) throws Exception {
		Options options = new Options();

        Option batchOpt = new Option("b", "batch", false, "Run the concolic model checkeer in batch mode");
        
        Option verboseOpt = new Option("v", "verbose", false, "Whether to print log information on the screen");
        
        Option disasmTypeOpt = Option.builder("t").longOpt("disasmType")
                .argName("disasmType")
                .hasArg()
                .desc("Disassembler type")
                .build();
        
        Option logDirOpt = Option.builder("l").longOpt("log_dir")
                .argName("log_dir")
                .hasArg()
                .desc("Benchmark library")
                .build();
        
        Option exeDirOpt = Option.builder("e").longOpt("executable_dir")
                .argName("executable_dir")
                .hasArg()
                .desc("Executable file library")
                .build();
        
        Option fileNameOpt = Option.builder("f").longOpt("file_name")
                .argName("file_name")
                .hasArg()
                .desc("Benchmark file name")
                .build();
        
        Option cmcBoundOpt = Option.builder("c").longOpt("cmc_bound")
                .argName("cmc_bound")
                .hasArg()
                .desc("The default value of the CMC bound")
                .build();
        
        Option memAddrSizeOpt = Option.builder("s").longOpt("memory_addr_size")
                .argName("memory_addr_size")
                .hasArg()
                .desc("The default value of the memory address size")
                .build();
	    

        options.addOption(batchOpt);
        options.addOption(verboseOpt);
        options.addOption(disasmTypeOpt);
        options.addOption(logDirOpt);
        options.addOption(exeDirOpt);
        options.addOption(fileNameOpt);
        options.addOption(cmcBoundOpt);
        options.addOption(memAddrSizeOpt);
        
        
        CommandLineParser parser = new DefaultParser();
        CommandLine line = parser.parse(options, args);
	    
	    Utils.MAX_VISIT_COUNT = Integer.valueOf(line.getOptionValue("cmc_bound", "25"));
	    Config.MEM_ADDR_SIZE = Integer.valueOf(line.getOptionValue("memory_addr_size", "32"));
	    String disasmType = line.getOptionValue("disasm_type", "idapro");
	    String fileName = line.getOptionValue("file_name");
	    String logDir = line.getOptionValue("log_dir", "benchmark/coreutils-idapro");
	    String execDir = line.getOptionValue("executable_dir", "benchmark/coreutils-build/src");
	    boolean batch = (line.hasOption("batch")) ? true : false;
	    boolean verbose = (line.hasOption("verbose")) ? true : false;
	    if(batch) {
	    	cmc_batch(execDir, logDir, disasmType, verbose);
	    }
	    else {
	        String disasmPath = Paths.get(logDir, fileName + "." + disasmType).toString();
	        String execPath = Paths.get(execDir, fileName).toString();
	        cmc_main(execPath, disasmPath, disasmType, verbose);
	    }
	}
	    
}
        