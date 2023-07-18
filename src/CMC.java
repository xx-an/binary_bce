
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.concurrent.TimeUnit;
import java.util.logging.Level;

import binary.BinaryContent;

import org.apache.commons.cli.*;

import common.Config;
import common.Helper;
import common.Utils;
import controlflow.ControlFlow;
import graph.GraphBuilder;
import normalizer.NormFactory;
import normalizer.NormHelper;
import normalizer.Normalizer;

public class CMC {
	

	static ControlFlow constructCF(String execPath, GraphBuilder graphBuilder) {
		Normalizer norm = NormFactory.norm;
	    Path constraintConfigPath = Paths.get(Utils.PROJECT_DIR.toString(), Utils.PREDEFINED_CONSTRAINT_FILE);
	    HashMap<String, ArrayList<String>> preConstraint = Helper.parse_predefined_constraint(constraintConfigPath);
	    ControlFlow cfg = new ControlFlow(preConstraint, norm, graphBuilder);
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
	    Utils.output_logger.info("# of reached instructions: " + Integer.toString(numReachableAddrs));
	    Utils.output_logger.info("# of paths: " + Integer.toString(numPaths));
	    Utils.output_logger.info("# of (possibly) negative paths: " + Integer.toString(numNegPaths));
	    Utils.output_logger.info("# of uninitialized content: " + Integer.toString(numUninitialized));
	    Utils.output_logger.info("# of unresolved indirects: " + Integer.toString(numUnresolvedIndirects));
	}
	    
	
	static void cmc_main(String execPath, String disasmPath, String disasmType, boolean verbose) throws Exception {
	    set_logger(disasmPath, disasmType, verbose);
	    NormHelper.disassemble_to_asm(execPath, disasmPath, disasmType);
	    NormFactory.setDisasm(disasmPath, disasmType);
	    BinaryContent.readBinaryContent(execPath);
//	     GraphBuilder graphBuilder = new GraphBuilder(0);
//	    graphBuilder.addEdge(0, 1);
//	    graphBuilder.addEdge(1, 2);
//	    graphBuilder.addEdge(2, 1);
//	    graphBuilder.addEdge(1, 3);
//	    graphBuilder.addEdge(3, 1);
//	    graphBuilder.addEdge(1, 4);
//	    graphBuilder.addEdge(4, 5);
//	    graphBuilder.addEdge(5, 4);
//	    graphBuilder.addEdge(2, 6);
//	    graphBuilder.addEdge(6, 2);
//	    graphBuilder.addEdge(6, 7);
//	    graphBuilder.addEdge(7, 2);
//	    graphBuilder.detectAllCycles();
	    GraphBuilder graphBuilder = new GraphBuilder(NormFactory.norm);
		long startTime = System.nanoTime();
	    ControlFlow cfg = constructCF(execPath, graphBuilder);
	    long duration = TimeUnit.NANOSECONDS.toSeconds(System.nanoTime() - startTime);
	    write_results(cfg);
	    Utils.output_logger.info("Execution time (s) : " + Long.toString(duration));
	    close_logger();
	}
	
	
	static void cmc_batch(String execDir, String disasmDir, String disasmType, boolean verbose) throws Exception {
	    ArrayList<String> asmFiles = Utils.getASMFiles(disasmDir, disasmType);
	    Collections.sort(asmFiles);
	    for(String asmPath : asmFiles) {
	        String fileName = Utils.get_file_name(asmPath);
	        // if file_name in ["cp.exe", "cut.exe", "dir.exe", "fmt.exe", "grmdir.exe", "gsort.exe", "id.exe", "ls.exe", "md5sum.exe", "mv.exe", "nl.exe", "pathchk.exe", "readlink.exe", "rmdir.exe", "sha1sum.exe", "shred.exe", "sort.exe", "split.exe", "su.exe", "uname.exe", "vdir.exe", "who.exe"]:
	        System.out.println(fileName);
	        String execPath = Paths.get(execDir, Utils.rsplit(fileName, "\\.")[0]).toString();
	        try {
	            cmc_main(execPath, asmPath, disasmType, verbose);
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
        
        Option execDirOpt = Option.builder("e").longOpt("exec_dir")
                .argName("exec_dir")
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
        
        Option memAddrSizeOpt = Option.builder("m").longOpt("addr_size")
                .argName("addr_size")
                .hasArg()
                .desc("The size of the memory address")
                .build();
	    

        options.addOption(batchOpt);
        options.addOption(verboseOpt);
        options.addOption(disasmTypeOpt);
        options.addOption(logDirOpt);
        options.addOption(execDirOpt);
        options.addOption(fileNameOpt);
        options.addOption(cmcBoundOpt);
        options.addOption(memAddrSizeOpt);
        
        
        CommandLineParser parser = new DefaultParser();
        CommandLine line = parser.parse(options, args);
        
        Utils.MAX_VISIT_COUNT = Integer.decode(line.getOptionValue("cmc_bound", "25"));
        Config.MEM_ADDR_SIZE = Integer.decode(line.getOptionValue("addr_size", "32"));
	    String disasmType = line.getOptionValue("disasm_type", "idapro");
	    String fileName = line.getOptionValue("file_name", "basename.exe");
	    String execDir = Paths.get(Utils.PROJECT_DIR.toString(), line.getOptionValue("exec_dir", "benchmark/coreutils-bin")).toString();
	    String logDir = Paths.get(Utils.PROJECT_DIR.toString(), line.getOptionValue("log_dir", "benchmark/coreutils-idapro")).toString();
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
        