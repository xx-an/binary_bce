import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.concurrent.TimeUnit;
import java.util.logging.Level;

import java.io.FileWriter;
import java.io.PrintWriter;

import org.apache.commons.cli.*;

import binary.BinaryContent;
import common.Config;
import common.Helper;
import common.Utils;
import controlflow.ControlFlow;
import graph.GraphBuilder;
import normalizer.NormFactory;
import normalizer.NormHelper;
import normalizer.Normalizer;

public class WinCheck {
	

	static ControlFlow constructCF(String execPath, GraphBuilder graphBuilder) {
		Normalizer norm = NormFactory.norm;
	    Path constraintConfigPath = Paths.get(Utils.PROJECT_DIR.toString(), Utils.PREDEFINED_CONSTRAINT_FILE);
	    HashMap<String, ArrayList<String>> preConstraint = Helper.parse_predefined_constraint(constraintConfigPath);
	    ControlFlow cfg = new ControlFlow(preConstraint, norm, graphBuilder);
	    return cfg;
	}
    

	static void set_logger(String normPath, String normType) throws SecurityException, IOException {
	   for(String logName : Utils.LOG_NAMES) {
	        String loggerPath = normPath.replace("." + normType, "." + logName);
	        Utils.setup_logger(logName, loggerPath, Level.WARNING);
	    }
	}


	static void close_logger() {
		for(String logName : Utils.LOG_NAMES) {
	        Utils.close_logger(logName);
		}
	}


	static void writeToCSV() {
		String csvFile = "statistics.csv";
		String csvPath = Paths.get(Utils.PROJECT_DIR.toString(), csvFile).toString();

        try (PrintWriter writer = new PrintWriter(new FileWriter(csvPath))) {
            // Writing data to CSV
            writer.println("Name,Age,City");

            writer.println("John Doe,25,New York");
            writer.println("Jane Smith,30,San Francisco");

            System.out.println("CSV written successfully to " + csvFile);
        } catch (IOException e) {
            e.printStackTrace();
        }
	}
	
	
	static void write_results(ControlFlow cfg) {
		int numPaths = cfg.wincheckExecInfo[0];
		int numNegPaths = cfg.wincheckExecInfo[1];
		int numUnresolvedIndirects = cfg.wincheckExecInfo[2];
		int numUninitialized = cfg.wincheckExecInfo[3];
	    int numReachableAddrs = cfg.reachable_addresses_num();
	    Utils.output_logger.info("# of reached instructions: " + Integer.toString(numReachableAddrs));
	    Utils.output_logger.info("# of paths: " + Integer.toString(numPaths));
	    Utils.output_logger.info("# of (possibly) negative paths: " + Integer.toString(numNegPaths));
	    Utils.output_logger.info("# of uninitialized content: " + Integer.toString(numUninitialized));
	    Utils.output_logger.info("# of unresolved indirects: " + Integer.toString(numUnresolvedIndirects));
	}


	static void writeToCSV(PrintWriter writer, String fileName, ControlFlow cfg, long execTime) {
		int numPaths = cfg.wincheckExecInfo[0];
		int numNegPaths = cfg.wincheckExecInfo[1];
		int numUnresolvedIndirects = cfg.wincheckExecInfo[2];
		int numUninitialized = cfg.wincheckExecInfo[3];
	    int numReachableAddrs = cfg.reachable_addresses_num();
		String writeInfo = fileName + ",";
		writeInfo += Integer.toString(numReachableAddrs) + ",";
		writeInfo += Integer.toString(numPaths) + ",";
		writeInfo += Integer.toString(numNegPaths) + ",";
		writeInfo += Integer.toString(numUninitialized) + ",";
		writeInfo += Integer.toString(numUnresolvedIndirects) + ",";
		writeInfo += Long.toString(execTime);
		writer.println(writeInfo);
	}
	    
	
	static void wincheck_main(String fileName, String execPath, String disasmPath, String disasmType, boolean toCSV, PrintWriter writer) throws Exception {
	    set_logger(disasmPath, disasmType);
	    NormHelper.disassemble_to_asm(execPath, disasmPath, disasmType);
	    NormFactory.setDisasm(disasmPath, disasmType);
	    BinaryContent.readBinaryContent(execPath);
	    GraphBuilder graphBuilder = new GraphBuilder(NormFactory.norm);
		long startTime = System.nanoTime();
	    ControlFlow cfg = constructCF(execPath, graphBuilder);
	    long execTime = TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - startTime);
	    write_results(cfg);
	    Utils.output_logger.info("Execution time (ms) : " + Long.toString(execTime));
		if(toCSV) {
			writeToCSV(writer, fileName, cfg, execTime);
		}
	    close_logger();
	}
	
	
	static void wincheck_batch(String execDir, String disasmDir, String disasmType, boolean toCSV) throws Exception {
	    ArrayList<String> asmFiles = Utils.getASMFiles(disasmDir, disasmType);
	    Collections.sort(asmFiles);
		String csvFile = "statistics.csv";
		String csvPath = Paths.get(Utils.PROJECT_DIR.toString(), csvFile).toString();

        try (PrintWriter writer = new PrintWriter(new FileWriter(csvPath))) {
            // Writing data to CSV
            writer.println("file name, # of reached instructions,# of paths,# of (possibly) negative paths,# of uninitialized content,# of unresolved indirects,Execution time (ms)");
			for(String asmPath : asmFiles) {
				String fileName = Utils.getFileName(asmPath);
				System.out.println(fileName);
				String execPath = Paths.get(execDir, fileName).toString();
				try {
					wincheck_main(fileName, execPath, asmPath, disasmType, toCSV, writer);
					Thread.sleep(15);
				}
				catch(InterruptedException e) {
					close_logger();
					Thread.sleep(15);
					continue;
				}
			}
        } catch (IOException e) {
            e.printStackTrace();
        }
	}
	
	
	void wincheck_specified(String[] fileNames, String execDir, String disasmDir, String disasmType, boolean toCSV) throws Exception {
	    for(String fileName : fileNames) {
	        String execPath = Paths.get(execDir, fileName).toString();
	        String disasmPath = Paths.get(disasmDir, fileName + "." + disasmType).toString();
	        try {
	        	wincheck_main(fileName, execPath, disasmPath, disasmType, toCSV, null);
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
        
        Option verboseOpt = new Option("v", "verbose", false, "Whether to print detailed log information");
        
		Option toCSVOpt = new Option("x", "tocsv", false, "Whether to write all the output information to a CSV file");

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
		options.addOption(toCSVOpt);
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
        Config.initConfig();
	    String disasmType = line.getOptionValue("disasm_type", "idapro");
	    String fileName = line.getOptionValue("file_name", "basename.exe");
	    String execDir = Paths.get(Utils.PROJECT_DIR.toString(), line.getOptionValue("exec_dir", "benchmark/coreutils-bin")).toString();
	    String logDir = Paths.get(Utils.PROJECT_DIR.toString(), line.getOptionValue("log_dir", "benchmark/coreutils-idapro")).toString();
	    boolean batch = (line.hasOption("batch")) ? true : false;
	    boolean verbose = (line.hasOption("verbose")) ? true : false;
		boolean toCSV = (line.hasOption("tocsv")) ? true : false;
	    
	    if(batch) {
	    	wincheck_batch(execDir, logDir, disasmType, toCSV);
	    }
	    else {
	        String disasmPath = Paths.get(logDir, fileName + "." + disasmType).toString();
	        String execPath = Paths.get(execDir, fileName).toString();
	        wincheck_main(fileName, execPath, disasmPath, disasmType, toCSV, null);
	    }
	}
	    
}
        