
public class DSV {

	String[] CHECK_RESULTS = new String[]{"", "$\\times$"};

	void construct_cfg(disasm_asm, disasm_type):
	    start_address = global_var.binary_info.entry_address
	    main_address = global_var.binary_info.main_address
	    address_sym_table = global_var.binary_info.address_sym_table
	    address_inst_map = disasm_asm.get_address_inst_map()
	    # print(global_var.binary_info.sym_table)
	    cfg = CFG(address_sym_table, address_inst_map, disasm_asm.address_next_map, start_address, main_address, disasm_asm.valid_address_no, disasm_type)
	    return cfg


	void set_logger(disasm_path, disasm_type, verbose=False):
	    logger_path = disasm_path.replace("." + disasm_type, "." + utils.LOG_NAME)
	    utils.setup_logger(logger_path, verbose, logging.DEBUG)


	void write_results(disasm_path, disasm_type, cnt_list):
	    output_path = disasm_path.replace("." + disasm_type, ".output")
	    with open(output_path, "w+") as f:
	        f.write("# of total instructions: " + str(cnt_list[0]) + "\n")
	        f.write("# of white instructions: " + str(cnt_list[1]) + "\n")
	        f.write("# of grey instructions: " + str(cnt_list[2]) + "\n")
	        f.write("# of black instructions: " + str(cnt_list[3]) + "\n")
	        f.write("Ratio (grey/white): " + str(cnt_list[4]) + "\n")
	        f.write("# of indirects: " + str(cnt_list[5]) + "\n")


	void write_soundness_results(disasm_path, disasm_type, res, unsound_cases, print_info):
	    output_path = disasm_path.replace("." + disasm_type, ".output")
	    with open(output_path, "a") as f:
	        if res:
	            f.write("The disassembly process is sound\n")
	            f.write("# of incorrectly disassembled instructions: 0\n") 
	        else:
	            f.write("The disassembly process is unsound\n")
	            f.write("# of incorrectly disassembled instructions: " + str(unsound_cases) + "\n")
	            f.write("\n" + print_info)
	    


	void update_soundness_results(disasm_log_path, res, unsound_cases, print_info):
	    output_path = disasm_log_path.replace(".log", ".output")
	    new_content = ""
	    with open(output_path, "r") as f:
	        lines = f.readlines()
	        new_content += "".join(lines[:6]) 
	    if res:
	        new_content += "The disassembly process is sound\n"
	        new_content += "# of incorrectly disassembled instructions: 0\n"
	    else:
	        new_content += "The disassembly process is unsound\n"
	        new_content += "# of incorrectly disassembled instructions: " + str(unsound_cases) + "\n"
	        new_content += "\n" + print_info + "\n"
	    with open(output_path, "w") as f:
	        f.write(new_content)


	void check_soundness(exec_path, disasm_log_path, not_only, verbose):
	    global_var.get_binary_info(exec_path)
	    res, unsound_cases, print_info = soundness.sound_disasm_file(global_var.binary_content, disasm_log_path)
	    if verbose:
	        print(print_info)
	    if not_only:
	        update_soundness_results(disasm_log_path, res, unsound_cases, print_info)


	void check_soundness_batch(elf_lib_dir, disasm_lib_dir, not_only, verbose):
	    disasm_log_files = [os.path.join(dp, f) for dp, _, filenames in os.walk(disasm_lib_dir) for f in filenames if f.endswith(".log")]
	    disasm_log_files.sort()
	    for disasm_log_path in disasm_log_files:
	        file_name = utils.get_file_name(disasm_log_path)
	        exec_path = os.path.join(elf_lib_dir, file_name)
	        if os.path.exists(exec_path):
	            print(file_name)
	            check_soundness(exec_path, disasm_log_path, not_only, verbose)
	            time.sleep(20)


	void check_soundness_specified(file_names, elf_lib_dir, disasm_lib_dir, not_only, verbose):
	    for file_name in file_names:
	        print(file_name)
	        exec_path = os.path.join(elf_lib_dir, file_name)
	        disasm_log_path = os.path.join(disasm_lib_dir, file_name + ".log")
	        if os.path.exists(exec_path):
	            check_soundness(exec_path, disasm_log_path, not_only, verbose)
	            time.sleep(10)
	        

	void dsv_main(elf_lib_dir, exec_path, disasm_path, disasm_type, not_only, verbose):
	    set_logger(disasm_path, disasm_type, verbose)
	    file_name = utils.get_exec_file_name(exec_path)
	    global_var.get_binary_info(exec_path)
	    helper.disassemble_to_asm(exec_path, disasm_path, disasm_type)
	    disasm_factory = Disasm_Factory(disasm_path, exec_path, global_var.binary_content, disasm_type)
	    disasm_asm = disasm_factory.get_disasm()
	    cfg = construct_cfg(disasm_asm, disasm_type)
	    utils.close_logger()
	    time.sleep(30)
	    cnt_list = neat_unreach.main_single(file_name, elf_lib_dir, disasm_lib_dir, disasm_type, False)
	    print(file_name + "\t" + "\t".join(list(map(lambda x: str(x), cnt_list))))
	    write_results(disasm_path, disasm_type, cnt_list)
	    if not_only:
	        res, unsound_cases, print_info = soundness.sound(global_var.binary_content, disasm_asm, cfg)
	        write_soundness_results(disasm_path, disasm_type, res, unsound_cases, print_info)
	    time.sleep(10)


	void dsv_batch(elf_lib_dir, disasm_lib_dir, disasm_type, not_only, verbose):
	    disasm_files = [os.path.join(dp, f) for dp, _, filenames in os.walk(disasm_lib_dir) for f in filenames if f.endswith(disasm_type)]
	    disasm_files.sort()
	    for disasm_path in disasm_files:
	        file_name = utils.get_file_name(disasm_path)
	        exec_path = os.path.join(elf_lib_dir, file_name)
	        if os.path.exists(exec_path):
	            try:
	                print(file_name)
	                dsv_main(elf_lib_dir, exec_path, disasm_path, disasm_type, not_only, verbose)
	            except:
	                utils.close_logger()
	                time.sleep(10)
	                continue


	void dsv_specified(file_names, elf_lib_dir, disasm_lib_dir, disasm_type, not_only, verbose):
	    for file_name in file_names:
	        exec_path = os.path.join(elf_lib_dir, file_name)
	        disasm_path = os.path.join(disasm_lib_dir, file_name + "." + disasm_type)
	        if os.path.exists(exec_path):
	            try:
	                print(file_name)
	                dsv_main(elf_lib_dir, exec_path, disasm_path, disasm_type, not_only, verbose)
	            except:
	                utils.close_logger()
	                time.sleep(10)
	                continue


	public static void main(String[] args) {
	    parser = argparse.ArgumentParser(description="Disassembly Soundness Verification")
	    parser.add_argument("-t", "--disasm_type", default="objdump", type=str, help="Disassembler")
	    parser.add_argument("-b", "--batch", default=False, action="store_true", help="Run dsv_main in batch mode") 
	    parser.add_argument("-s", "--soundness", default=False, action="store_true", help="Check the soundness for specific file") 
	    parser.add_argument("-n", "--not_only", default=False, action="store_true", help="Not only construct the CFG or check the soundness") 
	    parser.add_argument("-l", "--log_dir", default="benchmark/coreutils-objdump", type=str, help="Benchmark library") 
	    parser.add_argument("-e", "--elf_dir", default="benchmark/coreutils-build", type=str, help="Elf shared object library") 
	    parser.add_argument("-f", "--file_name", type=str, help="Benchmark file name")
	    parser.add_argument("-v", "--verbose", default=False, action="store_true", help="Whether to print log information on the screen")
	    parser.add_argument("-c", "--bmc_bound", default=25, type=int, help="The default value of the BMC bound")
	    args = parser.parse_args()
	    utils.MAX_VISIT_COUNT = args.bmc_bound
	    disasm_type = args.disasm_type
	    log_dir = args.log_dir
	    if disasm_type != "objdump" and "objdump" in args.log_dir:
	        log_dir = log_dir.replace("objdump", disasm_type)
	    disasm_lib_dir = os.path.join(utils.PROJECT_DIR, log_dir)
	    elf_lib_dir = os.path.join(utils.PROJECT_DIR, args.elf_dir)
	    # 
	    if args.soundness:
	        if args.batch:
	            check_soundness_batch(elf_lib_dir, disasm_lib_dir, args.not_only, args.verbose)   
	        else: 
	            disasm_log_path = os.path.join(disasm_lib_dir, args.file_name + ".log")
	            exec_path = os.path.join(elf_lib_dir, args.file_name)
	            check_soundness(exec_path, disasm_log_path, args.not_only, args.verbose)
	    else:
	        if args.batch:
	            dsv_batch(elf_lib_dir, disasm_lib_dir, disasm_type, args.not_only, args.verbose)
	        else:
	            disasm_path = os.path.join(disasm_lib_dir, args.file_name + "." + disasm_type)
	            exec_path = os.path.join(elf_lib_dir, args.file_name)
	            dsv_main(elf_lib_dir, exec_path, disasm_path, disasm_type, args.not_only, args.verbose)
	    # 
	    # disasm_path = os.path.join(disasm_lib_dir, args.file_name + "." + disasm_type)
	    # exec_path = os.path.join(elf_lib_dir, args.file_name)
	    # helper.disassemble_to_asm(exec_path, disasm_path, disasm_type)
	    
	    
	        
}
