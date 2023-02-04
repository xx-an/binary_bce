package common;

import binary.BinaryInfo;
import binary.BinaryContent;
    
public class GlobalVar {
	public static BinaryInfo binary_info = null;
	public static BinaryContent binary_content = null;
	
	public static void get_binary_info(String exec_path) {
	    binary_info = new BinaryInfo(exec_path);
	    binary_content = new BinaryContent(exec_path);
	}

}
