package common;

import binary.BinaryInfo;
import binary.BinaryContent;
    
public class GlobalVar {
	public static BinaryInfo binary_info;
	public static BinaryContent binary_content;
	
	public GlobalVar(String exec_path) {
	    binary_info = new BinaryInfo(exec_path);
	    binary_content = new BinaryContent(exec_path);
	}

}
