package common;

import binary.BinaryContent;
import binary.BinaryInfo;

public class GlobalVar {
	public static BinaryInfo binaryInfo;
	public static BinaryContent binaryContent;
	
	public static void getBinaryInfo(String execPath) {
		binaryInfo = new BinaryInfo(execPath);
		binaryContent = new BinaryContent(execPath);
	}
}