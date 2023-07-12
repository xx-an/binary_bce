package binary;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;

import common.Utils;

public class BinaryContent {
	
	public static Path srcPath;
	public static HashMap<Long, Byte> addressBytesMap;
	
	
	public static void readBinaryContent(String src_path) {
		srcPath = Paths.get(src_path);
		addressBytesMap = new HashMap<Long, Byte>();
		long idx = 0;
		try {
			byte[] content = Files.readAllBytes(srcPath);
			for(byte b : content) {
				addressBytesMap.put(idx, b);
				idx += 1;
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	public static long read_bytes(long address, int length) {
		ArrayList<Byte> res = new ArrayList<Byte>();
		for(int i = length - 1; i >= 0; i--) {
			long curr = address + i;
			if(addressBytesMap.containsKey(curr))
				res.add(addressBytesMap.get(curr));
			else
				return -1;
		}
		return Utils.bytes_to_int(res);
	}
	
	String read_byte_sequence(long address, int length) {
		ArrayList<Byte> res = new ArrayList<Byte>();
		for(int i = length - 1; i >= 0; i--) {
			long curr = address + i;
			if(addressBytesMap.containsKey(curr))
				res.add(addressBytesMap.get(curr));
			else
				return "";
		}
		return Utils.bytes_to_hex(res);
	}
	
	
	void read_bytes_all() {
		int num = addressBytesMap.size();
		for(int i = 0; i < num; i++) {
			long res = read_bytes(i, 1);
			System.out.println(res);
		}
	}
}
