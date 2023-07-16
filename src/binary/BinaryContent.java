package binary;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import common.Utils;
import normalizer.NormFactory;

public class BinaryContent {
	
	public static HashMap<Long, Byte> addressBytesMap;
	public static HashMap<String, Long> secStartAddrMap;
	public static HashMap<String, Long> secEndAddrMap;
	public static HashMap<String, Long> secBaseAddrMap;
	
	
	public static void readBinaryContent(String src_path) {
		Path srcPath = Paths.get(src_path);
		addressBytesMap = new HashMap<>();
		secStartAddrMap = NormFactory.norm.getSecStartAddrMap();
		secEndAddrMap = new HashMap<>();
		secBaseAddrMap = new HashMap<>();
		parseSecHeaders(src_path);
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
	
	static void parseSecHeaders(String srcPath) {
		String secHeaderInfo = Utils.execute_command("objdump -h " + srcPath);
		String[] lines = secHeaderInfo.split("\n");
		for(String line : lines) {
			line = line.strip();
			if(line != "" && Utils.imm_start_pat.matcher(line).find()) {
				line = Utils.remove_multiple_spaces(line);
				String[] lineSplit = line.split(" ");
				String secName = lineSplit[1];
				if(secStartAddrMap.containsKey(secName)) {
					long secAddr = secStartAddrMap.get(secName);
	                long secSize = Utils.imm_str_to_int(lineSplit[2]);
	                long secOffset = Utils.imm_str_to_int(lineSplit[5]);
	                secEndAddrMap.put(secName, secAddr + secSize + 1);
	                secBaseAddrMap.put(secName, secAddr - secOffset);
				}
			}
		}
		HashSet<String> nonExistSecNames = new HashSet<>();
		for(String secName : secStartAddrMap.keySet()) {
			if(!secEndAddrMap.containsKey(secName)) {
				nonExistSecNames.add(secName);
			}
		}
		for(String secName : nonExistSecNames) {
			secStartAddrMap.remove(secName);
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
