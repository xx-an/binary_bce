package normalizer;

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

import com.microsoft.z3.BitVecExpr;

public interface Normalizer {
	
	void read_asm_info() throws FileNotFoundException;
	
	HashMap<Long, String> getAddressInstMap();
	
	HashMap<Long, Long> getAddressNextMap();
	
	HashMap<Long, String> getAddressExtFuncMap();
	
	HashMap<Long, ArrayList<BitVecExpr>> readGlobalJPTEntriesMap();
	
	HashSet<Long> getFuncEndAddrSet();
	
	Long getMainAddress();
	
	Long getEntryAddress();
	
	HashMap<Long, String> getAddressSymTbl();
	
	HashMap<String, Long> getSymTbl();
	
	HashMap<String, Long> getSecStartAddr();
	
	HashMap<String, Long> getSecEndAddr();
	
	HashMap<String, Long> getSecBaseAddr();
}
