package normalizer;

import java.io.FileNotFoundException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;

public interface Normalizer {
	
	void readASMInfo() throws FileNotFoundException;
	
	HashMap<Long, String> getAddressInstMap();
	
	HashMap<Long, Long> getAddressNextMap();
	
	HashMap<Long, String> getAddressExtFuncMap();
	
	HashMap<Long, ArrayList<Long>> readGlobalJPTEntriesMap();
	
	HashSet<Long> getFuncEndAddrSet();
	
	Long getMainAddress();
	
	Long getEntryAddress();
	
	HashMap<String, Long> getSecStartAddrMap();
	
	HashMap<Long, String> getAddressSymTbl();
	
	HashMap<String, Long> getSymTbl();
}
