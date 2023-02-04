package normalizer;

import java.io.FileNotFoundException;
import java.util.HashMap;

public interface Normalizer {
	
	void read_asm_info() throws FileNotFoundException;
	
	HashMap<Long, String> getAddressInstMap();
	
	HashMap<Long, String> getAddressLabelMap();
	
	HashMap<Long, Long> getAddressNextMap();
	
	HashMap<Long, String> getAddressExtFuncMap();
	
}
