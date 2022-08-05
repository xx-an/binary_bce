package normalizer;

import java.io.FileNotFoundException;
import java.util.HashMap;

public interface Normalize {
	
	void read_asm_info() throws FileNotFoundException;
	
	HashMap<Long, String> get_address_inst_map();
	
}
