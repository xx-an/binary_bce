package common;

import java.util.ArrayList;
import java.util.Collections;
import java.util.function.Function;

public class InstElement {
	public String inst_name;
	public ArrayList<String> inst_args;
	
	public InstElement(String inst) {
		String[] inst_split = inst.strip().split(" ", 2);
		inst_name = inst_split[0].strip();
		inst_args = Utils.extract_inst_args(inst_split);
	}

	
	void reverse_arg_order() {
		Collections.reverse(inst_args);
	}
	

	public String normalize(long address, Function<String, String> rewrite_inst) {
        String inst_arg = String.join(",", inst_args);
        String result = inst_name + " " + inst_arg;
        result = rewrite_inst.apply(result);
        return result;
	}

}
