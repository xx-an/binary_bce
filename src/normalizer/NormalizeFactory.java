package normalizer;

import java.io.FileNotFoundException;

public class NormalizeFactory {

	String asm_path;
	String exec_path;
	String disasm_type;

	NormalizeFactory(String asm_path, String exec_path, String disasm_type) {
        this.asm_path = asm_path;
        this.exec_path = exec_path;
        this.disasm_type = disasm_type;
	}


    Normalize get_disasm() throws FileNotFoundException {
        if(this.disasm_type == "objdump")
            return new NormalizeObjdump(asm_path, exec_path);
        return null;
    }


}
