package normalizer;

import java.io.FileNotFoundException;

public class NormalizerFactory {

	String asm_path;
	String disasm_type;

	public NormalizerFactory(String asm_path, String disasm_type) {
        this.asm_path = asm_path;
        this.disasm_type = disasm_type;
	}


    public Normalizer get_disasm() throws FileNotFoundException {
        if(this.disasm_type == "objdump")
            return new NormalizeObjdump(asm_path);
        return null;
    }


}
