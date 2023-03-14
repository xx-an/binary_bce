package normalizer;

import java.io.FileNotFoundException;

public class NormFactory {

	String asmPath;
	String disasmType;

	public NormFactory(String asm_path, String disasmType) {
        this.asmPath = asm_path;
        this.disasmType = disasmType;
	}


    public Normalizer get_disasm() throws FileNotFoundException {
        if(this.disasmType.equals("idapro"))
            return new NormIDAPro(asmPath);
        return null;
    }


}
