package normalizer;

import java.io.FileNotFoundException;

public class NormalizerFactory {

	String asmPath;
	String disasmType;

	public NormalizerFactory(String asm_path, String disasmType) {
        this.asmPath = asm_path;
        this.disasmType = disasmType;
	}


    public Normalizer get_disasm() throws FileNotFoundException {
        if(this.disasmType == "idapro")
            return new NormalizerIDAPro(asmPath);
        return null;
    }


}
