package normalizer;

import java.io.FileNotFoundException;

public class NormFactory {

	public static Normalizer norm;

    public static void setDisasm(String asmPath, String disasmType) throws FileNotFoundException {
    	norm = null;
        if(disasmType.equals("idapro")) {
        	norm = new NormIDAPro(asmPath);
        }
        else if(disasmType.equals("objdump")) {
        	norm = new NormObjdump(asmPath);
        }
    }

}
