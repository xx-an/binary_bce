package common;

import java.util.logging.Formatter;
import java.util.logging.LogRecord;

public class LogFormatter extends Formatter {

    public String format(LogRecord record) {
//        return record.getSourceClassName()+"::"+
//                record.getSourceMethodName()+"::"+
         return record.getMessage() + "\n";
    }
    
}
