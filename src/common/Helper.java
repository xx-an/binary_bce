package common;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.function.Function;

import com.microsoft.z3.*;
import com.microsoft.z3.enumerations.Z3_sort_kind;

import normalizer.NormFactory;

public class Helper {
	public static int cnt = 0;
	public static int mem_cnt = 0;
	public static int stdout_mem_cnt = 0;
	
	public static Context ctx = new Context();
	public static final BitVecExpr STDOUT_ADDR = ctx.mkBVConst("stdout", Config.MEM_ADDR_SIZE);
	public static final HashMap<Integer, BitVecExpr> TERMINAL_SYMBOL;
	
	public static BoolExpr SymTrue = ctx.mkTrue();
	public static BoolExpr SymFalse = ctx.mkFalse();
	
	public static HashMap<String, Function<Tuple<BitVecExpr, BitVecExpr>, BoolExpr>> LOGIC_OP_FUNC_MAP = new HashMap<>();
	
	public static HashMap<String, Function<Tuple<BoolExpr, BoolExpr>, BoolExpr>> LOGIC_OP_FUNC_MAP_BOOLEXPR = new HashMap<>();
	
	static {
		LOGIC_OP_FUNC_MAP.put("==", arg -> is_equal(arg.x, arg.y));
		LOGIC_OP_FUNC_MAP.put("<>", arg -> not_equal(arg.x, arg.y));
		LOGIC_OP_FUNC_MAP.put("!=", arg -> not_equal(arg.x, arg.y));
		LOGIC_OP_FUNC_MAP.put("<", arg -> is_less(arg.x, arg.y));
		LOGIC_OP_FUNC_MAP.put(">", arg -> is_greater(arg.x, arg.y));
		LOGIC_OP_FUNC_MAP.put("<=", arg -> is_le(arg.x, arg.y));
		LOGIC_OP_FUNC_MAP.put(">=", arg -> is_ge(arg.x, arg.y));
		
		LOGIC_OP_FUNC_MAP_BOOLEXPR.put("==", arg -> is_equal(arg.x, arg.y));
		LOGIC_OP_FUNC_MAP_BOOLEXPR.put("<>", arg -> not_equal(arg.x, arg.y));
		LOGIC_OP_FUNC_MAP_BOOLEXPR.put("!=", arg -> not_equal(arg.x, arg.y));
		
		TERMINAL_SYMBOL = new HashMap<>();
		TERMINAL_SYMBOL.put(32, ctx.mkBVConst("x", 32));
		TERMINAL_SYMBOL.put(64, ctx.mkBVConst("x", 64));
			
	}

	public static void cnt_init() {
	    cnt = 0;
	    mem_cnt = 0;
	}

	public static BitVecExpr gen_sym(int length) {
	    if(cnt == 23) cnt += 1;
	    String expr = Utils.generate_sym_expr(cnt);
	    BitVecExpr res = ctx.mkBVConst(expr, length);
	    cnt += 1;
	    return res;
	}
	
	
	public static BitVecExpr gen_mem_sym(int length) {
	    String expr = Utils.generate_sym_expr(mem_cnt);
	    BitVecExpr res = ctx.mkBVConst("m_" + expr, length);
	    mem_cnt += 1;
	    return res;
	}
	 
  
	public static BitVecExpr gen_stdout_mem_sym(int length) {
		BitVecExpr stdout = ctx.mkBVConst("stdout", length);
		BitVecNum smc = ctx.mkBV(stdout_mem_cnt, length);
		BitVecExpr res = bv_add(stdout, smc);
	    stdout_mem_cnt += 1;
	    return res;
	}
	
	
	public static BitVecExpr substitute_sym_val(BitVecExpr arg, BitVecExpr prev_val, BitVecExpr new_val) {
		BitVecExpr res = (BitVecExpr) arg.substitute(prev_val, new_val).simplify();
	    return res;
	}
	
	
	public static BitVecExpr bottom(int length) {
		BitVecExpr res = ctx.mkBVConst("Bottom", length);
		return res;
	}
	
	
	public static BitVecExpr gen_bv_num(int val, int length) {
		BitVecExpr res = ctx.mkBV(val, length);
		return res;
	}
	
	public static BitVecExpr gen_bv_num(long val, int length) {
		BitVecExpr res = ctx.mkBV(val, length);
		return res;
	}
	
	public static BitVecExpr gen_spec_sym(String name, int length) {
		BitVecExpr res = ctx.mkBVConst(name, length);
		return res;
	}
	
	public static BoolExpr gen_bool_sym(int val) {
		BoolExpr res = (val == 0) ? ctx.mkFalse() : ctx.mkTrue();
		return res;
	}
	
	public static BoolExpr gen_bool_sym(long val) {
		BoolExpr res = (val == 0) ? ctx.mkFalse() : ctx.mkTrue();
		return res;
	}
	
	
	public static BoolExpr is_equal(BitVecExpr x, BitVecExpr y) {
		BoolExpr res = (BoolExpr) ctx.mkEq(x, y).simplify();
//		Utils.logger.info(res.toString());
		return res;
	}
	
	public static BoolExpr is_equal(BoolExpr x, BoolExpr y) {
		BoolExpr res = (BoolExpr) ctx.mkEq(x, y).simplify();
//		Utils.logger.info(res.toString());
		return res;
	}
	
	public static BoolExpr is_equal(BitVecExpr x, int y) {
		BitVecExpr bv_y = gen_bv_num(y, x.getSortSize());
		return is_equal(x, bv_y);
	}
	
	static BoolExpr not_equal(BitVecExpr x, BitVecExpr y) {
		return (BoolExpr) ctx.mkNot(is_equal(x, y)).simplify();
	}
	
	public static BoolExpr not_equal(BitVecExpr x, int y) {
		BitVecExpr bv_y = gen_bv_num(y, x.getSortSize());
		return not_equal(x, bv_y);
	}
	
	public static BoolExpr not_equal(BoolExpr x, BoolExpr y) {
		return (BoolExpr) ctx.mkNot(is_equal(x, y)).simplify();
	}
	
	public static BoolExpr is_less(BitVecExpr x, BitVecExpr y) {
		return (BoolExpr) ctx.mkBVSLT(x, y).simplify();
	}
	
	static BoolExpr is_greater(BitVecExpr x, BitVecExpr y) {
		return (BoolExpr) ctx.mkBVSGT(x, y).simplify();
	}
	
	static BoolExpr is_le(BitVecExpr x, BitVecExpr y) {
		return (BoolExpr) ctx.mkBVSLE(x, y).simplify();
	}
	
	static BoolExpr is_ge(BitVecExpr x, BitVecExpr y) {
		return (BoolExpr) ctx.mkBVSGE(x, y).simplify();
	}
	
	public static BitVecExpr bv_add(BitVecExpr x, BitVecExpr y) {
		return (BitVecExpr) ctx.mkBVAdd(x, y).simplify();
	}
	
	public static BitVecExpr bv_add(BitVecExpr x, long y) {
		int size = x.getSortSize();
		BitVecNum bv_y = ctx.mkBV(y, size);
		return (BitVecExpr) ctx.mkBVAdd(x, bv_y).simplify();
	}
	
	public static BitVecExpr bv_add(BitVecExpr x, int y) {
		int size = x.getSortSize();
		BitVecNum bv_y = ctx.mkBV(y, size);
		return (BitVecExpr) ctx.mkBVAdd(x, bv_y).simplify();
	}
	
	public static BitVecExpr bv_sub(BitVecExpr x, BitVecExpr y) {
		return (BitVecExpr) ctx.mkBVSub(x, y).simplify();
	}
	
	public static BitVecExpr bv_sub(BitVecExpr x, int y) {
		int size = x.getSortSize();
		BitVecNum bv_y = ctx.mkBV(y, size);
		return (BitVecExpr) ctx.mkBVSub(x, bv_y).simplify();
	}
	
	public static BitVecExpr bv_and(BitVecExpr x, BitVecExpr y) {
		return (BitVecExpr) ctx.mkBVAND(x, y).simplify();
	}
	
	public static BitVecExpr bv_and(BitVecExpr x, int y) {
		int size = x.getSortSize();
		BitVecNum bv_y = ctx.mkBV(y, size);
		return bv_and(x, bv_y);
	}
	
	public static BitVecExpr bv_or(BitVecExpr x, BitVecExpr y) {
		return (BitVecExpr) ctx.mkBVOR(x, y).simplify();
	}
	
	public static BitVecExpr bv_xor(BitVecExpr x, BitVecExpr y) {
		return (BitVecExpr) ctx.mkBVXOR(x, y).simplify();
	}
	
	
	public static BitVecExpr bv_lshift(BitVecExpr x, BitVecExpr y) {
		return (BitVecExpr) ctx.mkBVSHL(x, y).simplify();
	}
	
	public static BitVecExpr bv_lshift(BitVecExpr x, int y) {
		BitVecExpr bv_y = gen_bv_num(y, x.getSortSize());
		return bv_lshift(x, bv_y);
	}
	
	public static BitVecExpr bv_arith_rshift(BitVecExpr x, BitVecExpr y) {
		return (BitVecExpr) ctx.mkBVASHR(x, y).simplify();
	}
	
	public static BitVecExpr bv_arith_rshift(BitVecExpr x, int y) {
		BitVecExpr bv_y = gen_bv_num(y, x.getSortSize());
		return bv_arith_rshift(x, bv_y);
	}
	
	public static BitVecExpr bv_logic_rshift(BitVecExpr x, BitVecExpr y) {
		return (BitVecExpr) ctx.mkBVLSHR(x, y).simplify();
	}
	
	public static BitVecExpr bv_logic_rshift(BitVecExpr x, int y) {
		BitVecExpr bv_y = gen_bv_num(y, x.getSortSize());
		return bv_logic_rshift(x, bv_y);
	}
	
	public static BitVecExpr bv_mult(BitVecExpr x, BitVecExpr y) {
		return (BitVecExpr) ctx.mkBVMul(x, y).simplify();
	}
	
	public static BitVecExpr bv_udiv(BitVecExpr x, BitVecExpr y) {
		return (BitVecExpr) ctx.mkBVUDiv(x, y).simplify();
	}
	
	public static BitVecExpr bv_sdiv(BitVecExpr x, BitVecExpr y) {
		return (BitVecExpr) ctx.mkBVSDiv(x, y).simplify();
	}
	
	public static BitVecExpr bv_umod(BitVecExpr x, BitVecExpr y) {
		return (BitVecExpr) ctx.mkBVURem(x, y).simplify();
	}
	
	public static BitVecExpr bv_smod(BitVecExpr x, BitVecExpr y) {
		return (BitVecExpr) ctx.mkBVSRem(x, y).simplify();
	}
	
	public static BoolExpr bv_and(BoolExpr... x) {
		return (BoolExpr) ctx.mkAnd(x).simplify();
	}
	
	public static BoolExpr bv_or(BoolExpr... x) {
		return (BoolExpr) ctx.mkOr(x).simplify();
	}
	
	public static BoolExpr bv_xor(BoolExpr x, BoolExpr y) {
		return (BoolExpr) ctx.mkXor(x, y).simplify();
	}
	
	public static BoolExpr bv_not(BoolExpr x) {
		return (BoolExpr) ctx.mkNot(x).simplify();
	}
	
	BitVecExpr sym_op(String op, BitVecExpr x, BitVecExpr y) {
		BitVecExpr res = null;
	    if(op.equals("-"))
	        res = ctx.mkBVSub(x, y);
	    else if(op.equals("+"))
	        res = ctx.mkBVAdd(x, y);
	    return (BitVecExpr) res.simplify();
	}


	public static BoolExpr is_neg(BitVecExpr x) {
		int length = x.getSortSize();
		BitVecNum zero = ctx.mkBV(0, length);
		return (BoolExpr) ctx.mkBVSLT(x, zero).simplify();
	}
	
	public static BoolExpr is_pos(BitVecExpr x) {
		int length = x.getSortSize();
		BitVecNum zero = ctx.mkBV(0, length);
		return (BoolExpr) ctx.mkBVSGE(x, zero).simplify();
	}
	
	public static boolean is_bit_vec_num(BitVecExpr arg) {
		return (arg instanceof BitVecNum);
	}
	

	BoolExpr sym_not(BoolExpr sym) {
	    return (BoolExpr) ctx.mkNot(sym).simplify();
	}

	public static BitVecExpr bit_ith(BitVecExpr sym, int idx) {
	    return (BitVecExpr) ctx.mkExtract(idx, idx, sym).simplify();
	}

	public static BoolExpr most_significant_bit(BitVecExpr val, int dest_len) {
		BitVecExpr msb = bit_ith(val, dest_len - 1);
		BitVecNum one = ctx.mkBV(1, 1);
	    return is_equal(msb, one);
	}
	
	public static BoolExpr smost_significant_bit(BitVecExpr val, int dest_len) {
		BitVecExpr smsb = bit_ith(val, dest_len - 2);
		BitVecNum one = ctx.mkBV(1, 1);
	    return is_equal(smsb, one);
	}
	
	
	public static BoolExpr least_significant_bit(BitVecExpr val, int dest_len) {
		BitVecExpr smsb = bit_ith(val, 0);
		BitVecNum one = ctx.mkBV(1, 1);
	    return is_equal(smsb, one);
	}

	
	BitVecExpr bit_vec_wrap(String name, int length) {
		BitVecExpr res = ctx.mkBVConst(name, length);
	    return res;
	}
	
	
	@SuppressWarnings("unchecked")
	public static Model check_pred_satisfiable(ArrayList<BoolExpr> predicates) {
		Solver s = ctx.mkSolver();
	    for(BoolExpr pred : predicates)
	        s.add(pred);
	    Model model = null;
	    if (s.check() == Status.SATISFIABLE)
	    	model = s.getModel();
	    return model;
	}


	@SuppressWarnings("unchecked")
	public static ArrayList<Model> repeated_check_pred_satisfiable(ArrayList<BoolExpr> predicates, int num) {
	    ArrayList<Model> res = new ArrayList<Model>();
	    Solver s = ctx.mkSolver();
	    for(BoolExpr pred : predicates)
	        s.add(pred);
	    while(res.size() < num && s.check() == Status.SATISFIABLE) {
	        Model m = s.getModel();
	        res.add(m);
	        // Create a new constraint the blocks the current model
	        BoolExpr[] block = new BoolExpr[m.getNumConsts()];
	        int idx = 0;
	        for(FuncDecl<?> d : m.getDecls()) {
	            // d is a declaration
	            if(d.getArity() > 0)
	                throw new Z3Exception("uninterpreted functions are not supported");
	            // create a constant from declaration
	            Expr<?> c = d.apply();
	            if(c.isArray() || c.getSort().getSortKind() == Z3_sort_kind.Z3_UNINTERPRETED_SORT)
	            	throw new Z3Exception("arrays && uninterpreted sorts are not supported");
	            block[idx] = not_equal((BitVecExpr) c, (BitVecExpr) m.getConstInterp(d));
	            idx += 1;
	        }
	        s.add(ctx.mkAnd(block));
	    }
	    return res;
	}
	
	
	String pp_z3_model_info(Model m) {
	    ArrayList<String> res = new ArrayList<String>();
	    for(FuncDecl<?> d : m.getDecls()) {
	        Expr<?> s_val = m.getConstInterp(d);	// m[d];
	        res.add(d.getName().toString() + ": " + s_val.toString());
	    }
	    return String.join(", ", res);
	}


	BoolExpr bitwiseXNOR(BitVecExpr sym, int length) {
		BitVecExpr res = bit_ith(sym, 0);
		for(int i = 1; i < length; i++) {
			BitVecExpr curr = bit_ith(sym, i);
			res = ctx.mkBVXNOR(res, curr);
		}
		BitVecExpr one = ctx.mkBV(1, 1);
	    return is_equal(res, one);
	}

	
	public static BitVecExpr sign_ext(int length, BitVecExpr sym) {
		if(length > 0)
			return (BitVecExpr) ctx.mkSignExt(length, sym).simplify();;
		return sym;
	}
	
	
	public static BitVecExpr zero_ext(int length, BitVecExpr sym) {
		if(length > 0)
			return (BitVecExpr) ctx.mkZeroExt(length, sym).simplify();
		return sym;
	}

	
	public static BitVecExpr extract(int high, int low, BitVecExpr sym) {
		return (BitVecExpr) ctx.mkExtract(high, low, sym).simplify();
	}
	
	public static BitVecExpr concat(BitVecExpr... syms) {
		BitVecExpr res = null;
		for (int i = 0; i < syms.length; ++i) {
			BitVecExpr sym = syms[i];
			if(i == 0)
				res = sym;
			else {
				res = ctx.mkConcat(res, sym);
			}
		}
		return (BitVecExpr) res.simplify();
	}


	public static BitVecExpr upper_half(BitVecExpr sym) {
	    int sym_len = sym.getSortSize();
	    return (BitVecExpr) extract(sym_len - 1, sym_len / 2, sym).simplify();
	}
	
	public static BitVecExpr lower_half(BitVecExpr sym) {
	    int sym_len = sym.getSortSize();
	    return (BitVecExpr) extract(sym_len / 2 - 1, 0, sym).simplify();
	}


	BitVecExpr truncate_to_size(String dest, BitVecExpr sym) {
		int dest_len = Utils.get_sym_length(dest, Config.MEM_ADDR_SIZE);
		return (BitVecExpr) extract(dest_len - 1, 0, sym).simplify();
	}

	String string_of_address(BitVecExpr address) {
	    String res = null;
	    if(is_bit_vec_num(address)) {
	        res = Utils.num_to_hex_string(((BitVecNum) address).getLong());
	    }
	    else
	    	res = address.toString();
	    return res;
	}
	
	
	public static int int_of_sym(BitVecExpr sym) {
	    int res = ((BitVecNum) sym).getInt();
	    return res;
	}
	
	public static long long_of_sym(BitVecExpr sym) {
		long res = ((BitVecNum) sym).getLong();
	    return res;
	}

	
	public static BitVecExpr extract_bytes(int high, int low, BitVecExpr sym) {
	    return extract(high * 8 - 1, low * 8, sym);
	}
	
	public static BitVecExpr neg(BitVecExpr sym) {
		return (BitVecExpr) ctx.mkBVNeg(sym).simplify();
	}

	public static BitVecExpr not_op(BitVecExpr sym) {
		return (BitVecExpr) ctx.mkBVNot(sym).simplify();
	}

	BitVecExpr update_sym_expr(BitVecExpr expr, BitVecExpr new_expr, String rel) {
		BitVecExpr res = expr;
	    if(rel.equals("or"))
	    	res = (BitVecExpr) ctx.mkBVOR(expr, new_expr).simplify();
	    else if(rel.equals("and"))
	    	res = (BitVecExpr) ctx.mkBVAND(expr, new_expr).simplify();
	    else if(rel.equals("r"))
	        res = new_expr;
	    return res;
	}

	public static boolean is_term_address(BitVecExpr address) {
	    return address.equals(TERMINAL_SYMBOL.get(Config.MEM_ADDR_SIZE));
	}

	boolean is_bv_sym_var(BitVecExpr arg) {
	    return (arg instanceof BitVecExpr && !(arg instanceof BitVecNum));
	}

	static boolean bvnum_eq(BitVecExpr lhs, BitVecExpr rhs) {
	    boolean res = false;
	    if(lhs.getSort() == rhs.getSort()) {
	        res = (lhs.equals(rhs));
	    }
	    return res;
	}
	
	public static HashMap<String, ArrayList<String>> parse_predefined_constraint(Path constraintConfigPath) {
		HashMap<String, ArrayList<String>> res = new HashMap<>();
		File file = new File(constraintConfigPath.toString());
		try (BufferedReader br = new BufferedReader(new FileReader(file))) {
		    String line;
		    ArrayList<String> constrList = null;
		    while ((line = br.readLine()) != null) {
		    	line = line.strip();
	            if(line != null && line != "") {
	                line = line.replace("\t", " ");
	                String[] lineSplit = line.strip().split(" ", 2);
	                String extFuncName = lineSplit[0].strip();
	                String constraint = lineSplit[1].strip();
	                if(res.containsKey(extFuncName)) {
	                	constrList = res.get(extFuncName);
	                	constrList.add(constraint);
	                }
	                else {
	                	constrList = new ArrayList<>();
	                	constrList.add(constraint);
	                	res.put(extFuncName, constrList);
	                }
	            }
		    }
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		} catch (IOException e) {
			e.printStackTrace();
		}
	    return res;
	}


	boolean strict_bitvec_equal(BitVecExpr left, BitVecExpr right) {
	    boolean res = true;
	    if((left instanceof BitVecNum) && (right instanceof BitVecNum)) {
	        res = bvnum_eq(left, right);
	    }
	    else if(left instanceof BitVecNum) {
	        res = false;
	    }
	    else if(right instanceof BitVecNum) {
	        res = false;
	    }
	    else
	        res = bvnum_eq(left, right);
	    return res;
	}


	public static boolean bitvec_eq(BitVecExpr v_old, BitVecExpr v) {
		boolean res = true;
	    if((v_old instanceof BitVecNum) && (v instanceof BitVecNum))
	        res = bvnum_eq(v_old, v);
	    else if(v_old instanceof BitVecNum)
	        res = false;
	    return res;
	}


	public static BitVecExpr merge_sym(BitVecExpr lhs, BitVecExpr rhs, HashMap<Long, String> address_inst_map) {
		BitVecExpr res = rhs;
	    if((lhs instanceof BitVecNum) && (rhs instanceof BitVecNum)) {
	        long lhs_num = ((BitVecNum) lhs).getLong();
	        long rhs_num = ((BitVecNum) rhs).getLong();
	        if(!address_inst_map.containsKey(rhs_num)) {
	            if(!bvnum_eq(lhs, rhs)) {
	                if(lhs_num >= NormFactory.norm.getSecStartAddr().get(Lib.RODATASEC) && lhs_num < NormFactory.norm.getSecEndAddr().get(Lib.RODATASEC))
	                    res = gen_sym(rhs.getSortSize());
	                else if(rhs_num < NormFactory.norm.getSecStartAddr().get(Lib.RODATASEC) || rhs_num >= NormFactory.norm.getSecEndAddr().get(Lib.RODATASEC))
	                    res = gen_sym(rhs.getSortSize());
	            }
	        }
	    }
	    else if(rhs instanceof BitVecNum) {
	    	long rhs_num = ((BitVecNum) rhs).getLong();
	        if(!address_inst_map.containsKey(rhs_num))
	            res = gen_sym(rhs.getSortSize());
	    }
	    return res;
	}


	public static boolean is_bottom(BitVecExpr sym, int length) {
	    return sym.equals(bottom(length));
	}

}
