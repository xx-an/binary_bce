package common;

import java.io.File;
import java.io.FileNotFoundException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Scanner;
import java.util.function.Function;

import com.microsoft.z3.*;
import com.microsoft.z3.enumerations.Z3_sort_kind;

public class Helper {
	public static int cnt = 0;
	public static int mem_cnt = 0;
	public static int stdout_mem_cnt = 0;
	
	public static Context ctx = new Context();
	public static final BitVecExpr STDOUT_ADDR = (BitVecExpr) ctx.mkBVConst("stdout", Lib.DEFAULT_REG_LEN);
	
	public static HashMap<String, Function<Tuple<BitVecExpr, BitVecExpr>, BoolExpr>> LOGIC_OP_FUNC_MAP;
	
	public static HashMap<String, Function<Tuple<BoolExpr, BoolExpr>, BoolExpr>> LOGIC_OP_FUNC_MAP_BOOLEXPR;
	
	Helper() {
		LOGIC_OP_FUNC_MAP = new HashMap<String, Function<Tuple<BitVecExpr, BitVecExpr>, BoolExpr>>();
		LOGIC_OP_FUNC_MAP.put("==", arg -> is_equal(arg.x, arg.y));
		LOGIC_OP_FUNC_MAP.put("<>", arg -> not_equal(arg.x, arg.y));
		LOGIC_OP_FUNC_MAP.put("!=", arg -> not_equal(arg.x, arg.y));
		
		LOGIC_OP_FUNC_MAP_BOOLEXPR = new HashMap<String, Function<Tuple<BoolExpr, BoolExpr>, BoolExpr>>();
		LOGIC_OP_FUNC_MAP_BOOLEXPR.put("==", arg -> is_equal(arg.x, arg.y));
		LOGIC_OP_FUNC_MAP_BOOLEXPR.put("<>", arg -> not_equal(arg.x, arg.y));
		LOGIC_OP_FUNC_MAP_BOOLEXPR.put("!=", arg -> not_equal(arg.x, arg.y));
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
	    BitVecExpr res = ctx.mkBVConst("m#" + expr, length);
	    mem_cnt += 1;
	    return res;
	}
	 
  
	public static BitVecExpr gen_stdout_mem_sym(int length) {
		BitVecExpr stdout = ctx.mkBVConst("stdout", length);
		BitVecNum smc = ctx.mkBV(stdout_mem_cnt, length);
		BitVecExpr res = ctx.mkBVAdd(stdout, smc);
	    stdout_mem_cnt += 1;
	    return res;
	}

	public static BitVecExpr gen_seg_reg_sym(String name, int length) {
		BitVecExpr res = ctx.mkBVConst("_" + name, length);
	    return res;
	}
	
	
	public static BitVecExpr substitute_sym_val(BitVecExpr arg, BitVecExpr prev_val, BitVecExpr new_val) {
		BitVecExpr res = (BitVecExpr) arg.substitute(prev_val, new_val);
	    return res;
	}
	
	
	public static BitVecExpr gen_sym_x(int length) {
		BitVecExpr res = ctx.mkBVConst("x", length);
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
	
	
	public static BoolExpr is_equal(BitVecExpr x, BitVecExpr y) {
		return ctx.mkEq(x, y);
	}
	
	public static BoolExpr is_equal(BoolExpr x, BoolExpr y) {
		return ctx.mkEq(x, y);
	}
	
	public static BoolExpr is_equal(BitVecExpr x, int y) {
		BitVecExpr bv_y = gen_bv_num(y, x.getSortSize());
		return ctx.mkEq(x, bv_y);
	}
	
	public static BoolExpr is_less(BitVecExpr x, BitVecExpr y) {
		return ctx.mkBVSLT(x, y);
	}
	
	
	public static BoolExpr sym_true() {
		return ctx.mkTrue();
	}
	
	
	public static BoolExpr sym_false() {
		return ctx.mkFalse();
	}
	
	public static BitVecExpr bv_add(BitVecExpr x, BitVecExpr y) {
		return ctx.mkBVAdd(x, y);
	}
	
	public static BitVecExpr bv_add(BitVecExpr x, int y) {
		int size = x.getSortSize();
		BitVecNum bv_y = ctx.mkBV(y, size);
		return ctx.mkBVAdd(x, bv_y);
	}
	
	public static BitVecExpr bv_sub(BitVecExpr x, BitVecExpr y) {
		return ctx.mkBVSub(x, y);
	}
	
	public static BitVecExpr bv_sub(BitVecExpr x, int y) {
		int size = x.getSortSize();
		BitVecNum bv_y = ctx.mkBV(y, size);
		return ctx.mkBVSub(x, bv_y);
	}
	
	public static BitVecExpr bv_and(BitVecExpr x, BitVecExpr y) {
		return ctx.mkBVAND(x, y);
	}
	
	public static BitVecExpr bv_and(BitVecExpr x, int y) {
		int size = x.getSortSize();
		BitVecNum bv_y = ctx.mkBV(y, size);
		return bv_and(x, bv_y);
	}
	
	public static BitVecExpr bv_or(BitVecExpr x, BitVecExpr y) {
		return ctx.mkBVOR(x, y);
	}
	
	public static BitVecExpr bv_xor(BitVecExpr x, BitVecExpr y) {
		return ctx.mkBVXOR(x, y);
	}
	
	
	public static BitVecExpr bv_lshift(BitVecExpr x, BitVecExpr y) {
		return ctx.mkBVSHL(x, y);
	}
	
	public static BitVecExpr bv_lshift(BitVecExpr x, int y) {
		BitVecExpr bv_y = gen_bv_num(y, x.getSortSize());
		return ctx.mkBVSHL(x, bv_y);
	}
	
	public static BitVecExpr bv_arith_rshift(BitVecExpr x, BitVecExpr y) {
		return ctx.mkBVASHR(x, y);
	}
	
	public static BitVecExpr bv_arith_rshift(BitVecExpr x, int y) {
		BitVecExpr bv_y = gen_bv_num(y, x.getSortSize());
		return ctx.mkBVASHR(x, bv_y);
	}
	
	public static BitVecExpr bv_logic_rshift(BitVecExpr x, BitVecExpr y) {
		return ctx.mkBVLSHR(x, y);
	}
	
	public static BitVecExpr bv_logic_rshift(BitVecExpr x, int y) {
		BitVecExpr bv_y = gen_bv_num(y, x.getSortSize());
		return ctx.mkBVLSHR(x, bv_y);
	}
	
	public static BitVecExpr bv_mult(BitVecExpr x, BitVecExpr y) {
		return ctx.mkBVMul(x, y);
	}
	
	public static BitVecExpr bv_udiv(BitVecExpr x, BitVecExpr y) {
		return ctx.mkBVUDiv(x, y);
	}
	
	public static BitVecExpr bv_sdiv(BitVecExpr x, BitVecExpr y) {
		return ctx.mkBVSDiv(x, y);
	}
	
	public static BitVecExpr bv_umod(BitVecExpr x, BitVecExpr y) {
		return ctx.mkBVURem(x, y);
	}
	
	public static BitVecExpr bv_smod(BitVecExpr x, BitVecExpr y) {
		return ctx.mkBVSRem(x, y);
	}
	
	public static BoolExpr bv_and(BoolExpr... x) {
		return ctx.mkAnd(x);
	}
	
	public static BoolExpr bv_or(BoolExpr... x) {
		return ctx.mkOr(x);
	}
	
	public static BoolExpr bv_xor(BoolExpr x, BoolExpr y) {
		return ctx.mkXor(x, y);
	}
	
	public static BoolExpr bv_not(BoolExpr x) {
		return ctx.mkNot(x);
	}
	
	BitVecExpr sym_op(String op, BitVecExpr x, BitVecExpr y) {
		BitVecExpr res = null;
	    if(op == "-")
	        res = ctx.mkBVSub(x, y);
	    else if(op == "+")
	        res = ctx.mkBVAdd(x, y);
	    return (BitVecExpr) res.simplify();
	}
	
	
	static BoolExpr not_equal(BitVecExpr x, BitVecExpr y) {
		return (BoolExpr) ctx.mkNot(ctx.mkEq(x, y)).simplify();
	}
	
	public static BoolExpr not_equal(BitVecExpr x, int y) {
		BitVecExpr bv_y = gen_bv_num(y, x.getSortSize());
		return not_equal(x, bv_y);
	}
	
	BoolExpr not_equal(BoolExpr x, BoolExpr y) {
		return (BoolExpr) ctx.mkNot(ctx.mkEq(x, y)).simplify();
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
	
	
	public static Model check_pred_satisfiable(ArrayList<BoolExpr> predicates) {
		Solver s = ctx.mkSolver();
	    for(BoolExpr pred : predicates)
	        s.add(pred);
	    Model model = null;
	    if (s.check() == Status.SATISFIABLE)
	    	model = s.getModel();
	    return model;
	}


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
		return ctx.mkSignExt(length, sym);
	}
	
	
	public static BitVecExpr zero_ext(int length, BitVecExpr sym) {
		return ctx.mkZeroExt(length, sym);
	}

	
	public static BitVecExpr extract(int high, int low, BitVecExpr sym) {
		return ctx.mkExtract(high, low, sym);
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
		int dest_len = Utils.get_sym_length(dest, Lib.DEFAULT_REG_LEN);
		return (BitVecExpr) extract(dest_len - 1, 0, sym).simplify();
	}

	String string_of_address(BitVecExpr address) {
	    String res = null;
	    if(is_bit_vec_num(address)) {
	        res = Integer.toHexString(((BitVecNum) address).getInt());
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
		return ctx.mkBVNeg(sym);
	}

	public static BitVecExpr not_op(BitVecExpr sym) {
		return ctx.mkBVNot(sym);
	}

	BitVecExpr update_sym_expr(BitVecExpr expr, BitVecExpr new_expr, String rel) {
		BitVecExpr res = expr;
	    if(rel == "or")
	    	res = (BitVecExpr) ctx.mkBVOR(expr, new_expr).simplify();
	    else if(rel == "and")
	    	res = (BitVecExpr) ctx.mkBVAND(expr, new_expr).simplify();
	    else if(rel == "r")
	        res = new_expr;
	    return res;
	}

	BoolExpr is_term_address(BitVecExpr address) {
	    return is_equal(address, ctx.mkBVConst("x", Lib.DEFAULT_REG_LEN));
	}

	boolean is_bv_sym_var(BitVecExpr arg) {
	    return (arg instanceof BitVecExpr && !(arg instanceof BitVecNum));
	}

	static boolean bvnum_eq(BitVecExpr lhs, BitVecExpr rhs) {
	    boolean res = false;
	    if(lhs.getSort() == rhs.getSort()) {
	        res = (lhs == rhs);
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
	        int lhs_num = ((BitVecNum) lhs).getInt();
	        int rhs_num = ((BitVecNum) rhs).getInt();
	        if(!address_inst_map.containsKey(rhs_num)) {
	            if(!bvnum_eq(lhs, rhs)) {
	                if(lhs_num >= GlobalVar.binary_info.rodata_start_addr && lhs_num < GlobalVar.binary_info.rodata_end_addr)
	                    res = gen_sym(rhs.getSortSize());
	                else if(rhs_num < GlobalVar.binary_info.rodata_start_addr || rhs_num >= GlobalVar.binary_info.rodata_end_addr)
	                    res = gen_sym(rhs.getSortSize());
	            }
	        }
	    }
	    else if(rhs instanceof BitVecNum) {
	    	int rhs_num = ((BitVecNum) rhs).getInt();
	        if(!address_inst_map.containsKey(rhs_num))
	            res = gen_sym(rhs.getSortSize());
	    }
	    return res;
	}


	public static boolean is_bottom(BitVecExpr sym, int length) {
	    return sym == bottom(length);
	}


	HashMap<String, ArrayList<String>> parse_predefined_constraint(String constraint_config_file) throws FileNotFoundException {
		HashMap<String, ArrayList<String>> res = new HashMap<String, ArrayList<String>>();
		File f = new File(constraint_config_file);
		Scanner sn = new Scanner(f);
		while (sn.hasNextLine()) {
	        String line = sn.nextLine();
	        line = line.strip();
	        if(line != null) {
                line = line.replace("\t", " ");
                String[] line_split = line.strip().split(" ", 1);
                String ext_func_name = line_split[0].strip();
                String constraint = line_split[1].strip();
                if(res.containsKey(constraint)) {
                	ArrayList<String> constraint_list = res.get(ext_func_name);
                	constraint_list.add(constraint);
                }
                else {
                	ArrayList<String> constraint_list = new ArrayList<String>();
                	constraint_list.add(constraint);
                	res.put(ext_func_name, constraint_list);
                }
	        }
		}
	    return res;
	}


}
