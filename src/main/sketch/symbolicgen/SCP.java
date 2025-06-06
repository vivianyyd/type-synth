package customcodegen;

import java.io.OutputStream;
import java.util.Comparator;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.TreeSet;
import java.util.Vector;
import java.io.OutputStream;
import java.io.PrintWriter;

import sketch.compiler.ast.core.FEReplacer;
import sketch.compiler.passes.printers.CodePrinter;
import sketch.compiler.ast.core.Annotation;
import sketch.compiler.ast.core.FieldDecl;
import sketch.compiler.ast.core.Function;
import sketch.compiler.ast.core.Function.LibraryFcnType;
import sketch.compiler.ast.core.Function.PrintFcnType;
import sketch.compiler.ast.core.Package;
import sketch.compiler.ast.core.stmts.*;
import sketch.compiler.ast.core.typs.StructDef;
import sketch.compiler.ast.core.typs.StructDef.StructFieldEnt;
import sketch.compiler.ast.cuda.stmts.CudaSyncthreads;
import sketch.compiler.ast.promela.stmts.StmtFork;
import sketch.compiler.ast.spmd.stmts.SpmdBarrier;
import sketch.compiler.ast.spmd.stmts.StmtSpmdfork;
import sketch.util.annot.CodeGenerator;

@CodeGenerator
public class SCP extends FEReplacer {
	boolean outtags = false;
	private static final int tabWidth = 2;
	protected final PrintWriter out;
	protected int indent = 0;
	protected String pad = "";

	protected final boolean printLibraryFunctions;

	public SCP outputTags() {

		outtags = true;
		return this;
	}

	public SCP() {
		out = new PrintWriter(System.out);
		printLibraryFunctions = false;
	}

	protected void printTab() {
		if (indent * tabWidth != pad.length()) {
			StringBuffer b = new StringBuffer();
			for (int i = 0; i < indent * tabWidth; i++)
				b.append(' ');
			pad = b.toString();
		}
		out.print(pad);
	}

	protected void print(String s) {
		out.print(s);
	}

	protected void printLine(String s) {
		printTab();
		out.println(s);
		out.flush();
	}

	protected void printIndentedStatement(Statement s) {
		if (s == null) return;
		if (s instanceof StmtBlock)
			s.accept(this);
		else {
			indent++;
			s.accept(this);
			indent--;
		}
	}


	public Object visitFunction(Function func) {
		out.print("// FUNCTION START");
		if (outtags && func.getTag() != null) {
			out.println("T=" + func.getTag());
		}
//		printTab();
//		out.println("/*" + func.getCx() + "*/");
//		printTab();
		//From the custom code generator you have access to any annotations attached to the function.
		//You can use these annotations to pass information to your code generator.
		for (Entry<String, Vector<Annotation>> anitv : func.annotationSet()) {
			for (Annotation anit : anitv.getValue()) {
				out.print(anit.toString() + " ");
			}
		}
		out.print("\n");
		out.println((func.getInfo().printType == PrintFcnType.Printfcn ? "printfcn " : "") + func.toString());
		super.visitFunction(func);
		out.println("// FUNCTION END");
		out.flush();
		return func;
	}


	@Override
	public Object visitPackage(Package spec) {

		//The name resolver is used to find functions and structs matching a particular name.
		nres.setPackage(spec);
//		printLine("/* HELLO HELLO HELLO " + spec.getName() + "*/");

		for (StructDef tsOrig : spec.getStructs()) {
			StructDef ts = (StructDef) tsOrig.accept(this);
		}

		for (Iterator iter = spec.getVars().iterator(); iter.hasNext(); ) {
			FieldDecl oldVar = (FieldDecl) iter.next();
			FieldDecl newVar = (FieldDecl) oldVar.accept(this);

		}
		int nonNull = 0;

		TreeSet<Function> orderedFuncs = new TreeSet<Function>(new Comparator<Function>() {
			public int compare(Function o1, Function o2) {
				final int det_order =
						o1.getInfo().determinsitic.compareTo(o2.getInfo().determinsitic);
				return det_order + (det_order == 0 ? 1 : 0) *
						o1.getName().compareTo(o2.getName());
			}
		});
		orderedFuncs.addAll(spec.getFuncs());

		for (Function oldFunc : orderedFuncs) {
			if (oldFunc.getInfo().libraryType != LibraryFcnType.Library || printLibraryFunctions) {
				Function newFunc = (Function) oldFunc.accept(this);
			}
		}
//		printLine("/* END PACKAGE " + spec.getName() + "*/");
		return spec;
	}


	public Object visitStmtFor(StmtFor stmt) {
		if (outtags && stmt.getTag() != null) {
			out.println("T=" + stmt.getTag());
		}
		printLine("for(" + stmt.getInit() + "; " + stmt.getCond() + "; " +
				stmt.getIncr() + ")" + (stmt.isCanonical() ? "/*Canonical*/" : ""));
		printIndentedStatement(stmt.getBody());
		return stmt;
	}

	public Object visitStmtSpmdfork(StmtSpmdfork stmt) {
		if (outtags && stmt.getTag() != null) {
			out.println("T=" + stmt.getTag());
		}
		printLine("spmdfork(" + stmt.getNProc() + ")");
		printIndentedStatement(stmt.getBody());
		return stmt;
	}

	public Object visitSpmdBarrier(SpmdBarrier stmt) {
		printLine("spmdbarrier();");
		return stmt;
	}

	@Override
	public Object visitStmtIfThen(StmtIfThen stmt) {
		if (outtags && stmt.getTag() != null) {
			out.println("T=" + stmt.getTag());
		}
		printLine("if(" + stmt.getCond() + ")/*" + stmt.getCx() + "*/");
		printIndentedStatement(stmt.getCons());
		if (stmt.getAlt() != null) {
			printLine("else");
			printIndentedStatement(stmt.getAlt());
		}
		return stmt;
	}

	@Override
	public Object visitStmtWhile(StmtWhile stmt) {
		if (outtags && stmt.getTag() != null) {
			out.println("T=" + stmt.getTag());
		}
		printLine("while(" + stmt.getCond() + ")");
		printIndentedStatement(stmt.getBody());
		return stmt;
	}

	@Override
	public Object visitStmtDoWhile(StmtDoWhile stmt) {
		if (outtags && stmt.getTag() != null) {
			out.println("T=" + stmt.getTag());
		}
		printLine("do");
		printIndentedStatement(stmt.getBody());
		printLine("while(" + stmt.getCond() + ")");
		return stmt;
	}

	@Override
	public Object visitStmtLoop(StmtLoop stmt) {
		if (outtags && stmt.getTag() != null) {
			out.println("T=" + stmt.getTag());
		}
		printLine("loop(" + stmt.getIter() + ")");
		printIndentedStatement(stmt.getBody());
		return stmt;
	}

	@Override
	public Object visitStmtFork(StmtFork stmt) {
		if (outtags && stmt.getTag() != null) {
			out.println("T=" + stmt.getTag());
		}
		printLine("fork(" + stmt.getLoopVarDecl() + "; " + stmt.getIter() + ")");
		printIndentedStatement(stmt.getBody());
		return stmt;
	}

	@Override
	public Object visitStmtBlock(StmtBlock stmt) {
		if (outtags && stmt.getTag() != null) {
			out.println("T=" + stmt.getTag());
		}
		printLine("{");
		indent++;
		super.visitStmtBlock(stmt);
		indent--;
		printLine("}");
		out.flush();
		return stmt;
	}


	@Override
	public Object visitStmtAssert(StmtAssert stmt) {
//		if (outtags && stmt.getTag() != null) {
//			out.println("T=" + stmt.getTag());
//		}
//		printLine(stmt.toString() + ";" + " //" + stmt.getMsg());
		return super.visitStmtAssert(stmt);
	}

	@Override
	public Object visitStmtAssume(StmtAssume stmt) {
		if (outtags && stmt.getTag() != null) {
			out.println("T=" + stmt.getTag());
		}
		printLine(stmt.toString() + ";" + " //" + stmt.getMsg());
		return super.visitStmtAssume(stmt);
	}

	@Override
	public Object visitStmtAssign(StmtAssign stmt) {
		if (outtags && stmt.getTag() != null) {
			out.println("T=" + stmt.getTag());
		}
		printLine(stmt.toString() + ';');
		return super.visitStmtAssign(stmt);
	}


	@Override
	public Object visitStmtBreak(StmtBreak stmt) {
		printLine(stmt.toString());
		return super.visitStmtBreak(stmt);
	}

	@Override
	public Object visitStmtContinue(StmtContinue stmt) {
		printLine(stmt.toString());
		return super.visitStmtContinue(stmt);
	}

	@Override
	public Object visitStmtEmpty(StmtEmpty stmt) {
		printLine(stmt.toString());
		return super.visitStmtEmpty(stmt);
	}

	@Override
	public Object visitStmtExpr(StmtExpr stmt) {
		if (outtags && stmt.getTag() != null) {
			out.println("T=" + stmt.getTag());
		}
		{
//			printLine(stmt.toString() + ";");
			
			String input = stmt.toString();
			if (input.indexOf("(") == input.lastIndexOf(")") - 1) {
				printLine(stmt.toString() + ";");
			} else {
				int lastCommaIndex = input.lastIndexOf(",");

				int lhsIndex = lastCommaIndex;
				String optionalParen = "";
				if (lastCommaIndex == -1) {
					optionalParen = "(";
					lhsIndex = input.lastIndexOf("(");
				}
				int closingParenIndex = input.indexOf(")", lhsIndex);
				String beforeLastComma = input.substring(0, lhsIndex).trim();
				String afterLastComma = input.substring(lhsIndex + 1, closingParenIndex).trim();

				printLine(afterLastComma + " = " + beforeLastComma + optionalParen + ")");
			}
		}
		return stmt;
	}

	public Object visitStmtFunDef(StmtFunDecl stmt) {
		printLine(stmt.toString());
		return stmt;
	}

	@Override
	public Object visitStmtReturn(StmtReturn stmt) {
		printLine(stmt.toString());
		return super.visitStmtReturn(stmt);
	}

	// @Override
	// public Object visitStmtAngelicSolve(StmtAngelicSolve stmt) {
	// printLine("angelic_solve");
	// return super.visitStmtAngelicSolve(stmt);
	// }

	@Override
	public Object visitStmtVarDecl(StmtVarDecl stmt) {
		if (outtags && stmt.getTag() != null) {
			out.println("T=" + stmt.getTag());
		}

		for (int i = 0; i < stmt.getNumVars(); i++) {
			String str = stmt.getType(i) + " " + stmt.getName(i);
			if (stmt.getInit(i) != null) {
				str += " = " + stmt.getInit(i);
			}
			printLine(str + ";");
		}

		return stmt;
	}

	@Override
	public Object visitFieldDecl(FieldDecl field) {
		printLine(field.toString());
		return super.visitFieldDecl(field);
	}

	public Object visitStmtReorderBlock(StmtReorderBlock block) {
		printLine("reorder");
		block.getBlock().accept(this);
		return block;
	}

	public Object visitStmtInsertBlock(StmtInsertBlock sib) {
		printLine("insert");
		sib.getInsertStmt().accept(this);
		printLine("into");
		sib.getIntoBlock().accept(this);
		return sib;
	}

	public Object visitStmtAtomicBlock(StmtAtomicBlock block) {
		if (outtags && block.getTag() != null) {
			out.println("T=" + block.getTag());
		}
		if (block.isCond()) {
			printLine("atomic(" + block.getCond().accept(this) + ")");
		} else {
			printLine("atomic");
		}
		visitStmtBlock(block.getBlock());
		return block;
	}

	@Override
	public Object visitStructDef(StructDef ts) {
// 	    printLine("struct " + ts.getName() + " {");
//         for (StructFieldEnt ent : ts.getFieldEntriesInOrder()) {
// 	        printLine("    " + ent.getType().toString() + " " + ent.getName() + ";");
// 	    }
//         for (Entry<String, Vector<Annotation>> at : ts.annotationSet()) {
//             for (Annotation ann : at.getValue()) {
//                 printLine("    " + ann);
//             }
//         }
// 	    printLine("}");
		return ts;
	}

	@Override
	public Object visitStmtMinLoop(StmtMinLoop stmtMinLoop) {
		printTab();
		print("minloop");
		printIndentedStatement(stmtMinLoop.getBody());
		return stmtMinLoop;
	}

	@Override
	public Object visitStmtMinimize(StmtMinimize stmtMinimize) {
		printLine("minimize(" + stmtMinimize.getMinimizeExpr().accept(this) + ")");
		return stmtMinimize;
	}

	@Override
	public Object visitCudaSyncthreads(CudaSyncthreads cudaSyncthreads) {
		printLine("__syncthreads();");
		return cudaSyncthreads;
	}
}
