//==--- tools/clang-check/ClangInterpreter.cpp - Clang Interpreter tool --------------===//
//===----------------------------------------------------------------------===//
#include <stdio.h>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/Decl.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"

using namespace clang;

class StackFrame {
   /// StackFrame maps Variable Declaration to Value
   /// Which are either integer or addresses (also represented using an Integer value)
   std::map<Decl*, int> mVars;
   std::map<Stmt*, int> mExprs;
   /// The current stmt
   Stmt * mPC;

   bool exited = false;
   int retValue = 0;

public:
   StackFrame() : mVars(), mExprs(), mPC() {
   }

   void bindDecl(Decl* decl, int val) {
      mVars[decl] = val;
   }    
   int getDeclVal(Decl * decl) {
      assert (mVars.find(decl) != mVars.end());
      return mVars.find(decl)->second;
   }
   void bindStmt(Stmt * stmt, int val) {
	   mExprs[stmt] = val;
   }
   int getStmtVal(Stmt * stmt) {
	   assert (mExprs.find(stmt) != mExprs.end());
	   return mExprs[stmt];
   }
   void setPC(Stmt * stmt) {
	   mPC = stmt;
   }
   Stmt * getPC() {
	   return mPC;
   }
   bool isExited() {
      return exited;
   }
   void setRetStatus(int val = 0) {
      exited = true;
      retValue = val;
   }
   int getRetValue() {
      return retValue;
   }
};

/// Heap maps address to a value
class Heap {

   int hsize = 0;
   std::vector<int> heap;

public:
   int Malloc(int size) {
      int res = hsize;
      hsize += size;
      heap.resize(hsize);
      return res;
   }
   void Free (int addr) {
      // Do nothing
   }
   void Update(int addr, int val) {
      heap[addr] = val;
   }
   int get(int addr) {
      return heap[addr];
   }
};

class Environment {
   std::vector<StackFrame> mStack;

   FunctionDecl * mFree;				/// Declartions to the built-in functions
   FunctionDecl * mMalloc;
   FunctionDecl * mInput;
   FunctionDecl * mOutput;

   FunctionDecl * mEntry;

   Heap mHeap;
public:
   /// Get the declartions to the built-in functions
   Environment() : mStack(), mFree(NULL), mMalloc(NULL), mInput(NULL), mOutput(NULL), mEntry(NULL) {
   }

   bool checkExited() {
      return mStack.back().isExited();
   }

   /// Initialize the Environment
   void init(TranslationUnitDecl * unit) {
      mStack.push_back(StackFrame());
	   for (TranslationUnitDecl::decl_iterator i =unit->decls_begin(), e = unit->decls_end(); i != e; ++ i) {
		   if (FunctionDecl * fdecl = dyn_cast<FunctionDecl>(*i) ) {
			   if (fdecl->getName().equals("FREE")) mFree = fdecl;
			   else if (fdecl->getName().equals("MALLOC")) mMalloc = fdecl;
			   else if (fdecl->getName().equals("GET")) mInput = fdecl;
			   else if (fdecl->getName().equals("PRINT")) mOutput = fdecl;
			   else if (fdecl->getName().equals("main")) mEntry = fdecl;
		   }
         else if (VarDecl * vdecl = dyn_cast<VarDecl>(*i) ) {
            if (vdecl->getType()->isArrayType()) {
               declarray(vdecl);
            } else if (vdecl->hasInit()) {
               if (isa<IntegerLiteral>(vdecl->getInit())) {
                  IntegerLiteral *integer = dyn_cast<IntegerLiteral>(vdecl->getInit());
                  int intVal = integer->getValue().getSExtValue();
                  mStack.back().bindDecl(vdecl, intVal);
               }
            } else {
               mStack.back().bindDecl(vdecl, 0);
            }
         }
	   }
   }

   FunctionDecl * getEntry() {
	   return mEntry;
   }

   /// !TODO Support comparison operation
   void binop(BinaryOperator *bop) {
	   Expr * left = bop->getLHS();
	   Expr * right = bop->getRHS();

	   if (bop->isAssignmentOp()) {
		   int val = mStack.back().getStmtVal(right);
		   mStack.back().bindStmt(left, val);
		   if (DeclRefExpr * declexpr = dyn_cast<DeclRefExpr>(left)) {
			   Decl * decl = declexpr->getFoundDecl();
			   mStack.back().bindDecl(decl, val);
		   } else if (auto array = dyn_cast<ArraySubscriptExpr>(left)) {
            int base = mStack.back().getStmtVal(array->getLHS()->IgnoreImpCasts());
            int offset = mStack.back().getStmtVal(array->getRHS());
            mHeap.Update(base + offset, val);
         } else if(auto unaryexpr = dyn_cast<UnaryOperator>(left)) {
            int addr = mStack.back().getStmtVal(unaryexpr->getSubExpr());
            mHeap.Update(addr, val);
         }
	   } else {
         int lval = mStack.back().getStmtVal(left);
         int rval = mStack.back().getStmtVal(right);
         if(bop->isComparisonOp()) {
            switch (bop->getOpcode())
            {
            case BO_LT:
               mStack.back().bindStmt(bop, lval < rval);
               break;
            
            case BO_GT:
               mStack.back().bindStmt(bop, lval > rval);
               break;
            
            case BO_LE:
               mStack.back().bindStmt(bop, lval <= rval);
               break;

            case BO_GE:
               mStack.back().bindStmt(bop, lval >= rval);
               break;

            case BO_EQ:
               mStack.back().bindStmt(bop, lval == rval);
               break;

            case BO_NE:
               mStack.back().bindStmt(bop, lval != rval);
               break;

            default:
               break;
            }
         }

         if(bop->isAdditiveOp()) {
            switch (bop->getOpcode())
            {
            case BO_Add:
               mStack.back().bindStmt(bop, lval + rval);
               break;

            case BO_Sub:
               mStack.back().bindStmt(bop, lval - rval);
               break;

            default:
               break;
            }
         }

         if(bop->isMultiplicativeOp()) {
            switch (bop->getOpcode())
            {
            case BO_Mul:
               mStack.back().bindStmt(bop, lval * rval);
               break;
            
            case BO_Div:
               mStack.back().bindStmt(bop, lval / rval);
               break;

            default:
               break;
            }
         }
      }
   }

   void decl(DeclStmt * declstmt) {
	   for (DeclStmt::decl_iterator it = declstmt->decl_begin(), ie = declstmt->decl_end();
			   it != ie; ++ it) {
		   Decl * decl = *it;
		   if (VarDecl * vardecl = dyn_cast<VarDecl>(decl)) {
            if (vardecl->getType()->isArrayType()) {
               declarray(vardecl);
            } else if (vardecl->hasInit()) {
               int val = mStack.back().getStmtVal(vardecl->getInit());
               mStack.back().bindDecl(vardecl, val);
            } else {
   			   mStack.back().bindDecl(vardecl, 0);
            }
		   }
	   }
   }
   void declref(DeclRefExpr * declref) {
	   mStack.back().setPC(declref);
	   if (declref->getType()->isIntegerType()
         || declref->getType()->isArrayType()
         || declref->getType()->isPointerType()) {
		   Decl* decl = declref->getFoundDecl();

		   int val = mStack.back().getDeclVal(decl);
		   mStack.back().bindStmt(declref, val);
	   }
   }

   void cast(CastExpr * castexpr) {
	   mStack.back().setPC(castexpr);
	   if (castexpr->getType()->isIntegerType()
         || castexpr->getSubExpr()->getType()->isPointerType()) {
		   Expr * expr = castexpr->getSubExpr();
		   int val = mStack.back().getStmtVal(expr);
		   mStack.back().bindStmt(castexpr, val );
	   }
   }
	
   void paren(ParenExpr * parenexpr) {
	   if (parenexpr->getSubExpr()->getType()->isPointerType()) {
		   Expr * expr = parenexpr->getSubExpr();
		   int val = mStack.back().getStmtVal(expr);
		   mStack.back().bindStmt(parenexpr, val );
	   }
   }
   
   /// !TODO Support Function Call
   bool call(CallExpr * callexpr) {
	   mStack.back().setPC(callexpr);
	   int val = 0;
	   FunctionDecl * callee = callexpr->getDirectCallee();
	   if (callee == mInput) {
		  llvm::errs() << "Please Input an Integer Value : ";
		  scanf("%d", &val);

		  mStack.back().bindStmt(callexpr, val);
	   } else if (callee == mOutput) {
		   Expr * decl = callexpr->getArg(0);
		   val = mStack.back().getStmtVal(decl);
		   llvm::errs() << val;
	   } else if (callee == mMalloc) {
         Expr * msize = callexpr->getArg(0);
         val = mStack.back().getStmtVal(msize);
         mStack.back().bindStmt(callexpr, mHeap.Malloc(val));
      } else if (callee == mFree) {
         Expr * fsize = callexpr->getArg(0);
         val = mStack.back().getStmtVal(fsize);
         mHeap.Free(val);
      } else {
		   /// You could add your code here for Function call Return
         std::vector<int> args;
         for(auto i = callexpr->arg_begin(); i != callexpr->arg_end(); i++) {
            args.push_back(mStack.back().getStmtVal(*i));
         }
         mStack.push_back(StackFrame());
         auto args_it = args.begin();
         for(auto i = callee->param_begin(); i != callee->param_end(); i++) {
            mStack.back().bindDecl(*i, *args_it), args_it++;
         }
         
         return true;
	   }
      return false;
   }

   void intliteral(IntegerLiteral *integer) {
      int val = integer->getValue().getSExtValue();
      mStack.back().bindStmt(integer, val);
	}

   void Return(ReturnStmt *ret) {
      int retVal = mStack.back().getStmtVal(ret->getRetValue());
      mStack.back().setRetStatus(retVal);
   }

   void endcall(CallExpr * callexpr) {
      int retValue = mStack.back().getRetValue();
      mStack.pop_back();
      mStack.back().bindStmt(callexpr, retValue);
   }

   int getCond(Expr * expr) {
      return mStack.back().getStmtVal(expr);
   }

   void unaryop(UnaryOperator * uop) {
      Expr *expr = uop->getSubExpr();
      int val = mStack.back().getStmtVal(expr);
      switch (uop->getOpcode())
      {
      case UO_Plus:
         mStack.back().bindStmt(uop, val);
         break;
      
      case UO_Minus:
         mStack.back().bindStmt(uop, -val);
         break;
      
      case UO_Deref:
         mStack.back().bindStmt(uop, mHeap.get(val));
         break;
         
      default:
         break;
      }
   }

   void unarysizeof(UnaryExprOrTypeTraitExpr * uexpr) {
      mStack.back().bindStmt(uexpr, 1);
   }

   void arraysub(ArraySubscriptExpr * subexpr) {
      int base = mStack.back().getStmtVal(subexpr->getLHS()->IgnoreImpCasts());
      int offset = mStack.back().getStmtVal(subexpr->getRHS());
      mStack.back().bindStmt(subexpr, mHeap.get(base + offset));
   }

   void declarray(VarDecl * vardecl) {
      auto array = dyn_cast<ConstantArrayType>(vardecl->getType().getTypePtr());
      int len = array->getSize().getSExtValue();
      mStack.back().bindDecl(vardecl, mHeap.Malloc(len));
   }
};


