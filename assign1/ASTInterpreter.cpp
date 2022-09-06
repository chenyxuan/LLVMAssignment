//==--- tools/clang-check/ClangInterpreter.cpp - Clang Interpreter tool --------------===//
//===----------------------------------------------------------------------===//

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/EvaluatedExprVisitor.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendAction.h"
#include "clang/Tooling/Tooling.h"

using namespace clang;

#include "Environment.h"

class InterpreterVisitor : 
   public EvaluatedExprVisitor<InterpreterVisitor> {
public:
   explicit InterpreterVisitor(const ASTContext &context, Environment * env)
   : EvaluatedExprVisitor(context), mEnv(env) {}
   virtual ~InterpreterVisitor() {}

   virtual void VisitBinaryOperator (BinaryOperator * bop) {
      if (mEnv->checkExited()) {
         return;
      }
	   VisitStmt(bop);
	   mEnv->binop(bop);
   }
   virtual void VisitDeclRefExpr(DeclRefExpr * expr) {
      if (mEnv->checkExited()) {
         return;
      }
	   VisitStmt(expr);
	   mEnv->declref(expr);
   }
   virtual void VisitCastExpr(CastExpr * expr) {
      if (mEnv->checkExited()) {
         return;
      }
	   VisitStmt(expr);
	   mEnv->cast(expr);
   }
   virtual void VisitCallExpr(CallExpr * call) {
      if (mEnv->checkExited()) {
         return;
      }
	   VisitStmt(call);
      if (mEnv->call(call)) {
         Visit(call->getDirectCallee()->getBody());
         mEnv->endcall(call);
      }
   }
   virtual void VisitDeclStmt(DeclStmt * declstmt) {
      if (mEnv->checkExited()) {
         return;
      }
      VisitStmt(declstmt);
	   mEnv->decl(declstmt);
   }
   virtual void VisitIfStmt(IfStmt * ifstmt) {
      if (mEnv->checkExited()) {
         return;  
      }
      Expr *cond = ifstmt->getCond();
      Visit(cond);
      if (mEnv->getCond(cond)) {
         Visit(ifstmt->getThen());
      } else {
         if (ifstmt->getElse()) {
            Visit(ifstmt->getElse());
         }
      }
   }
   virtual void VisitWhileStmt(WhileStmt *whilestmt) {
      if (mEnv->checkExited()) {
         return;
      }
      Expr *cond = whilestmt->getCond();
      Visit(cond);
      while (mEnv->getCond(cond)) {
         Visit(whilestmt->getBody());
         Visit(cond);
      }
   }
   virtual void VisitForStmt(ForStmt *forstmt) {
      if (mEnv->checkExited()) {
         return;
      }

      if(forstmt->getInit()) {
         Visit(forstmt->getInit());
      }

      while(true) {
         Expr *cond = forstmt->getCond();

         Visit(cond);
         if(mEnv->getCond(cond)) {
            Visit(forstmt->getBody());
            Visit(forstmt->getInc());
         } else {
            break;
         }
      }
   }
   virtual void VisitIntegerLiteral (IntegerLiteral * integer) {
      if (mEnv->checkExited()) {
         return;
      }
      mEnv->intliteral(integer);
   }
   virtual void VisitReturnStmt(ReturnStmt *returnStmt) {
      if (mEnv->checkExited()) {
         return;
      }
      Visit(returnStmt->getRetValue());
      mEnv->Return(returnStmt);
   }
   virtual void VisitUnaryOperator(UnaryOperator *uop) {
      VisitStmt(uop);
      mEnv->unaryop(uop);
   }
   virtual void VisitUnaryExprOrTypeTraitExpr(UnaryExprOrTypeTraitExpr *uexpr) {
      VisitStmt(uexpr);
      mEnv->unarysizeof(uexpr);
   }
   virtual void VisitArraySubscriptExpr(ArraySubscriptExpr *subexpr) {
      VisitStmt(subexpr);
      mEnv->arraysub(subexpr);
   }
   virtual void VisitParenExpr(ParenExpr *expr) {
	   VisitStmt(expr);
	   mEnv->paren(expr);
   }
private:
   Environment * mEnv;
};

class InterpreterConsumer : public ASTConsumer {
public:
   explicit InterpreterConsumer(const ASTContext& context) : mEnv(),
   	   mVisitor(context, &mEnv) {
   }
   virtual ~InterpreterConsumer() {}

   virtual void HandleTranslationUnit(clang::ASTContext &Context) {
	   TranslationUnitDecl * decl = Context.getTranslationUnitDecl();
	   mEnv.init(decl);

	   FunctionDecl * entry = mEnv.getEntry();
	   mVisitor.VisitStmt(entry->getBody());
  }
private:
   Environment mEnv;
   InterpreterVisitor mVisitor;
};

class InterpreterClassAction : public ASTFrontendAction {
public: 
  virtual std::unique_ptr<clang::ASTConsumer> CreateASTConsumer(
    clang::CompilerInstance &Compiler, llvm::StringRef InFile) {
    return std::unique_ptr<clang::ASTConsumer>(
        new InterpreterConsumer(Compiler.getASTContext()));
  }
};

int main (int argc, char ** argv) {
   if (argc > 1) {
       clang::tooling::runToolOnCode(std::unique_ptr<clang::FrontendAction>(new InterpreterClassAction), argv[1]);
   }
}
