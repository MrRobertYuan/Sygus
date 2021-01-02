from z3 import *

verbose=False

def DeclareVar(sort,name):
    if sort=="Int":
        return Int(name)
    if sort=='Bool':
        return Bool(name)

def getSort(sort):
    if sort=="Int":
        return IntSort()
    if sort=="Bool":
        return BoolSort()

def toString(Expr, Bracket=True, ForceBracket=False):
    if type(Expr)==str:
        return Expr
    if type(Expr)==tuple:
        return (str(Expr[1])) # todo: immediate 
    subexpr=[]
    for expr in Expr:
        if type(expr)==list:
            subexpr.append(toString(expr, ForceBracket=ForceBracket))
        elif type(expr)==tuple:
            subexpr.append(str(expr[1]))
        else:
            subexpr.append(expr)

    if not Bracket:
        #print subexpr
        return "%s"%(' '.join(subexpr))
    # Avoid Redundant Brackets
    if ForceBracket:
        return "(%s)"%(' '.join(subexpr))
    if len(subexpr)==1:
        return "%s"%(' '.join(subexpr))
    else:
        return "(%s)"%(' '.join(subexpr))

# 解析输入
def ReadQuery(bmExpr):
    SynFunExpr=[]
    VarDecMap={}
    Constraints=[]
    FunDefMap={}
    for expr in bmExpr:
        if len(expr)==0:
            continue
        elif expr[0]=='synth-fun':
            SynFunExpr=expr
        elif expr[0]=='declare-var':
            VarDecMap[expr[1]]=expr
        elif expr[0]=='constraint':
            Constraints.append(expr)
        elif expr[0]=='define-fun':
            FunDefMap[expr[1]]=expr
    
    if verbose:
        print(SynFunExpr)
        print(VarDecMap)
        print(FunDefMap)
        print(Constraints)
    
    VarTable={}
    # Declare Var
    for var in VarDecMap:
        VarTable[var]=DeclareVar(VarDecMap[var][2],var)

    # Declare Target Function
    class SynFunction:
        def __init__(self, SynFunExpr):
            self.name=SynFunExpr[1]
            # TODO: arg and ret sort
            self.argList=SynFunExpr[2]
            self.retSort=SynFunExpr[3]
            self.Sorts=[]
            for expr in self.argList:
                self.Sorts.append(getSort(expr[1]))
            self.Sorts.append(getSort(self.retSort))
            self.targetFunction=Function('__TARGET_FUNCTION__', *(self.Sorts))
    synFunction=SynFunction(SynFunExpr)

    def magic(i):
        MAGIC_NUMBER = [543, 1245, 3214, 121456, 12341, 87965, 3245, 728]
        if i >= len(MAGIC_NUMBER):
            return 777
        else:
            return MAGIC_NUMBER[i]
    
    class Checker:
        def __init__(self, VarTable,  synFunction, Constraints):
            self.VarTable=VarTable
            self.synFunction=synFunction
            self.Constraints=Constraints
            self.solver=Solver()
            self.spec_smt2_string = '\n'.join([f'(assert {toString(c[1:])})' for c in Constraints])
            
            self.counterexample = And([x == magic(i) for i, x in enumerate(self.VarTable.values()) if x.sort() == IntSort() ])

        def check(self,funcDefStr):
            self.solver.push()
            smt2_string = f'{funcDefStr}\n{self.spec_smt2_string}'
            spec = parse_smt2_string(smt2_string, decls=dict(self.VarTable))
            spec = And(spec)
            spec = Not(spec)
            self.solver.add(spec)
            if verbose:
                print("spec:", spec)

            # print(f"Check: {funcDefStr}")

            res=self.solver.check(self.counterexample)
            # print("After ce check.")
            if res == sat:
                model=self.solver.model()
                self.solver.pop()
                return model

            res=self.solver.check()
            # print("After check.")
            if res==unsat:
                self.solver.pop()
                return None
            else:
                model=self.solver.model()
                self.solver.pop()
                return model
    
    checker=Checker(VarTable, synFunction, Constraints)
    return checker
