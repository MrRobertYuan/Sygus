import sys
import sexp
import pprint
import translator
import time

def Extend(Stmts, Productions):
    ret = []
    for i in range(len(Stmts)):
        if type(Stmts[i]) == list:
            TryExtend = Extend(Stmts[i], Productions)
            if len(TryExtend) > 0 :
                for extended in TryExtend:
                    ret.append(Stmts[0:i]+[extended]+Stmts[i+1:])
        elif Stmts[i] in Productions:
            for extended in Productions[Stmts[i]]:
                ret.append(Stmts[0:i]+[extended]+Stmts[i+1:])
    return ret

def stripComments(bmFile):
    noComments = '('
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + ')'

commutative = set(['*', '+', 'and', 'or', '='])

def getReverse(TE):
    #print("Before:", str(TE))
    if(TE[0] in commutative and TE[1] != TE[2]):
        t = TE[1]
        TE[1] = TE[2]
        TE[2] = t
    elif(TE[0] == 'mod' or TE[0] == '-'):
        t = getReverse(TE[1])
        if( t != TE[1] ):
            TE[1] = t
        else:
            TE[2] = getReverse(TE[2])
    #print("After:", str(TE))
    return TE

if __name__ == '__main__':
    benchmarkFile = open(sys.argv[1])
    bm = stripComments(benchmarkFile)
    bmExpr = sexp.sexp.parseString(bm, parseAll=True).asList()[0] #Parse string to python list
    #print(bmExpr)
    checker = translator.ReadQuery(bmExpr)
    #print (checker.check('(define-fun f ((x Int)) Int (mod (* x 3) 10)  )'))
    #raw_input()
    SynFunExpr = []
    StartSym = 'My-Start-Symbol' #virtual starting symbol
    for expr in bmExpr:
        if len(expr)==0:
            continue
        elif expr[0]=='synth-fun':
            SynFunExpr=expr
    FuncDefine = ['define-fun']+SynFunExpr[1:4] #copy function signature



    #print(FuncDefine)
    BfsQueue = [[StartSym]] #Top-down
    Productions = {StartSym:[]}
    Type = {StartSym:SynFunExpr[3]} # set starting symbol's return type

    for NonTerm in SynFunExpr[4]: #SynFunExpr[4] is the production rules
        NTName = NonTerm[0]
        NTType = NonTerm[1]
        if NTType == Type[StartSym]:
            Productions[StartSym].append(NTName)
        Type[NTName] = NTType
        #Productions[NTName] = NonTerm[2]
        Productions[NTName] = []
        for NT in NonTerm[2]:
            if type(NT) == tuple:
                Productions[NTName].append(str(NT[1])) # deal with ('Int',0). You can also utilize type information, but you will suffer from these tuples.
            else:
                Productions[NTName].append(NT)
    Count = 0
    TE_set = set()

    time_start = time.time()
    while(len(BfsQueue)!=0):
        # print(f"TE_set size: {len(TE_set)}")
        # print(f"Queue size: {len(BfsQueue)}")
        Curr = BfsQueue.pop(0)
        #print("Extending "+str(Curr))
        TryExtend = Extend(Curr, Productions)
        if(len(TryExtend) == 0): # Nothing to extend
            FuncDefineStr = translator.toString(FuncDefine,ForceBracket = True) # use Force Bracket = True on function definition. MAGIC CODE. DO NOT MODIFY THE ARGUMENT ForceBracket = True.
            CurrStr = translator.toString(Curr)
            #SynFunResult = FuncDefine+Curr
            #Str = translator.toString(SynFunResult)
            Str = FuncDefineStr[:-1]+' '+ CurrStr+FuncDefineStr[-1] # insert Program just before the last bracket ')'
            Count += 1
            # print (Count)
            # print (Str)
            # if Count % 100 == 1:
                # print (Count)
                # print (Str)
                #raw_input()
            #print '1'
            check_start_time = time.time()
            counterexample = checker.check(Str, counterexample)
            check_end_time = time.time()
            print(f"Check time: {check_end_time-check_start_time}. {counterexample}")
            #print counterexample
            if(counterexample == None): # No counter-example
                Ans = Str
                break
            #print '2'
        #print(TryExtend)
        #raw_input()
        #BfsQueue+=TryExtend
        for TE in TryExtend:
            TE_str = str(TE)
            if not TE_str in TE_set:
                BfsQueue.append(TE)
                TE_set.add(TE_str)
                t = str([getReverse(TE[0])])
                TE_set.add(t)
                # TE_set.add(str([getReverse(TE[0])]))
                # print(TE_str)
                # print(t)
    time_end = time.time()
    print(Ans)
    print(time_end-time_start)

	# Examples of counter-examples    
	# print (checker.check('(define-fun max2 ((x Int) (y Int)) Int 0)'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int x)'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (+ x y))'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) y x))'))
