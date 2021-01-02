import sys
import sexp
import pprint
import translator
import time
from queue import PriorityQueue

def Extend(Stmts, Productions):
    ret = []
    not_context = Stmts[0] == 'not'
    for i in range(len(Stmts)):
        if type(Stmts[i]) == list:
            TryExtend = Extend(Stmts[i], Productions)
            if len(TryExtend) > 0 :
                for extended in TryExtend:
                    ret.append(Stmts[0:i]+[extended]+Stmts[i+1:])
        elif Stmts[i] in Productions:
            for extended in Productions[Stmts[i]]:
                if type(extended) is list:
                    if extended[0] == '<' or extended[0] == '<=':
                        continue
                    if not_context and (extended[0] == 'not' or extended[0] in symmetrical):
                        continue
                elif Stmts[0] in relational and i == 2 and extended == Stmts[1]:
                    continue
                elif Stmts[0] == 'ite' and i == 3 and extended == Stmts[2]:
                    continue
                ret.append(Stmts[0:i]+[extended]+Stmts[i+1:])
        if len(ret) > 0:
            break
    return ret

def stripComments(bmFile):
    noComments = '('
    for line in bmFile:
        line = line.split(';', 1)[0]
        noComments += line
    return noComments + ')'

TE_set = set()
TE_dict = dict()
Productions = dict()
commutative = set(['*', '+', 'and', 'or', '='])

symmetrical = {
    '<': '>',
    '>': '<',
    '>=': '<=',
    '<=': '>='
}

relational = set(['=', '<', '>', '<=', '>='])
logical = set(['not', 'and', 'or'])

def add_identical(TE):
    identicals = get_identical(TE)
    # print("Identical")
    # pprint.pprint(TE)
    # pprint.pprint(identicals)
    # pprint.pprint(TE_dict)
    for te in identicals:
        te_str = str(te)
        TE_set.add(te_str)

def get_identical(TE, context=0):
    TE_str = str(TE)
    ret = []
    if context >= 2:
        return [TE]
    if(TE_str in TE_dict):
        return TE_dict[TE_str]

    if type(TE) is list:
        if len(TE) == 1:    # Variable or constant
            ret.append(get_identical(TE[0], context+1))
        elif len(TE) == 2:  # Not
            te1 = get_identical(TE[1], context+1)
            for x in te1:
                ret.append([TE[0], x])
        elif len(TE) == 3:
            te1 = get_identical(TE[1], context+1)
            te2 = get_identical(TE[2], context+1)
            for x in te1:
                for y in te2:
                    ret.append([TE[0], x, y])
                    if TE[0] in commutative:
                        if str(x) != str(y) and (str(x) in Productions or str(y) in Productions):
                            ret.append([TE[0], y, x])
                    if TE[0] in symmetrical:
                        ret.append([symmetrical[TE[0]], y, x])
        elif len(TE) == 4:  # ite
            te1 = get_identical(TE[1])
            te2 = get_identical(TE[2])
            te3 = get_identical(TE[3])
            for x in te1:
                for y in te2:
                    for z in te3:
                        ret.append([TE[0], x, y, z])

        else:
            ret = [TE]
    else:
        ret = [TE]
    TE_dict[TE_str] = ret
    return ret

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

def calcuAll(l):
    ans = 0
    for i in range(len(l)):
        if type(l[i]) == list:
            ans += calcuAll(l[i])
        else:
            ans += 1
    return ans

def calcuStart(l):
    ans = 0
    for i in range(len(l)):
        if type(l[i]) == list:
            ans += calcuAll(l[i])
        elif l[i] in Productions:
            ans += 1
    return ans

class myList:
    allCnt: 0
    startCnt: 0
    list: []

    def __init__(self, l):
        self.list = l
        self.startCnt = calcuStart(l)
        self.allCnt = calcuAll(l)

    def __lt__(self, other):
        if self.allCnt != other.allCnt:
            return self.allCnt < other.allCnt
        else:
            return self.startCnt < other.startCnt

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

    priorityQueue = PriorityQueue()
    myTE = myList([StartSym])
    priorityQueue.put(myTE)
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

    time_start = time.time()
    while(priorityQueue.empty() == False):
        # print(f"TE_set size: {len(TE_set)}")
        # print(f"Queue size: {len(BfsQueue)}")
        # Curr = BfsQueue.pop(0)
        Curr = priorityQueue.get().list
        # print("Extending "+str(Curr))
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
            counterexample = checker.check(Str)
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
                # BfsQueue.append(TE)
                myTE = myList(TE)
                priorityQueue.put(myTE)
                add_identical(TE)
                # TE_set.add(TE_str)
                # TE_set.add(str([getReverse(TE[0])]))

    time_end = time.time()
    print(Ans)
    print(time_end-time_start)

	# Examples of counter-examples    
	# print (checker.check('(define-fun max2 ((x Int) (y Int)) Int 0)'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int x)'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (+ x y))'))
    # print (checker.check('(define-fun max2 ((x Int) (y Int)) Int (ite (<= x y) y x))'))
