from enum import Enum
from typing import List,Callable

class TwoVal(Enum):
    Zero = 0 
    One = 1
    
    def And(args : List):
        return TwoVal.frombool(all([var == TwoVal.One for var in args]))
    
    def Or(args : List):
        return TwoVal.frombool(any([var == TwoVal.One for var in args]))

    def Not(var):
        if var == TwoVal.One:
            return TwoVal.Zero
        if var == TwoVal.Zero:
            return TwoVal.One
        
    def frombool(bool):
        if bool == False:
            return TwoVal.Zero
        if bool == True:
            return TwoVal.One
    
    def __repr__(self):
        if self == TwoVal.Zero:
            return "0"
        if self == TwoVal.One:
            return "1"
        
class ThreeVal(Enum):
    Zero = 0
    One = 1
    Half = 2

    def And(args : List):
        if all([var == ThreeVal.One for var in args]):
            return ThreeVal.One
        if any([var == ThreeVal.Zero for var in args]):
            return ThreeVal.Zero
        else:
            return ThreeVal.Half

    def Or(args : List):
        if all([var == ThreeVal.Zero for var in args]):
            return ThreeVal.Zero
        if any([var == ThreeVal.One for var in args]):
            return ThreeVal.One
        else:
            return ThreeVal.Half
        
    def Not(var):
        if var == ThreeVal.One:
            return ThreeVal.Zero
        if var == ThreeVal.Zero:
            return ThreeVal.One
        if var == ThreeVal.Half:
            return ThreeVal.Half

    def meet(args: List):
        #Meet in the information order
        if all([var == ThreeVal.Zero for var in args]):
            return ThreeVal.Zero
        if all([var == ThreeVal.One for var in args]):
            return ThreeVal.One
        else:
            return ThreeVal.Half
        
    def __repr__(self):
        if self == ThreeVal.Zero:
            return "0"
        if self == ThreeVal.One:
            return "1"
        if self == ThreeVal.Half:
            return "1/2"

    def frombool(bool):
        if bool == 0:
            return ThreeVal.Zero
        if bool == 1:
            return ThreeVal.One
 
class LogicalExpression:
    def __init__(self):
        pass

    def handle(self,logic):
        pass

    def substitute(self,input):
        pass

class And(LogicalExpression):
    def __init__(self, *args:LogicalExpression):
        self.args = list(args)

    def handle(self,logic):
        results =  [ arg.handle(logic) for arg in self.args ]
        return logic.And(results)

    def substitute(self, input):
        subs = [ arg.substitue(input) for arg in self.args ] 
        return And(*subs)
        
    def __repr__(self):
        return "And("+ str(self.args)+ ")"
    
class Or(LogicalExpression):
    def __init__(self, *args:LogicalExpression):
        self.args = list(args)

    def handle(self,logic):
        results =  [ arg.handle(logic) for arg in self.args ]
        return logic.Or(results)
    
    def __repr__(self):
        return "Or("+ str(self.args)+ ")"

class Not(LogicalExpression):
    def __init__(self,body:LogicalExpression):
        self.body = body

    def handle(self,logic):
        body_result =  self.body.handle(logic)
        return logic.Not(body_result)

class ForAll(LogicalExpression):
    def __init__(self,domain,body:LogicalExpression):
        self.domain = domain
        self.body = body

    def handle(self,logic):
        results = [self.body.substitute(var).handle(logic) for var in self.domain] 
        return logic.And(results)

class Exists(LogicalExpression):
    def __init__(self,domain,body:LogicalExpression):
        self.domain = domain
        self.body = body

    def handle(self,logic):
        subs = [self.body.substitute(var) for var in self.domain]
        results = [formula.handle(logic) for formula in subs]
        return logic.Or(results)
    
class Atom(LogicalExpression):
    #No free variables
    def __init__(self,logicvar):
        self.logicvar = logicvar

    def handle(self,logic):
        return self.logicvar 

    def __repr__(self):
        return "atomic"+self.logicvar.__repr__()

class FV(LogicalExpression):
    def __init__(self,function: Callable[...,LogicalExpression]):
        self.function = function 

    def substitute(self,*input):
        return self.function(*input)
            
def example1():
    zero = Atom(TwoVal.Zero)
    one = Atom(TwoVal.One)
    first = And(one,zero)
    second = Or(first,one)
    print(second)
    print(second.handle(TwoVal))

def example2():
    domain = [0,1]
    query = [TwoVal.Zero,TwoVal.One]
    formula = Exists(domain,FV(lambda input: Atom(query[input])))
    print(formula.handle(TwoVal))
    
