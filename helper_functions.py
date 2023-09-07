from shape_parser import Program,Command,CommandType
from copy import deepcopy
from logical_expressions import *
from transformers import State
from typing import Set,Optional
from algorithm import State


class Constraint:
    def __init__(self):
        pass

    def check(self):
        pass
                
class Type1Constraint(Constraint):
    def __init__(self,name, arity: int, lhs: FV):
        self.name = name
        self.arity = arity
        self.type = 1
        self.lhs = lhs

    def check(self,state,assignment):
        predicate_values = state.predicate_values
        sub = self.lhs.substitute(predicate_values,assignment,state.individuals)
        lhs_result = sub.handle(ThreeVal)
        if lhs_result == ThreeVal.One:
            return False
        return True
    
    def __repr__(self):
        return self.name

class Type2Constraint(Constraint):
    def __init__(self, name, arity: int, lhs: FV, b: bool):
        self.name = name
        self.arity = arity
        self.type = 2
        self.lhs = lhs
        self.b = b

    def check(self,state,assignment):
        #This should somehow relate to summary node
        predicate_values = state.predicate_values
        sub = self.lhs.substitute(predicate_values,assignment,state.individuals) 
        lhs_result = sub.handle(ThreeVal)
        if lhs_result == ThreeVal.One:
            if self.b == 1:
                if assignment[0]!=assignment[1]:
                    return False
                if predicate_values['sm'][assignment[0]] == ThreeVal.Half:
                    return False
                else:
                    return True
            if self.b == 0:
                if assignment[0]==assignment[1]:
                    return False
                if predicate_values['sm'][assignment[0]] == ThreeVal.Half:
                    return False
                else:
                    return True
        return True
    
    def __repr__(self):
        return self.name
  
class Type3Constraint(Constraint):
    def __init__(self,name, arity: int, lhs: FV, predicate: str, pred_arity:int, b: bool):
        self.arity = arity
        self.name = name
        self.lhs = lhs
        self.predicate = predicate
        self.pred_arity = pred_arity
        self.b = b
        self.type = 3

    def check(self,state,assignment):
        predicate_values = state.predicate_values
        sub = self.lhs.substitute(predicate_values,assignment,state.individuals) 
        lhs_result = sub.handle(ThreeVal)

        if lhs_result == ThreeVal.One:
            if self.pred_arity == 1:
                predicate_inputs = (assignment[0])
            else:
                predicate_inputs = tuple(assignment[:self.pred_arity])
            predicate_value = predicate_values[self.predicate][predicate_inputs]
            if not(self.b):
                predicate_value = ThreeVal.Not(predicate_value)
            if predicate_value == ThreeVal.One:
                return True
            return False
    
    def __repr__(self):
        return self.name

def cartesian_product(lst, k):
    #Thanks chatGPT
    if k == 0:
        return [[]]
    if k == 1:
        return [(x,) for x in lst]
    result = []
    smaller_product = cartesian_product(lst, k - 1)
    for item in lst:
        for product in smaller_product:
            result.append((item,) + product)
    return result

class helper_functions: 
    def cannonical_embedding(state:State,predicates: list[str]):
        #Definition 4.13 from the paper

        individuals = state.individuals
        pre = state.predicate_values
        cannonical_nodes = set()
        emp_state = state.empty()
        post = emp_state.predicate_values
        mapping = {} #dictionary mapping individuals to cannonical nodes
        
        for indv in individuals:
            one_set = ""
            zero_set = ""
            for pred in predicates:
                if pre[pred][indv] == ThreeVal.One:
                    one_set = one_set + pred
                if pre[pred][indv] == ThreeVal.Zero:
                    zero_set = zero_set + pred
            new_node = "("+one_set+","+zero_set+")"
            cannonical_nodes.add(new_node)
            mapping[indv] = new_node

        for pointer in state.pointers:
            for cannonical_node in cannonical_nodes:
                or_results = []
                for indv in individuals:
                    if mapping[indv] == cannonical_node:
                        or_results.append(pre[pointer][indv])
                result = ThreeVal.meet(or_results)
                post[pointer][cannonical_node] = result
        
        for cannonical_node in cannonical_nodes:
            preimage = []
            for indv in individuals:
                if mapping[indv] == cannonical_node:
                    preimage.append(indv)
            if len(preimage) > 1 or pre['sm'][preimage[0]] == ThreeVal.Half:
                result = ThreeVal.Half
            else:
                result = ThreeVal.Zero
            post['sm'][cannonical_node] = result

        for can_node_1 in cannonical_nodes:
            for can_node_2 in cannonical_nodes:
                meet_results = []
                for indv1 in individuals:
                    for indv2 in individuals:
                        #print(can_node_1,can_node_2,indv1,indv2)
                        if mapping[indv1] == can_node_1 and mapping[indv2] == can_node_2:
                            meet_results.append(pre['n'][(indv1,indv2)])
                            #print(pre['n'][(indv1,indv2)])
                #print(meet_results)
                result = ThreeVal.meet(meet_results)
                post['n'][(can_node_1,can_node_2)] = result

        cannonical_state = state.change_indvs_or_values(cannonical_nodes,post)
        return cannonical_state
        #ADD INSTRUMENTATION

    def focus(state: State,formulae: Set) -> Set:
        focus_pointers = {formula for formula in formulae if type(formula) == str}
        focus_deref = {formula[1] for formula in formulae if type(formula) == tuple and formula[0] == 'n'}
        workset = {state}
        for pointer in focus_pointers:
            result_set = set()
            for workstate in workset:
                new_states = helper_functions.focus_var(workstate,pointer)
                result_set.update(new_states)
            workset = result_set
        for pointer in focus_deref:
            result_set = set()
            for workstate in workset:
                new_states = helper_functions.focus_var_deref(workstate,pointer)
                result_set.update(new_states)
            workset = result_set
        return workset

    def focus_var(state: State,pointer):
        assert state.logic == ThreeVal
        workset = {state}
        answerset = set()
        while workset:
            s = workset.pop()
            individuals = s.individuals
            pre = s.predicate_values
            flag = False
            for u in individuals:
                if pre[pointer][u] == ThreeVal.Half:
                    post0 = deepcopy(pre)
                    post0[pointer][u] = ThreeVal.Zero
                    s0 = s.change_indvs_or_values(individuals,post0)
                    workset.add(s0)
                    post1 = deepcopy(pre)
                    post1[pointer][u] = ThreeVal.One
                    s1 = s.change_indvs_or_values(individuals,post1)
                    workset.add(s1)
                    if pre['sm'][u] == ThreeVal.Half:
                        u0 = u+".0"
                        u1 = u+".1"
                        assert(not(u0 in individuals))
                        assert(not(u1 in individuals))
                        s_exp = helper_functions.expand(s,u,u0,u1)
                        s_exp_pre = s_exp.predicate_values
                        s_exp_post = deepcopy(s_exp_pre)
                        s_exp_post[pointer][u0] = ThreeVal.Zero
                        s_exp_post[pointer][u1] = ThreeVal.One
                        s2 = s_exp.change_indvs_or_values(s_exp.individuals,s_exp_post)
                        workset.add(s2)
                    flag = True
                    break
            if flag == False:
                answerset.add(s)
        return answerset           

    def focus_var_deref(state,pointer,sel = 'n'):
        print(type(state))
        assert state.logic == ThreeVal
        workset = helper_functions.focus_var(state,pointer)
        answerset = set()
        while workset:
            s = workset.pop()
            individuals = s.individuals
            pre = s.predicate_values
            flag = False
            for u in individuals:
                for v in individuals:
                    if pre[pointer][(v)] == ThreeVal.One and pre[sel][(v,u)] == ThreeVal.Half:
                        post0 = deepcopy(pre)
                        post0[sel][(v,u)] = ThreeVal.Zero
                        s0 = s.change_indvs_or_values(individuals,post0)
                        workset.add(s0)
                        post1 = deepcopy(pre)
                        post1[sel][(v,u)] = ThreeVal.One
                        s1 = s.change_indvs_or_values(individuals,post1)
                        workset.add(s1)
                        if pre['sm'][u] == ThreeVal.Half:
                            u0 = u+".0"
                            u1 = u+".1"
                            assert(not(u0 in individuals))
                            assert(not(u1 in individuals))
                            s_exp = helper_functions.expand(s,u,u0,u1)
                            s_exp_pre = s_exp.predicate_values
                            s_exp_post = deepcopy(s_exp_pre)
                            s_exp_post[sel][(v,u0)] = ThreeVal.Zero
                            s_exp_post[sel][(v,u1)] = ThreeVal.One
                            s2 = s_exp.change_indvs_or_values(s_exp.individuals,s_exp_post)
                            workset.add(s2)
                        flag = True
                        break
            if flag == False:
                answerset.add(s)
        return answerset           
    
    def expand(state : State,u,u0,u1):
        individuals = state.individuals
        pre = state.predicate_values
        new_individuals = individuals.copy()
        new_individuals.remove(u)
        new_individuals.add(u0)
        new_individuals.add(u1)
        empty_state = state.empty()
        post = empty_state.predicate_values
        """updates to post need to be done in a clever way - this is not going to be full, currently missing instrumentation - and this should be more modular, the same problem appears in malloc"""
        m = lambda w: u if w == u0 or w == u1 else w
        for pointer in state.pointers:
            for indv in new_individuals:
                post[pointer][(indv)] = pre[pointer][(m(indv))]
                post[pointer][(indv)] = pre[pointer][(m(indv))]
        for indv1 in new_individuals:
            for indv2 in new_individuals:
                post['n'][(indv1,indv2)] = pre['n'][(m(indv1),m(indv2))]    
        for indv in new_individuals:
            post['sm'][(indv)] = pre['sm'][(m(indv))]

        return state.change_indvs_or_values(new_individuals,post)

    def coerce(state :State ,constraints: Set[Constraint]) -> Optional[State] :
        #Maybe pass on this or only do a partial implementation
        workstate = state
        individuals = state.individuals
        """UNTESTED"""
        while(constraints):
            const = constraints.pop()
            const_arity = const.arity
            possible_assignments = cartesian_product(individuals,const_arity)
            for assignment in possible_assignments:
                pre = workstate.predicate_values
                if const.check(workstate,assignment) == False:
                    #print("\nfailed constraint: ",const,"on state: ",workstate,"\nand assignment: ",assignment)
                    if const.type == 1:
                        return None
                    if const.type == 2:
                        if const.b == 1 and (assignment[0] == assignment[1]) and (pre['sm'][assignment[0]] == ThreeVal.Half):
                            post = deepcopy(pre)
                            post['sm'][assignment[0]] = ThreeVal.Zero
                            new_state = workstate.change_indvs_or_values(workstate.individuals,post)
                            workstate = new_state
                        else: 
                            return None
                    if const.type == 3:
                        predic = const.predicate
                        if const.pred_arity == 1:
                            predicate_inputs = (assignment[0])
                        else:
                            predicate_inputs = tuple(assignment[:const.pred_arity])
                        predicate_value = pre[predic][predicate_inputs]
                        if predicate_value == ThreeVal.Half:
                            post = deepcopy(pre)
                            post[predic][predicate_inputs] = const.b
                            new_state = workstate.change_indvs_or_values(workstate.individuals,post)
                            workstate = new_state
                        else: 
                            return None
                    #print("\ncoerced state:")
                    #print(workstate)
        return workstate

class examples:
    def focus_example():
        pointers = {'x'}
        individuals = {'u0','u1'}
        predicate_values = {'x':{('u0'): ThreeVal.Half,('u1'): ThreeVal.Zero},'sm':{('u0'): ThreeVal.Half,('u1'): ThreeVal.Half}, 
        'n': {('u0','u0'): ThreeVal.Zero, ('u0','u1') : ThreeVal.Half, ('u1','u0'):ThreeVal.Zero, ('u1','u1'):ThreeVal.Half}}
        s = State(pointers,{},individuals,predicate_values,ThreeVal)
        print(helper_functions.focus_var(s,'x'))
        
    def focus_deref_example():
        #figure 15 from the paper
        pointers = {'x','y'}
        individuals = {'u1','u'}
        predicate_values = {'x':{('u1'): ThreeVal.One,('u'):ThreeVal.Zero},'y':{('u1'):ThreeVal.One,('u'):ThreeVal.Zero},'sm':{('u1'): ThreeVal.Zero,('u'): ThreeVal.Half}, 
        'n': {('u1','u1'):ThreeVal.Zero, ('u1','u'):ThreeVal.Half, ('u','u1'):ThreeVal.Zero, ('u','u'):ThreeVal.Half}}
        s = State(pointers,{},individuals,predicate_values,ThreeVal)
        print(helper_functions.focus_var_deref(s,'x'))

    def constraint_example():
        pointers = {'x','y'}
        individuals = {'u1','u'}
        predicate_values = {'x':{('u1'): ThreeVal.One,('u'):ThreeVal.One},'y':{('u1'):ThreeVal.One,('u'):ThreeVal.Zero},'sm':{('u1'): ThreeVal.Zero,('u'): ThreeVal.Half}, 
        'n': {('u1','u1'):ThreeVal.Zero, ('u1','u'):ThreeVal.Half, ('u','u1'):ThreeVal.Zero, ('u','u'):ThreeVal.Half}}
        s = State(pointers,{},individuals,predicate_values,ThreeVal)
        const_lhs =  FV(lambda pre,ass: And(Atom(pre['x'][ass[0]]),Atom(pre['x'][ass[1]])))
        constraint = Type1Constraint(2,const_lhs)
        print(constraint.check(s,['u','u']))
        constraint2 = Type2Constraint(2,const_lhs,1)
        print(constraint2.check(s,['u','u']))
        constraint3 = Type3Constraint(2,const_lhs,'y',1,1)
        print(constraint3.check(s,['u1','u']))

    def coerce_example():
        #last two lines in figure 15
        zero = ThreeVal.Zero
        half = ThreeVal.Half
        one = ThreeVal.One
        pointers = {'x','y'}

        #second structure - middle column
        individuals1 = {'u1','u'}
        values1 = {
            'x':{('u1'):one,('u'):zero},
            'y':{('u1'):zero,('u'):one},
            'n':{('u1','u1'):zero,('u1','u'):one,('u','u1'):zero,('u','u'):half},
            'sm':{('u1'):zero,('u'):half}
        }
        state1=State(pointers,{},individuals1,values1,ThreeVal)

        const1_lhs = FV(lambda pre,ass,domain: And(Atom(pre['y'][ass[0]]),Atom(pre['y'][ass[1]])))
        constraint1 = Type2Constraint('y points to one node - case 1',2,const1_lhs,1)
        #eq 40

        const2_lhs = FV(lambda pre,ass,domain: Exists(domain,FV(lambda v3:And(Atom(pre['n'][(v3,ass[0])]),Atom(pre['n'][(v3,ass[1])])))))
        constraint2 = Type2Constraint('n field points to one node - case 1',2,const2_lhs,1)
        #eq 41

        const3_lhs = FV(lambda pre,ass,domain: Exists(domain,FV(lambda v1:And(Atom(pre['n'][(ass[0],v1)]),Atom(ThreeVal.frombool(v1!=ass[1]))))))
        constraint3 = Type3Constraint('n field points to one node - case 2',2,const3_lhs,'n',2,0)
        #eq 48 

        coerce_result = helper_functions.coerce(state1,{constraint1,constraint2,constraint3})
        print(coerce_result)

        individuals2 = {'u1','u.1','u.0'}
        values2 = {
            'x':{('u1'):one,('u.1'):zero,('u.0'):zero},
            'y':{('u1'):zero,('u.1'):one,('u.0'):zero},
            'n':{('u1','u1'):zero,('u1','u.1'):one,('u.1','u.1'):half,('u.1','u1'):zero,('u1','u.0'):zero,('u.0','u1'):zero,('u.1','u.0'):half,('u.0','u.1'):half,('u.0','u.0'):half},
            'sm':{('u1'):zero,('u.0'):half,('u.1'):half}
        }
        state2=State(pointers,{},individuals2,values2,ThreeVal)

        coerce_result2 = helper_functions.coerce(state2,{constraint1,constraint2,constraint3})
        print(coerce_result2)
    
    def cannonical_embed_example():
        zero = ThreeVal.Zero
        half = ThreeVal.Half
        one = ThreeVal.One

        pointers = {'x','y'}
        individuals = {'u1','u2',}
        predicate_values = {'x':{'u1':one,'u2':one},'y':{'u1':one,'u2':half},
                            'n':{('u1','u2'): one,('u1','u1'): one,('u2','u2'): zero,('u2','u1'): half},
                            'sm':{'u1':zero,'u2':zero}}
        
        state = State(pointers,{},individuals,predicate_values,ThreeVal)

        abstraction_predicates = ['x'] #important that its ordered
        print(helper_functions.cannonical_embedding(state,abstraction_predicates))

    def cannonical_embed_example2():
        #example from fig 6 -> fig 9 
        zero = ThreeVal.Zero
        half = ThreeVal.Half
        one = ThreeVal.One

        pointers = {'x','y'}
        individuals = {'u1','u2','u3','u4','u5','u6'}

        pairs = cartesian_product(list(individuals),2)
        n_dict = {pair:zero for pair in pairs}
        n_dict[('u1','u2')] = one
        n_dict[('u2','u3')] = one
        n_dict[('u3','u4')] = one
        n_dict[('u4','u5')] = one
        n_dict[('u5','u6')] = one
        pred = {'x':{'u1':one,'u2':zero,'u3':zero,'u4':zero,'u5':zero,'u6':zero},
                'y':{'u1':zero,'u2':zero,'u3':zero,'u4':one,'u5':zero,'u6':zero},
                'n':n_dict,
                'sm':{'u1':zero,'u2':zero,'u3':zero,'u4':zero,'u5':zero,'u6':zero}}

        state = State(pointers,{},individuals,pred,ThreeVal)
        abstraction_predicates = ['x','y']
        print(helper_functions.cannonical_embedding(state,abstraction_predicates))    
    
    def focus_parse():
        focus_formulae = {'x',('n','y')}
        pointers = {'x','y'}
        individuals = {'u1','u'}
        predicate_values = {'x':{('u1'): ThreeVal.One,('u'):ThreeVal.Zero},'y':{('u1'):ThreeVal.One,('u'):ThreeVal.Zero},'sm':{('u1'): ThreeVal.Zero,('u'): ThreeVal.Half}, 
        'n': {('u1','u1'):ThreeVal.Zero, ('u1','u'):ThreeVal.Half, ('u','u1'):ThreeVal.Zero, ('u','u'):ThreeVal.Half}}
        s = State(pointers,{},individuals,predicate_values,ThreeVal)
        s1 = helper_functions.focus(s,focus_formulae)
        print(s1)

examples.focus_parse()

