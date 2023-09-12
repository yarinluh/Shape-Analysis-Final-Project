from shape_parser import Command,CommandType,ECondition,EConditionType,ORCondition,ANDCondition,BoolConditionType,BOOLCondition
from copy import deepcopy
from logical_expressions import *
from typing import Set
from helper_functions import helper_functions
from state import State
from state_visualisation import *

# TODO : 
# instrumentation predicates - which ones we want and how to implement them - add them to coerce? write the compatibility constraints for them.
# fix bug in coerce - pointers - case 2
# finish 'is' instrumentation, and add the rest of the instrumentation, add compatibility constraints for 'is'
# create the signature from the program code    

class state_transformers:  
    #missing instrumentation updates for even,odd
    # BUG when updating r-x for x.n=y and x = y.n

    def evaluate_transformer_on_state(state:State,command:Command,logic):
        type = command.command_type 

        if type == CommandType.C_Skip:
            individuals = state.individuals.copy()
            predicate_values = deepcopy(state.predicate_values)
            return state.change_indvs_or_values(individuals,predicate_values)
        
        if type == CommandType.C_Assign_Var: 
            x_variable = command.command_parameters['x']           
            y_variable = command.command_parameters['y']
            individuals = state.individuals.copy()
            pre = state.predicate_values
            post = deepcopy(pre)
            for indv in individuals:
                post[x_variable][(indv)] = pre[y_variable][(indv)]
            #updates to r and c 
            rx = 'r-'+x_variable
            ry = 'r-'+y_variable
            for indv in individuals:
                post[rx][indv] = pre[ry][indv]
            return state.change_indvs_or_values(individuals,post)
        
        if type == CommandType.C_Assign_Null: 
            x_variable = command.command_parameters['x']            
            individuals = state.individuals.copy()
            post = deepcopy(state.pre)
            for indv in individuals:
                post[x_variable][(indv)] = logic.Zero
            #updates to r and c
            rx = 'r-'+x_variable
            ry = 'r-'+y_variable
            for indv in individuals:
                post[rx][indv] = logic.Zero
            return state.change_indvs_or_values(individuals,post)
        
        if type == CommandType.C_Assign_To_Next:
            individuals = state.individuals.copy()
            x_variable = command.command_parameters['x']           
            y_variable = command.command_parameters['y']
            pre = state.predicate_values
            post = deepcopy(pre)

            for indv in individuals:
                rhs_condition = Exists(individuals,FV(lambda indv1: And(Atom(pre[y_variable][(indv1)]),Atom(pre['n'][(indv1,indv)]))))
                post[x_variable][(indv)] = rhs_condition.handle(logic)
            #updates to r and c
            rx = 'r-'+x_variable
            ry = 'r-'+y_variable
            for indv in individuals:
                post[rx][indv] = logic.And([pre[ry][indv],logic.Or([pre['c'][indv],logic.Not(pre[y_variable][indv])])])
            return state.change_indvs_or_values(individuals,post)

        if type == CommandType.C_Set_Next_To_Var:
            #Assuming the previous command was set_next_to_null as in the paper/instructions
            individuals = state.individuals.copy()
            x_variable = command.command_parameters['x']           
            y_variable = command.command_parameters['y']
            pointers = state.pointers            
            pre = state.predicate_values
            post = deepcopy(pre)
            for indv1 in individuals:
                for indv2 in individuals:
                    rhs_condition = Or(Atom(pre['n'][(indv1,indv2)]),And(Atom(pre[x_variable][(indv1)]),Atom(pre[y_variable][(indv2)])))
                    post['n'][(indv1,indv2)] = rhs_condition.handle(logic)

            #is updates
            is_update_condition = FV(lambda v: Exists(individuals,FV(lambda u: And(Atom(pre[y_variable][v]),Atom(pre['n'][(u,v)])))))
            is_update_formula = FV(lambda v: Exists(individuals,FV(lambda v1: Exists(individuals,FV(lambda v2: And(Atom(logic.frombool(v1!=v2)),Atom(post['n'][(v1,v)]),Atom(post['n'][(v2,v)]) ))))))

            for indv in individuals:
                subs = is_update_condition.substitute(indv)
                res = subs.handle(logic)
                if res != logic.Zero:
                    subs = is_update_formula.substitute(indv)
                    res = subs.handle(logic)
                    post['is'][indv] = logic.Or([pre['is'][indv],res])
            
            #updates to r and c
            rx = 'r-'+x_variable
            ry = 'r-'+y_variable
            
            for pointer in pointers:
                rz = 'r-'+pointer
                for indv in individuals:
                    part1 = pre[rz][indv]
                    part2 = Exists(individuals,FV(lambda u: 
                            And(Atom(pre[rz][u]),Atom(pre[x_variable][u]),Atom(pre[ry][indv]))))
                    post[rz][indv] = logic.Or([part1,part2.handle(logic)])

            for indv in individuals:
                part1 = pre['c'][indv]
                part2 = Exists(individuals,FV(lambda u: 
                        And(Atom(pre[x_variable][u]),Atom(pre[ry][u]),Atom(pre[ry][indv]))))
                post[rz][indv] = logic.Or([part1,part2.handle(logic)])

            return state.change_indvs_or_values(individuals,post)
            

        if type == CommandType.C_Set_Next_To_Null: 
            individuals = state.individuals.copy()
            x_variable = command.command_parameters['x']
            pointers = state.pointers           
            pre = state.predicate_values
            post = deepcopy(pre)
            for indv1 in individuals:
                for indv2 in individuals:
                    rhs_condition = And(Atom(pre['n'][(indv1,indv2)]),Not(Atom(pre[x_variable][(indv1)])))
                    post['n'][(indv1,indv2)] = rhs_condition.handle(logic)

            #is update
            is_update_condition = FV(lambda v: Exists(individuals,FV(lambda u: And(Atom(pre[x_variable][u]),Atom(pre['n'][(u,v)])))))
            is_update_formula = FV(lambda v: Exists(individuals,FV(lambda v1: Exists(individuals,FV(lambda v2: And(Atom(logic.frombool(v1!=v2)),Atom(post['n'][(v1,v)]),Atom(post['n'][(v2,v)]) ))))))

            for indv in individuals:
                subs = is_update_condition.substitute(indv)
                res = subs.handle(logic)
                if res != logic.Zero:
                    subs = is_update_formula.substitute(indv)
                    res = subs.handle(logic)
                    post['is'][indv] = logic.And([pre['is'][indv],res])
            
            #updates to r and c
            rx = 'r-'+x_variable
            exact_formula = FV(lambda v: Or(
            Atom(post[x_variable][v]),
            Exists(individuals,FV(lambda v1: Reach(individuals,v1,v)))))
            
            for pointer in pointers:
                rz = 'r-'+pointer
                if pointer == x_variable:
                    for indv in individuals:
                        post[rx][indv] = post[x_variable][indv]
                else:
                    for indv in individuals:
                        condition = logic.And([pre['c'][indv],pre[rx][indv]])
                        if condition != logic.Zero:
                            subs = exact_formula.substitute(indv)
                            result = subs.handle(logic)
                        else:
                            part1 = pre[rz][indv]
                            part2 = Not(Exists(individuals, FV(lambda u:
                                       And(Atom(pre[rz][u]),Atom(pre[x_variable][u]),Atom(pre[rx][indv]),Not(Atom(pre[x_variable][indv]))))))
                            result = logic.And([part1,part2.handle(logic)])
                            post[rz][indv] = result

            for indv in individuals:
                part2 = Not(Exists(individuals,FV(lambda u:
                            And(Atom(pre[x_variable][u]),Atom(pre['c'][u]),Atom(pre[rx][indv])))))
                post['c'][indv] = logic.And([pre['c'][indv],part2.handle(logic)])

            return state.change_indvs_or_values(individuals,post)

        if type == CommandType.C_New:
            #Temporary - don't know how/if to implement the IsNew'
            pointers = state.pointers
            new_individuals = state.individuals.copy()
            new_individual = 'u'+str(len(new_individuals))
            new_individuals.add(new_individual) 
            x_variable = command.command_parameters['x']           
            pre = state.predicate_values
            post = deepcopy(pre)
            
            post[x_variable][new_individual] = logic.frombool(True)
            for pointer in state.pointers:
                if pointer != x_variable:
                    post[pointer][new_individual] = logic.frombool(False)

            for indv1 in new_individuals:
                for indv2 in new_individuals:
                    if indv1 == new_individual or indv2 == new_individual:
                        post['n'][(indv1,indv2)] = logic.frombool(False)

            for indv in new_individuals:
                if indv == new_individual:
                    post['sm'][indv] = logic.frombool(False)
                    post['is'][indv] = logic.frombool(False)
                    post['c'][indv] = logic.frombool(False)
                    for pointer in pointers:
                        rz = 'r-'+pointer
                        if pointer == x_variable:
                            post[rz][indv] = logic.frombool(True)
                        else:
                            post[rz][indv] = logic.frombool(False)
             
            return state.change_indvs_or_values(new_individuals,post)

        #The following two commands shouldn't reach this as they have different treatment:
        if type == CommandType.C_Assume:
            pass

        if type == CommandType.C_Assert:
            pass

    def evaluate_boolean_condition_on_state(state: State,cond: ECondition,logic):
        #We return true if the boolean evaluates to 1 or 1/2 

        if cond.econdition_type == EConditionType.E_True:
            return True
        
        if cond.econdition_type == EConditionType.E_False:
            return False
        
        if cond.econdition_type == EConditionType.E_Equal_Var:
            i_variable = cond.econdition_parameters['i']
            j_variable = cond.econdition_parameters['j']
            domain = state.individuals
            pre = state.predicate_values
            check_condition = ForAll(domain,FV(
                lambda input: And(Or(Atom(pre[i_variable][(input)]),Not(Atom(pre[j_variable][(input)]))),
                                  Or(Atom(pre[j_variable][(input)]),Not(Atom(pre[i_variable][(input)]))))
            ))
            result = check_condition.handle(logic)
            if result == logic.One:
                return True
            if result == logic.Zero:
                return False
            else:
                return True

        if cond.econdition_type == EConditionType.E_Diff_Var:
            i_variable = cond.econdition_parameters['i']
            j_variable = cond.econdition_parameters['j']
            domain = state.individuals
            pre = state.predicate_values
            check_condition = Exists(domain,FV(
                lambda input: Not(And(Or(Atom(pre[i_variable][(input)]),Not(Atom(pre[j_variable][(input)]))),
                                  Or(Atom(pre[j_variable][(input)]),Not(Atom(pre[i_variable][(input)])))))
            ))
            result = check_condition.handle(logic)
            if result == logic.One:
                return True
            if result == logic.Zero:
                return False
            else:
                return True
        
        if cond.econdition_type == EConditionType.E_Equal_Null:
            i_variable = cond.econdition_parameters['i']
            domain = state.individuals
            pre = state.predicate_values
            check_condition = ForAll(domain,FV(
                lambda input : Not(Atom(pre[i_variable][(input)]))
            ))
            result = check_condition.handle(logic)
            if result == logic.One:
                return True
            if result == logic.Zero:
                return False
            else:
                return True

        if cond.econdition_type == EConditionType.E_Diff_Null:
            i_variable = cond.econdition_parameters['i']
            domain = state.individuals
            pre = state.predicate_values
            check_condition = Exists(domain,FV(
                lambda input : Atom(pre[i_variable][(input)])
            ))
            result = check_condition.handle(logic)
            if result == logic.One:
                return True
            if result == logic.Zero:
                return False
            else:
                return True

    def evaluate_assert_on_state(state, ORC: ORCondition ,logic):
        #We return False for a result of 0 or 1/2
        disjunction_list = ORC.disjunction_list
        disjunction_results = []
        for disjunct in disjunction_list:
            conjunction_list = disjunct.conjunction_list
            conjunction_results = []
            for boolcondition in conjunction_list:
                result = state_transformers.evaluate_boolcondition_on_state(state,boolcondition,logic)
                conjunction_results.append(result)
            and_result = logic.And(conjunction_results)
            disjunction_results.append(and_result)
        or_result = logic.Or(disjunction_results)
        if or_result == logic.Zero:
            return False
        if or_result == logic.One:
            return True
        else:
            return False
        
    def evaluate_boolcondition_on_state(state: State,cond: BOOLCondition,logic):
        """All untested - but relatively simple"""
        type = cond.boolcondition_type

        if type == BoolConditionType.B_NULL_POINTER:
            x_variable = cond.boolcondition_parameters['x']
            domain = state.individuals
            pre = state.predicate_values
            check_condition = ForAll(domain,FV(
                lambda input : Not(Atom(pre[x_variable][(input)]))
            ))
            result = check_condition.handle(logic)
            return result

        if type == BoolConditionType.B_NOT_NULL_POINTER:
            x_variable = cond.boolcondition_parameters['x']
            domain = state.individuals
            pre = state.predicate_values
            check_condition = Exists(domain,FV(
                lambda input : Atom(pre[x_variable][(input)])
            ))
            result = check_condition.handle(logic)
            return result

        if type == BoolConditionType.B_VARIABLE_POINTER:
            x_variable = cond.boolcondition_parameters['x']
            y_variable = cond.boolcondition_parameters['y']
            domain = state.individuals
            pre = state.predicate_values
            check_condition = ForAll(domain,FV(
                lambda input: And(Or(Atom(pre[x_variable][(input)]),Not(Atom(pre[y_variable][(input)]))),
                                  Or(Atom(pre[y_variable][(input)]),Not(Atom(pre[x_variable][(input)]))))
            ))
            result = check_condition.handle(logic)
            return result
            
        if type == BoolConditionType.B_NOT_VARIABLE_POINTER:
            x_variable = cond.boolcondition_parameters['x']
            y_variable = cond.boolcondition_parameters['y']
            domain = state.individuals
            pre = state.predicate_values
            check_condition = Exists(domain,FV(
                lambda input: Not(And(Or(Atom(pre[x_variable][(input)]),Not(Atom(pre[y_variable][(input)]))),
                                  Or(Atom(pre[y_variable][(input)]),Not(Atom(pre[x_variable][(input)])))))
            ))
            result = check_condition.handle(logic)
            return result

        if type == BoolConditionType.B_NEXT_POINTER:
            x_variable = cond.boolcondition_parameters['x']
            y_variable = cond.boolcondition_parameters['y']
            domain = state.individuals
            pre = state.predicate_values
            check_condition = Exists(domain,FV(
                   lambda v1: Exists(domain,FV(
                   lambda v2: And(Atom(pre[y_variable][(v1)]),
                                  Atom(pre['n'][(v1,v2)]),
                                  Atom(pre[x_variable][(v2)]))))))
            result = check_condition.handle(logic)
            return result
        
        if type == BoolConditionType.B_NOT_NEXT_POINTER:
            x_variable = cond.boolcondition_parameters['x']
            y_variable = cond.boolcondition_parameters['y']
            domain = state.individuals
            pre = state.predicate_values
            check_condition = Not(Exists(domain,FV(
                   lambda v1: Exists(domain,FV(
                   lambda v2: And(Atom(pre[y_variable][(v1)]),
                                  Atom(pre['n'][(v1,v2)]),
                                  Atom(pre[x_variable][(v2)])))))))
            result = check_condition.handle(logic)
            return result

        """YET TO BE IMPLEMENTED - NEEDS INSTRUMENTATION"""
        if type == BoolConditionType.B_LIST:
            pass

        if type == BoolConditionType.B_NOT_LIST:
            pass

        if type == BoolConditionType.B_ODD_LIST:
            pass

        if type == BoolConditionType.B_EVEN_LIST:
            pass

class set_transformers:

    def abstract_transformer(set_of_states: Set[State], command: Command, logic):
        #focus -> coerce -> [st]_3 -> coerce -> t_embed
        print("\nstart","size: ",len(set_of_states),set_of_states)
        focus_result = set_transformers.focus_set(set_of_states,command)
        print("\nforcus result","size: ",len(focus_result),focus_result)
        #coerce1_result = set_transformers.coerce_set(focus_result) #MAYBE ADD ANOTHER COERCE IN THE MIDDLE LIKE THEY SUGGESTED
        #print("\ncoerce1 result","size: ",len(coerce1_result),coerce1_result)
        transformer_result = set_transformers.evaluate_transformer_on_set(focus_result,command,ThreeVal)
        #draw_set_of_states(transformer_result)
        print("\ntransformer result","size: ",len(transformer_result),transformer_result)
        coerce2_result = set_transformers.coerce_set(transformer_result)
        print("\ncoerce2 result","size: ",len(coerce2_result),coerce2_result)
        embed_result = set_transformers.cannonical_embed_set(coerce2_result)
        return embed_result

    def focus_set(set_of_states : Set[State], command: Command):
        outset = set()
        focus_formulae = command.focus_formulae
        #print(focus_formulae)
        for state in set_of_states:
            new_states = helper_functions.focus(state,focus_formulae)
            outset.update(new_states)
        return outset

    def coerce_set(set_of_states :Set[State]):
        outset = set()
        for state in set_of_states:
            constraints = helper_functions.create_constraints(state.pointers)
            #print(constraints)
            coerce_result = helper_functions.coerce(state,constraints)
            if coerce_result != None:
                outset.add(coerce_result)
        return outset

    def cannonical_embed_set(set_of_states: Set[State]):
        outset = set()
        for state in set_of_states:
            print(state.pointers)
            embed_result = helper_functions.cannonical_embedding(state,state.pointers)
            outset.add(embed_result)
        return outset

    def evaluate_transformer_on_set(set_of_states: Set[State],command: Command, logic):
        simple_commands = {CommandType.C_Skip,CommandType.C_Assign_Var,CommandType.C_Assign_Null,CommandType.C_Assign_To_Next,CommandType.C_Set_Next_To_Var,CommandType.C_Set_Next_To_Null,CommandType.C_New}
        if command.command_type in simple_commands:
            return {state_transformers.evaluate_transformer_on_state(state,command,logic) for state in set_of_states}

        if command.command_type == CommandType.C_Assume:
            return {state for state in set_of_states if state_transformers.evaluate_boolean_condition_on_state(state,command.command_parameters['E'],ThreeVal)}

        if command.command_type == CommandType.C_Assert:
            outset = set()
            for state in set_of_states:
                assert_orc = command.command_parameters['ORC']
                assert_result = state_transformers.evaluate_assert_on_state(state,assert_orc,ThreeVal)
                if assert_result == False:
                    print("assert: ",assert_orc,"may be violated by state: ",state)
                else:
                    outset.add(state)
            return outset
    
def econditions_example():
    pointers = {'x','y'}
    individuals = {'u1','u'}
    predicate_values = {'x':{('u1'): ThreeVal.Half,('u'):ThreeVal.Zero},'y':{('u1'):ThreeVal.One,('u'):ThreeVal.Zero},'sm':{('u1'): ThreeVal.Zero,('u'): ThreeVal.Half}, 
    'n': {('u1','u1'):ThreeVal.Zero, ('u1','u'):ThreeVal.Half, ('u','u1'):ThreeVal.Zero, ('u','u'):ThreeVal.Half}}
    s = State(pointers,{},individuals,predicate_values,ThreeVal)
    print(state_transformers.evaluate_boolean_condition_on_state(s,ECondition(['x','=','y']),ThreeVal))
    print(state_transformers.evaluate_boolean_condition_on_state(s,ECondition(['x','!=','y']),ThreeVal))
    print(state_transformers.evaluate_boolean_condition_on_state(s,ECondition(['x','=','NULL']),ThreeVal))
    print(state_transformers.evaluate_boolean_condition_on_state(s,ECondition(['x','!=','NULL']),ThreeVal))

def abstract_transformer_example_61():
    #start of the table from page 61 - table XV
    one = ThreeVal.One
    zero = ThreeVal.Zero
    half = ThreeVal.Half

    pointers = {'x','y'}
    individuals = {'u0','u1'}
    predicate_values = {
        'x':{'u0':one,'u1':zero},
        'y':{'u0':one,'u1':zero},
        'n':{('u0','u0'):zero,('u0','u1'):half,('u1','u0'):zero,('u1','u1'):half},
        'sm':{'u0':zero,'u1':half}
    }
    s = State(pointers,{},individuals,predicate_values,ThreeVal)
    set_of_states = {s}
    command = Command('y := y.n')
    print(set_transformers.abstract_transformer(set_of_states,command,ThreeVal))

def abstract_transformer_example():
    #figure 15 - full table
    one = ThreeVal.One
    zero = ThreeVal.Zero
    half = ThreeVal.Half

    pointers = {'x','y'}
    individuals = {'u0','u1'}
    predicate_values = {
        'x':{'u0':one,'u1':zero},
        'y':{'u0':one,'u1':zero},
        'n':{('u0','u0'):zero,('u0','u1'):half,('u1','u0'):zero,('u1','u1'):half},
        'sm':{'u0':zero,'u1':half}
    }
    s = State(pointers,{},individuals,predicate_values,ThreeVal)
    set_of_states = {s}
    command = Command('y := y.n')
    results=set_transformers.abstract_transformer(set_of_states,command,ThreeVal)
    print(results)

def is_instrumentation_example():
    one = ThreeVal.One
    zero = ThreeVal.Zero
    half = ThreeVal.Half

    
    pointers = {'x','y'}
    individuals = {'u0','u1','u2'}
    predicate_values = {
        'y' :{'u0':zero,'u1':zero,'u2':one},
        'x' :{'u0':one,'u1':zero,'u2':zero},
        'sm' : {'u0':zero,'u1':zero,'u2':zero},
        'is' : {'u0':zero,'u1':zero,'u2':one},
        'n' :{  ('u0','u0'):zero,('u0','u1'):zero,('u0','u2'):one,
                ('u1','u0'):zero,('u1','u1'):zero,('u1','u2'):one,
                ('u2','u0'):zero,('u2','u1'):zero,('u2','u2'):zero, }
    }   
    instrumentation = {'sm','is'}
    state = State(pointers,instrumentation,individuals,predicate_values)

    draw_state_graph(state,'state 0')
    state1 = state_transformers.evaluate_transformer_on_state(state,Command('x.n := NULL'),ThreeVal)
    draw_state_graph(state1,'state 1')

    state2 = state_transformers.evaluate_transformer_on_state(state1,Command('x.n := y'),ThreeVal)
    draw_state_graph(state2,'state 2')
