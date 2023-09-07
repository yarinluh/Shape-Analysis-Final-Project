from shape_parser import Command,CommandType,ECondition,EConditionType,ORCondition,ANDCondition,BoolConditionType,BOOLCondition
from copy import deepcopy
from logical_expressions import *
from typing import Set
from helper_functions import *
from algorithm import State

# TODO : implement assume and checking boolean conditions
# instrumentation predicates - which ones we want and how to implement them - add them to coerce? write the compatibility constraints for them.
# implement focus and coerce into the state transformers / set transformers.
# write the fixpoint algorithm    

    
class state_transformers:  
    #NOT YET INCLUDING UPDATES TO INSTRUMENTATION RELATIONS IF ANY, IN PARTICULAR NEW NODES DONT HAVE INSTRUMENTATION VALUES
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
            return state.change_indvs_or_values(individuals,post)

        if type == CommandType.C_Assign_Null: 
            x_variable = command.command_parameters['x']            
            individuals = state.individuals.copy()
            post = deepcopy(state.pre)
            for indv in individuals:
                post[x_variable][(indv)] = logic.Zero
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

            return state.change_indvs_or_values(individuals,post)

        if type == CommandType.C_Set_Next_To_Var:
            #Assuming the previous command was set_next_to_null as in the paper/instructions
            individuals = state.individuals.copy()
            x_variable = command.command_parameters['x']           
            y_variable = command.command_parameters['y']
            pre = state.predicate_values
            post = deepcopy(pre)
            for indv1 in individuals:
                for indv2 in individuals:
                    rhs_condition = Or(Atom(pre['n'][(indv1,indv2)]),And(Atom(pre[x_variable][(indv1)]),Atom(pre[y_variable][(indv2)])))
                    post['n'][(indv1,indv2)] = rhs_condition.handle(logic)
            return state.change_indvs_or_values(individuals,post)

        if type == CommandType.C_Set_Next_To_Null: 
            individuals = state.individuals.copy()
            x_variable = command.command_parameters['x']           
            pre = state.predicate_values
            post = deepcopy(pre)
            for indv1 in individuals:
                for indv2 in individuals:
                    rhs_condition = And(Atom(pre['n'][(indv1,indv2)]),Not(Atom(pre[x_variable][(indv1)])))
                    post['n'][(indv1,indv2)] = rhs_condition.handle(logic)
            return state.change_indvs_or_values(individuals,post)

        if type == CommandType.C_New:
            #Temporary - don't know how/if to implement the IsNew
            new_individuals = state.individuals.copy()
            new_individual = 'u'+str(len(new_individuals))
            new_individuals.append(new_individual) 
            x_variable = command.command_parameters['x']           
            pre = state.predicate_values
            post = deepcopy(pre)
            for indv in new_individuals:
                if indv == new_individual:
                    post[x_variable][indv]=logic.frombool(True)
                else:
                    post[x_variable][indv]=logic.frombool(False)
            for pointer in state.pointers:
                if pointer == x_variable: 
                    continue
                for indv in new_individuals:
                    if indv == new_individual:
                        post[pointer][(indv)] = logic.frombool(False)
                    else: 
                        post[pointer][(indv)] = pre[pointer][(indv)]
            for indv1 in new_individuals:
                for indv2 in new_individuals:
                    if indv1 == new_individual or indv2 == new_individual:
                        post['n'][(indv1,indv2)] = logic.frombool(False)
                    else:
                        post['n'][(indv1,indv2)] = pre['n'][(indv1,indv2)]
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
        """UNTESTED"""
        disjunction_list = ORC.disjunction_list
        disjunction_results = []
        for disjunct in disjunction_list:
            conjunction_list = disjunct.conjunction_list
            conjunction_results = []
            for boolcondition in conjunction_list:
                result = state_transformers.evaluate_boolcondition_on_state(state,boolcondition,logic)
                conjunction_list.append(result)
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

        """FROM HERE ON ITS NEWER AND MIGHT HAVE BUGS"""
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
    constraints = {}
    abstraction_predicates = {}
    """UNTESTED"""

    def abstract_transformer(set_of_states: Set[State], command: Command, logic):
        #focus -> coerce -> [st]_3 -> coerce -> t_embed
        focus_result = set_transformers.focus_set(set,command)
        coerce1_result = set_transformers.coerce_set(focus_result)
        transformer_result = set_transformers.evaluate_transformer_on_set(coerce1_result,command,ThreeVal)
        coerce2_result = set_transformers.coerce_set(transformer_result)
        embed_result = set_transformers.cannonical_embed_set(coerce2_result)
        return embed_result

    def focus_set(set_of_states : Set[State], command: Command):
        outset = set()
        focus_formulae = command.focus_formulae
        for state in set:
            new_states = helper_functions.focus(state,focus_formulae)
            outset.update(new_states)
        return outset

    def coerce_set(set_of_states :Set[State]):
        outset = set()
        for state in set_of_states:
            coerce_result = helper_functions.coerce(state,set_transformers.constraints)
            if coerce_result != None:
                outset.add(coerce_result)
        return outset

    def cannonical_embed_set(set_of_states: Set[State]):
        outset = set()
        for state in set_of_states:
            embed_result = helper_functions.cannonical_embedding(state,set_transformers.abstraction_predicates)
            outset.add(embed_result)
        return outset

    def evaluate_transformer_on_set(set_of_states: Set[State],command: Command, logic):
        simple_commands = {CommandType.C_Skip,CommandType.C_Assign_Var,CommandType.C_Assign_Null,CommandType.C_Assign_To_Next,CommandType.C_Set_Next_To_Var,CommandType.C_Set_Next_To_Null,CommandType.C_New}
        if command.command_type in simple_commands:
            return {state_transformers.evaluate_transformer_on_state(state,command,logic) for state in set_of_states}

        if command.command_type == CommandType.C_Assume:
            return {state for state in set_of_states if state_transformers.evaluate_boolean_condition_on_state(command.command_parameters['E'])}

        if command.command_type == CommandType.C_Assert:
            outset = set()
            for state in set:
                assert_orc = command.command_parameters['ORC']
                assert_result = state_transformers.evaluate_assert_on_state(state,assert_orc,logic)
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

