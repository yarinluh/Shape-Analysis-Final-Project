from time import time
from logical_expressions import *
import json

include_odd_even = True #Toggle even-odd instrumentation

class State:
    def __init__(self,pointers={},instrumentation={},individuals={},predicate_values={},logic=TwoVal):
        #predicate_values is a dictionary that maps each predicate to a a dictionary of mapping lists of individuals to a booelean/3-valued value
        self.logic = logic
        self.pointers = pointers
        self.instrumentation = instrumentation
        self.individuals = individuals
        self.predicate_values = predicate_values #values for all predicates (pointers,instrumentation)

    def __repr__(self):
        return "\nindividuals:" + self.individuals.__repr__() + "\npredicate values: " + self.predicate_values.__repr__() 

    def value_of_predicate(self,predicate,arguments):
        #arguments is a list from the list of individuals
        return self.predicate_values[predicate][arguments]
    
    def change_indvs_or_values(self,new_individuals,new_predicate_values):
        return State(self.pointers,self.instrumentation,new_individuals,new_predicate_values,self.logic)

    def __hash__(self):
        # Create a list of tuples containing (key, value) pairs from individuals
        individuals_items = list(self.individuals)

        # Create a list of tuples containing (key, value) pairs from the predicate_values dictionary
        pred_items = []
        self_dict = self.predicate_values

        for key in self_dict.keys():  # Corrected this line
            inter_dict = self_dict[key]
            for in_key in inter_dict.keys():  # Corrected this line
                pred_items.append((key,in_key,inter_dict[in_key]))

        # Sort the lists to ensure consistent hash values
        individuals_items.sort()
        pred_items.sort()

        # Combine the sorted items into a single tuple
        hashable_items = tuple(individuals_items + pred_items)

        return hash(hashable_items)

    def __eq__(self, other):
    # Assuming the signature is the same
        if self is None or other is None:
            return self is None and other is None
        if self.individuals != other.individuals:
            return False
        
        self_dict = self.predicate_values
        other_dict = other.predicate_values  # Corrected this line

        for key in self_dict.keys():  # Corrected this line
            inter_dict = self_dict[key]
            other_inter_dict = other_dict[key]
            for in_key in inter_dict.keys():  # Corrected this line
                if inter_dict[in_key] != other_inter_dict.get(in_key):  # Corrected this line
                    return False

        return True

    def create_empty_state(pointers):
        set_of_pointers = set(pointers)
        instrumentation_set = {'is','c','sm'}
        for pointer in set_of_pointers:
            instrumentation_set.add('r-'+pointer)
            if include_odd_even:
                instrumentation_set.add('r-even-'+pointer)
                instrumentation_set.add('r-odd-'+pointer)
        predicate_values = {}
        for pointer in set_of_pointers:
            predicate_values[pointer]={}
        for instr in instrumentation_set:
            predicate_values[instr]={}
        predicate_values['n'] = {}

        empty_state = State(set_of_pointers,instrumentation_set,set(),predicate_values,ThreeVal)
        return empty_state