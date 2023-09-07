from transformers import *

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

    def empty(self):
        predicate_values = {'sm':{},'n':{}} 
        for pointer in self.pointers:
            predicate_values[pointer] = {}
        return State(self.pointers,self.instrumentation,self.individuals,predicate_values,self.logic)
