from control_flow_graph import ControlFlowGraph
from time import time
from transformers import *
from state import State

def chaotic_iteration(cfg,pointers):
    nodes = cfg.nodes
    states_dictionary  = {n: set() for n in nodes}
    start_node = cfg.find_start_label()
    print('start node',start_node)
    states_dictionary[start_node] = {State.create_empty_state(pointers)}
    worklist = set(nodes)
    iteration = 0
    start_time = time()

    while worklist:
        print(f"\nIteration #{iteration} (started after {int(time()-start_time)} seconds).")
        print(f"Current worklist: {worklist}.")
        node = worklist.pop()
        new_dictionary = update_node_state(cfg, states_dictionary, node)
        if new_dictionary != states_dictionary: 
            dependencies = create_dependencies_of_node(cfg,node)
            worklist=worklist.union(dependencies)
        states_dictionary = new_dictionary
        iteration = iteration + 1
    print(f"\nFinished after {int(time()-start_time)} seconds.\n")
    return states_dictionary
                
def update_node_state(cfg, states_dictionary, node):
    new_dictionary = states_dictionary.copy()
    ingoing_edges = cfg.ingoing_edges(node)
    if ingoing_edges:
        ingoing_states = []
        for line in ingoing_edges:
            print("\n",line)
            start = line.start_label

            print("\n",start,len(states_dictionary[start]))
            #draw_set_of_states(states_dictionary[start],'location '+str(start))

            new_state = set_transformers.abstract_transformer(new_dictionary[start], line.command)
            
            #print("\n",node,new_state)
            ingoing_states.append(new_state)
            
        new_state_for_node = union(ingoing_states)
        if len(ingoing_edges) > 1:
            #print("\n","join_result for",node,new_state_for_node)
            pass
        new_dictionary[node] = new_state_for_node
        #print('location'+str(node),new_state_for_node)
        #draw_set_of_states(new_state_for_node,'location:'+str(node))

    return new_dictionary

def create_dependencies_of_node(cfg,node):
    result = set()
    outgoing_edges = cfg.outgoing_edges(node)
    for line in outgoing_edges:
        end = line.end_label
        result.add(end)
    return result

def union(sets : List):
    outset = set()
    for setvar in sets:
        outset.update(setvar)
    return outset

