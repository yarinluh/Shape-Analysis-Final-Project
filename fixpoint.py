from control_flow_graph import ControlFlowGraph
from time import time
from transformers import *
from state import State

def chaotic_iteration(cfg,pointers):
    nodes = cfg.nodes
    states_vector = [{} for _ in nodes] #Bottom is poor - maybe just have an empty structure as well
    start_node = cfg.find_start_label()
    states_vector[start_node] = {State.create_empty_state(pointers)}
    worklist = set(nodes)
    iteration = 0
    start_time = time()

    while worklist:
        print(f"\nIteration #{iteration} (started after {int(time()-start_time)} seconds).")
        print(f"Current worklist: {worklist}.")
        node = worklist.pop()
        new_vector = update_node_state(cfg, states_vector, node)
        if new_vector != states_vector: 
            dependencies = create_dependencies_of_node(cfg,node)
            worklist=worklist.union(dependencies)
        states_vector = new_vector
        iteration = iteration + 1
    return states_vector
                
def update_node_state(cfg, states_vector, node):
    new_vector = states_vector.copy()
    ingoing_edges = cfg.ingoing_edges(node)
    if ingoing_edges:
        ingoing_states = []
        for line in ingoing_edges:
            print("\n",line)
            start = line.start_label

            print("\n",start,states_vector[start])
            new_state = set_transformers.abstract_transformer(states_vector[start], line.command, ThreeVal)
            
            print("\n",node,new_state)
            ingoing_states.append(new_state)
            

        new_state_for_node = union(ingoing_states)
        if len(ingoing_edges) > 1:
            #print("\n","join_result for",node,new_state_for_node)
            pass
        new_vector[node] = new_state_for_node
        #print('location'+str(node),new_state_for_node)
        #draw_set_of_states(new_state_for_node,'location:'+str(node))
    return new_vector

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

