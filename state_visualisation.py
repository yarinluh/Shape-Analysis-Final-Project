# Import the necessary modules
from graphviz import Digraph
from state import State
import os
from logical_expressions import *

def draw_state_graph(state,title):
    individuals = state.individuals
    predicate_values = state.predicate_values

    # Create the 'state_figures' folder if it doesn't exist
    output_folder = 'state_figures'
    if not os.path.exists(output_folder):
        os.makedirs(output_folder)

    # Create a unique filename for the PNG image
    image_filename = os.path.join(output_folder, f'state_{len(os.listdir(output_folder)) + 1}.png')


    # Create a Digraph object
    dot = Digraph()
    dot.attr(rankdir='LR')
    dot.attr(label=title)


    # Add nodes for each individual, handling 'sm' values
    for individual in individuals:
        sm_value = predicate_values['sm'].get(individual, ThreeVal.Zero)
        if sm_value == ThreeVal.Half:
            dot.node(individual, individual, shape='doublecircle')
        else:
            dot.node(individual, individual)
        dot.node(individual+"ghost","",shape = 'none')

    # Add edges based on the 'n' predicate values
    for source_individual in individuals:
        for target_individual in individuals:
            edge_weight = predicate_values['n'].get((source_individual, target_individual), 0)
            if edge_weight == ThreeVal.One:
                dot.edge(source_individual, target_individual)
            elif edge_weight == ThreeVal.Half:
                dot.edge(source_individual, target_individual, style='dashed')

    # Add arrows for non-'n' and non-'sm' predicate values
    for key, value_dict in predicate_values.items():
        if key not in ('n', 'sm'):
            for individual, value in value_dict.items():
                if value == ThreeVal.One:
                    dot.edge(individual+"ghost", individual, label=key)
                elif value == ThreeVal.Half:
                    dot.edge(individual+"ghost", individual, label=key, style='dashed')

    # Specify the output file format (e.g., PDF, PNG, SVG)
    dot.format = 'png'
    dot.render(image_filename, cleanup=True)

    return image_filename

def draw_set_of_states(set_of_states,name):
    option = 0
    for state_result in set_of_states:
        option = option+1
        title = name+" - option "+str(option)
        draw_state_graph(state_result,title)
