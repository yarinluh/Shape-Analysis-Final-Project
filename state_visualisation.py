# Import the necessary modules
from graphviz import Digraph
from state import State,include_odd_even
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
    node = 0
    for individual in individuals:
        sm_value = predicate_values['sm'].get(individual, ThreeVal.Zero)
        if sm_value == ThreeVal.Half:
            dot.node(individual, 'u'+str(node) , shape='doublecircle')
        else:
            dot.node(individual, 'u'+str(node))
        node = node+1
        dot.node(individual+"ghost"+"one","",shape = 'none')
        dot.node(individual+"ghost"+"half","",shape = 'none')

    # Add edges based on the 'n' predicate values
    for source_individual in individuals:
        for target_individual in individuals:
            edge_weight = predicate_values['n'].get((source_individual, target_individual), 0)
            if edge_weight == ThreeVal.One:
                dot.edge(source_individual, target_individual)
            elif edge_weight == ThreeVal.Half:
                dot.edge(source_individual, target_individual, style='dashed')

    # Add arrows for non-'n' and non-'sm' predicate values
    for individual in individuals:
        one_label = ""
        half_label = ""
        for key, value_dict in predicate_values.items():
            if key not in ('n', 'sm'):
                value = value_dict[individual]
                if value == ThreeVal.One:
                    if one_label:
                        one_label += ", "
                    one_label += key
                elif value == ThreeVal.Half:
                    if half_label:
                        half_label += ", "
                    half_label += key
        if one_label:
            dot.edge(individual + "ghost"+"one", individual, label=one_label)
        if half_label:
            dot.edge(individual + "ghost"+"half", individual, label=half_label, style="dotted")

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


def delete_png_files_in_state_figures():
    folder_path = "state_figures"

    try:
        # List all files in the state_figures folder
        file_list = os.listdir(folder_path)
        
        # Iterate through the files and delete .png files
        for file_name in file_list:
            if file_name.endswith(".png"):
                file_path = os.path.join(folder_path, file_name)
                os.remove(file_path)
                print(f"Deleted: {file_name}")

        print("Deletion complete.")
    
    except FileNotFoundError:
        print(f"Folder '{folder_path}' not found.")
    except Exception as e:
        print(f"An error occurred: {str(e)}")

