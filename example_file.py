from pathlib import Path
from shape_parser import Program, Command
from state import State
from fixpoint import chaotic_iteration
from control_flow_graph import ControlFlowGraph
from state_visualisation import *

def run_example(address):
    path = Path(address)
    program = Program(path)
    variables = program.program_variables
    cfg = ControlFlowGraph(program)
    print(cfg.nodes)
    ret = chaotic_iteration(cfg,variables)
    for i in range(len(ret)):
        print(i,len(ret[i]))
        draw_set_of_states(ret[i],'output at location '+str(i))

#is not appearing in this example for some reason - which then after coerce deletes some of the models - problem!

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

#delete_png_files_in_state_figures()
run_example('examples/new_file.txt')

#bug when updating r-x for x.n=y and x = y.n

