from pathlib import Path
from shape_parser import Program
from fixpoint import chaotic_iteration
from control_flow_graph import ControlFlowGraph
from state_visualisation import *
from transformers import errors
from logical_expressions import *

def run_example(address):
    path = Path(address)
    program = Program(path)
    variables = program.program_variables
    cfg = ControlFlowGraph(program)
    print(cfg.nodes)
    ret = chaotic_iteration(cfg,variables)
    errors.results() 
    for key,value in ret.items():
        print(key,len(value))
        draw_set_of_states(value,'output at location '+str(key))
    
delete_png_files_in_state_figures()
run_example('examples/duplicate_list.txt')
