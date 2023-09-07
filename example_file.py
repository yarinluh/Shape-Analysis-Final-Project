from pathlib import Path
from shape_parser import Program, Command
from shape_analysis_start import *

def read_example_program():
    path = Path('example_program.txt')
    program = Program(path)

    for line in program.program_lines:
        command: Command = line.command
        print(command.command_type, command.command_parameters)

def example():
    pointers = {'x','t'}
    instrumentation = {'c'}

    individuals = ['u0','u1']
    zero = TwoVal.Zero
    one = TwoVal.One

    predicate_values = {
        'x': {('u0'): one,('u1'):zero},
        't': {('u0'): one,('u1'):zero},
        'n': {('u0','u0'): zero,('u0','u1'): one,('u1','u0'): zero,('u1','u1'): zero},
        'c': {('u0'): one,('u1'): one }}
    state0 = State(pointers,instrumentation,individuals,predicate_values)
    command1 = Command('x := t')
    state1 = concrete_transformers.evaluate_transformer(state0,command1,TwoVal)
    command2 = Command('x := t.n')
    state2 = concrete_transformers.evaluate_transformer(state0,command2,TwoVal)
    command3 = Command('x.n := t')
    state3 = concrete_transformers.evaluate_transformer(state0,command3,TwoVal)
    command4 = Command('x := new')
    state4 = concrete_transformers.evaluate_transformer(state0,command4,TwoVal)
    print(state0) 
    print(state4)   

def example2():
    path = Path('simple_example.txt')
    program = Program(path)
    state = State(['x','y'],predicate_values={'x':{},'y':{},'n':{}})
    print(state)
    for line in program.program_lines:
        command: Command = line.command
        print(command.command_type, command.command_parameters)
        new_state = concrete_transformers.evaluate_transformer_on_state(state,command,TwoVal)
        print(new_state)
        state = new_state

example2()