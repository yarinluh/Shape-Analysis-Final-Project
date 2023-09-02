from pathlib import Path
from shape_parser import Program, Command

def read_example_program():
    path = Path('example_program.txt')
    program = Program(path)

    for line in program.program_lines:
        command: Command = line.command
        print(command.command_type, command.command_parameters)

read_example_program()
