from enum import Enum
from typing import List
from saav_parser.e_conditions import ECondition
from saav_parser.or_conditions import ORCondition
from saav_parser.constants import *

class CommandType(Enum):
    C_Skip = 1
    C_Assign_Var = 2
    C_Assign_Const = 3
    C_Assign_Unknown = 4
    C_Plus1 = 5
    C_Minus1 = 6
    C_Assume = 7
    C_Assert = 8

class Command:
    def __init__(self, command_text: str):
        self.command_text: List[str] = command_text.split(" ")
        self.command_type: CommandType = self.get_command_type()
        self.command_parameters: dict = self.get_command_parameters()

    def get_command_type(self) -> CommandType:
        if self.command_text == ["skip"]:
            return CommandType.C_Skip
        
        if len(self.command_text) == 3 and \
            self.command_text[0] in VARIABLE_NAMES and \
            self.command_text[1] == ASSIGNMENT and \
            self.command_text[2] in VARIABLE_NAMES:
            return CommandType.C_Assign_Var

        if len(self.command_text) == 3 and \
            self.command_text[0] in VARIABLE_NAMES and \
            self.command_text[1] == ASSIGNMENT and \
            self.command_text[2].isdigit():
            return CommandType.C_Assign_Const
        
        if len(self.command_text) == 3 and \
            self.command_text[0] in VARIABLE_NAMES and \
            self.command_text[1] == ASSIGNMENT and \
            self.command_text[2] == QUESTION_MARK:
            return CommandType.C_Assign_Unknown

        if len(self.command_text) == 5 and \
            self.command_text[0] in VARIABLE_NAMES and \
            self.command_text[1] == ASSIGNMENT and \
            self.command_text[2] in VARIABLE_NAMES and \
            self.command_text[3] == PLUS and \
            self.command_text[4] == ONE_DIGIT:
            return CommandType.C_Plus1
        
        if len(self.command_text) == 5 and \
            self.command_text[0] in VARIABLE_NAMES and \
            self.command_text[1] == ASSIGNMENT and \
            self.command_text[2] in VARIABLE_NAMES and \
            self.command_text[3] == MINUS and \
            self.command_text[4] == ONE_DIGIT:
            return CommandType.C_Minus1
        

        if self.command_text[0] == "assume":
            try:
                ECondition(econdition_text=self.command_text[1:])
                return CommandType.C_Assume
            except SyntaxError:
                pass
        
        if self.command_text[0] == "assert":
            try:
                ORCondition(orcondition_text=' '.join(self.command_text[1:]))
                return CommandType.C_Assert
            except SyntaxError:
                pass
        
        raise SyntaxError(f"Ilegal Command: {self.command_text}.")
        
    def get_command_parameters(self) -> dict:
        if self.command_type == CommandType.C_Skip:
            return {}

        if self.command_type == CommandType.C_Assign_Var:
            return {"i": self.command_text[0],
                    "j": self.command_text[2]}

        if self.command_type == CommandType.C_Assign_Const:
            return {"i": self.command_text[0],
                    "K": int(self.command_text[2])}

        if self.command_type == CommandType.C_Assign_Unknown:
            return {"i": self.command_text[0]}

        if self.command_type == CommandType.C_Plus1:
            return {"i": self.command_text[0],
                    "j": self.command_text[2]}

        if self.command_type == CommandType.C_Minus1:
            return {"i": self.command_text[0],
                    "j": self.command_text[2]}

        if self.command_type == CommandType.C_Assume:
            return {"E": ECondition(econdition_text=self.command_text[1:])}

        if self.command_type == CommandType.C_Assert:
            return {"ORC": ORCondition(orcondition_text=' '.join(self.command_text[1:]))}
        
        raise SyntaxError(f"Ilegal Command: {self.command_text}.")


    def __repr__(self) -> str:
        if self.command_type == CommandType.C_Skip:
            return 'skip'

        if self.command_type == CommandType.C_Assign_Var:
            return f"{self.command_parameters['i']} {ASSIGNMENT} {self.command_parameters['j']}"

        if self.command_type == CommandType.C_Assign_Const:
            return f"{self.command_parameters['i']} {ASSIGNMENT} {self.command_parameters['K']}"

        if self.command_type == CommandType.C_Assign_Unknown:
            return f"{self.command_parameters['i']} {ASSIGNMENT} {QUESTION_MARK}"

        if self.command_type == CommandType.C_Plus1:
            return f"{self.command_parameters['i']} {ASSIGNMENT} {self.command_parameters['j']} {PLUS} {ONE_DIGIT}"

        if self.command_type == CommandType.C_Minus1:
            return f"{self.command_parameters['i']} {ASSIGNMENT} {self.command_parameters['j']} {MINUS} {ONE_DIGIT}"

        if self.command_type == CommandType.C_Assume:
            return f"assume {self.command_parameters['E']}"

        if self.command_type == CommandType.C_Assert:
            return f"assert {self.command_parameters['ORC']}"
        
        raise SyntaxError(f"Ilegal Command: {self.command_text}.")
