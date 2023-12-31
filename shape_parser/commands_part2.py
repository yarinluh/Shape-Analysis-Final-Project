from enum import Enum
from typing import List
from xml.dom.minidom import parseString
from shape_parser.e_conditions import ECondition,EConditionType
from shape_parser.or_conditions import ORCondition
from shape_parser.constants import *

class CommandType(Enum):
    C_Skip = 1
    C_Assign_Var = 2
    C_Assign_Null = 3
    C_Assign_To_Next = 4
    C_Set_Next_To_Var = 5
    C_Set_Next_To_Null = 6
    C_New = 7
    C_Assume = 8
    C_Assert = 9

class Command:
    def __init__(self, command_text: str):
        self.command_text: List[str] = command_text.split(" ")
        self.command_type: CommandType = self.get_command_type()
        self.command_parameters: dict = self.get_command_parameters()
        self.focus_formulae : set = self.get_focus_formulae()

    def get_command_type(self) -> CommandType:
        if self.command_text == ["skip"]:
            return CommandType.C_Skip
        
        if len(self.command_text) == 3 and self.command_text[0] in VARIABLE_NAMES and self.command_text[1] == ASSIGNMENT:

            third_word: str = self.command_text[2]
            if third_word in VARIABLE_NAMES:
                return CommandType.C_Assign_Var
            if third_word == NULL:
                return CommandType.C_Assign_Null
            if third_word == NEW:
                return CommandType.C_New

            third_word_dot_splitted: List[str] = third_word.split('.')
            if len(third_word_dot_splitted) == 2 and third_word_dot_splitted[0] in VARIABLE_NAMES and third_word_dot_splitted[1] == 'n':
                return CommandType.C_Assign_To_Next

        if len(self.command_text) == 3 and self.command_text[1] == ASSIGNMENT:
            first_word_dot_splitted: List[str] = self.command_text[0].split('.')
            if len(first_word_dot_splitted) == 2 and\
                first_word_dot_splitted[0] in VARIABLE_NAMES and\
                first_word_dot_splitted[1] == 'n':
                if self.command_text[2] in VARIABLE_NAMES:
                    return CommandType.C_Set_Next_To_Var
                if self.command_text[2] == NULL:
                    return CommandType.C_Set_Next_To_Null

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
            return {"x": self.command_text[0], "y": self.command_text[2]}

        if self.command_type == CommandType.C_Assign_Null:
            return {"x": self.command_text[0]}

        if self.command_type == CommandType.C_Assign_To_Next:
            return {"x": self.command_text[0], "y": self.command_text[2].split('.')[0]}

        if self.command_type == CommandType.C_Set_Next_To_Var:
            return {"x": self.command_text[0].split('.')[0], "y": self.command_text[2]}
        
        if self.command_type == CommandType.C_Set_Next_To_Null:
            return {"x": self.command_text[0].split('.')[0]}

        if self.command_type == CommandType.C_New:
            return {"x": self.command_text[0]}

        if self.command_type == CommandType.C_Assume:
            return {"E": ECondition(econdition_text=self.command_text[1:])}

        if self.command_type == CommandType.C_Assert:
            return {"ORC": ORCondition(orcondition_text=' '.join(self.command_text[1:]))}
        
        raise SyntaxError(f"Ilegal Command: {self.command_text}.")

    def get_focus_formulae(self):
        type = self.command_type 
        param = self.command_parameters

        if type == CommandType.C_Skip:
            return {}

        if type == CommandType.C_Assign_Var: 
            return {param['y']}

        if type == CommandType.C_Assign_Null: 
            return {param['x']}

        if type == CommandType.C_Assign_To_Next:
            return {('n',param['y'])}

        if type == CommandType.C_Set_Next_To_Var:
            return {param['x'],param['y']}

        if type == CommandType.C_Set_Next_To_Null: 
            return {param['x']}

        if type == CommandType.C_New:
            return {}

        if type == CommandType.C_Assume:
            econdition = self.command_parameters['E']
            type = econdition.econdition_type
            e_param = econdition.econdition_parameters

            if type == EConditionType.E_True:
                return {}
            
            if type == EConditionType.E_False:
                return {}
            
            if type == EConditionType.E_Equal_Var:
                return {e_param['i'],e_param['j']}
            
            if type == EConditionType.E_Diff_Var:
                return {e_param['i'],e_param['j']}
 
            if type == EConditionType.E_Equal_Null:
                return {e_param['i']}
                
            if type == EConditionType.E_Diff_Null:
                return {e_param['i']}
        

        if type == CommandType.C_Assert:
            #Currently not focusing on assertions - probably should?
            return {}

    def __repr__(self) -> str:
        if self.command_type == CommandType.C_Skip:
            return 'skip'

        if self.command_type == CommandType.C_Assign_Var:
            return f"{self.command_parameters['x']} {ASSIGNMENT} {self.command_parameters['y']}"

        if self.command_type == CommandType.C_Assign_Null:
            return f"{self.command_parameters['x']} {ASSIGNMENT} {NULL}"

        if self.command_type == CommandType.C_Assign_To_Next:
            return f"{self.command_parameters['x']} {ASSIGNMENT} {self.command_parameters['y']}.n"

        if self.command_type == CommandType.C_Set_Next_To_Var:
            return f"{self.command_parameters['x']}.n {ASSIGNMENT} {self.command_parameters['y']}"
        
        if self.command_type == CommandType.C_Set_Next_To_Null:
            return f"{self.command_parameters['x']}.n {ASSIGNMENT} {NULL}"

        if self.command_type == CommandType.C_New:
            return f"{self.command_parameters['x']} {ASSIGNMENT} {NEW}"

        if self.command_type == CommandType.C_Assume:
            return f"assume {self.command_parameters['E']}"

        if self.command_type == CommandType.C_Assert:
            return f"assert {self.command_parameters['ORC']}"
        
        raise SyntaxError(f"Ilegal Command: {self.command_text}.")
