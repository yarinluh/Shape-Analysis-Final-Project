from enum import Enum
from typing import List
from shape_parser.constants import *

class BoolConditionType(Enum):
    B_NULL_POINTER = 1              # x = NULL
    B_NOT_NULL_POINTER = 2          # x != NULL
    B_VARIABLE_POINTER = 3          # x = y
    B_NOT_VARIABLE_POINTER = 4      # x != y
    B_NEXT_POINTER = 5              # x = y.n
    B_NOT_NEXT_POINTER  = 6         # x != y.n
    B_LIST = 7                      # LS x y
    B_NOT_LIST = 8          # NOLS x y
    B_ODD_LIST = 9                  # ODD x y
    B_EVEN_LIST = 10                # EVEN x y

class BOOLCondition:
    def __init__(self, boolcondition_text: str):
        self.boolcondition_text: List[str] = boolcondition_text.split(' ')
        self.boolcondition_type: BoolConditionType = self.get_boolcondition_type()
        self.boolcondition_parameters: dict = self.get_boolcondition_parameters()

    def get_boolcondition_type(self) -> BoolConditionType:
        if len(self.boolcondition_text) != 3:
            raise SyntaxError(f"Ilegal BOOLCondition: {self.boolcondition_text}.")
        first_word: str = self.boolcondition_text[0]
        second_word: str = self.boolcondition_text[1]
        third_word: str = self.boolcondition_text[2]

        if first_word in VARIABLE_NAMES:
            
            if second_word == EQUAL:

                if third_word == NULL:
                    return BoolConditionType.B_NULL_POINTER
                
                if third_word in VARIABLE_NAMES:
                    return BoolConditionType.B_VARIABLE_POINTER
                
                third_word_dot_splitted: List[str] = third_word.split('.')
                if len(third_word_dot_splitted) == 2 and third_word_dot_splitted[0] in VARIABLE_NAMES and third_word_dot_splitted[1] == 'n':
                    return BoolConditionType.B_NEXT_POINTER
            
            elif second_word == NOT_EQUAL:

                if third_word == NULL:
                    return BoolConditionType.B_NOT_NULL_POINTER
                
                if third_word in VARIABLE_NAMES:
                    return BoolConditionType.B_NOT_VARIABLE_POINTER
                
                third_word_dot_splitted: List[str] = third_word.split('.')
                if len(third_word_dot_splitted) == 2 and third_word_dot_splitted[0] in VARIABLE_NAMES and third_word_dot_splitted[1] == 'n':
                    return BoolConditionType.B_NOT_NEXT_POINTER
                
        elif second_word in VARIABLE_NAMES and third_word in VARIABLE_NAMES:

            if first_word == LS:
                return BoolConditionType.B_LIST
            
            if first_word == NOLS:
                return BoolConditionType.B_NOT_LIST
            
            if first_word == ODD:
                return BoolConditionType.B_ODD_LIST
            
            if first_word == EVEN:
                return BoolConditionType.B_EVEN_LIST

        raise SyntaxError(f"Ilegal BOOLCondition: {self.boolcondition_text}.")
    
    def get_boolcondition_parameters(self) -> dict:
        if self.boolcondition_type in {BoolConditionType.B_NULL_POINTER, BoolConditionType.B_NOT_NULL_POINTER}:
            return {"x": self.boolcondition_text[0]}
        
        if self.boolcondition_type in {BoolConditionType.B_VARIABLE_POINTER, BoolConditionType.B_NOT_VARIABLE_POINTER}:
            return {"x": self.boolcondition_text[0], "y": self.boolcondition_text[2]}
        
        if self.boolcondition_type in {BoolConditionType.B_NEXT_POINTER, BoolConditionType.B_NOT_NEXT_POINTER}:
            third_word_dot_splitted: List[str] = self.boolcondition_text[2].split('.')
            return {"x": self.boolcondition_text[0], "y": third_word_dot_splitted[0]}
        
        if self.boolcondition_type in {BoolConditionType.B_LIST, BoolConditionType.B_NOT_LIST,
                                       BoolConditionType.B_ODD_LIST, BoolConditionType.B_EVEN_LIST}:
            return {"x": self.boolcondition_text[1], "y": self.boolcondition_text[2]}
        
        raise SyntaxError(f"Ilegal BOOLCondition: {self.boolcondition_text}.")

    def __repr__(self) -> str:
        return ' '.join(self.boolcondition_text)
