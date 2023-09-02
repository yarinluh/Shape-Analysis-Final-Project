from typing import List
from shape_parser.bool_conditions import BOOLCondition

class ANDCondition:
    def __init__(self, andcondition_text: str):
        self.andcondition_text: str = andcondition_text
        self.conjunction_list: List[BOOLCondition] = self.get_conjunction_list()

    def get_conjunction_list(self) -> List[BOOLCondition]:
        parsed_text: List[str] = self.andcondition_text.split('  ')
        return [BOOLCondition(boolcondition_text=word) for word in parsed_text]

    def __repr__(self) -> str:
        s = ""
        for bool_condition in self.conjunction_list:
            s += f"{bool_condition}  "
        return s[:-2]