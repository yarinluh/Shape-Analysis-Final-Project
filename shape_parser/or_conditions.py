from typing import List
from shape_parser.and_conditions import ANDCondition

class ORCondition:
    def __init__(self, orcondition_text: str):
        self.orcondition_text: str = orcondition_text
        self.disjunction_list: List[ANDCondition] = self.get_disjunction_list()

    def get_disjunction_list(self): # -> List[ANDCondition]:
        if self.orcondition_text == "" or self.orcondition_text[-1] != ')':
            raise SyntaxError(f"Ilegal ORCondition: {self.orcondition_text}.")
        
        parsed_text: List[str] = self.orcondition_text.split(')')[:-1]
        parsed_text = [word.strip() for word in parsed_text]
        if not all([word.startswith('(') for word in parsed_text]):
            raise SyntaxError(f"Ilegal ORCondition: {parsed_text}.")
        else:
            parsed_text = [word[1:] for word in parsed_text]

        return [ANDCondition(andcondition_text=word) for word in parsed_text]

    def __repr__(self) -> str:
        s = ""
        for and_condition in self.disjunction_list:
            s += f"({and_condition}) "
        return s[:-1]
