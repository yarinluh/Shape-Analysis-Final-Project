from shape_parser import Program, ProgramLine
from typing import List, Union
import networkx as nx
import matplotlib.pyplot as plt

def create_graph_from_program(program: Program) -> nx.DiGraph:
    G = nx.DiGraph()
    for program_line in program.program_lines:
        G.add_edge(*program_line.get_edge_label())
    return G

class ControlFlowGraph:
    def __init__(self, program: Program):
        self.program: Program = program
        self.nodes: List[int] = self.program.get_all_labels()
        
    def plot_graph(self):
        graph: nx.DiGraph = create_graph_from_program(self.program)
        pos = nx.spring_layout(graph)
        plt.figure()

        edge_labels: dict = {}
        for program_line in self.program.program_lines:
            edge_labels[program_line.get_edge_label] = str(program_line.command)

        nx.draw(graph, pos=pos, edge_color='black', width=1, linewidths=1, node_size=500, node_color='cyan',
                labels={node: node for node in graph.nodes()})
        
        nx.draw_networkx_edge_labels(graph, pos,
                                     edge_labels={program_line.get_edge_label(): str(program_line.command)
                                                  for program_line in self.program.program_lines},
                                                  font_size=16)

        plt.show()

    def ingoing_edges(self, node: int) -> List[ProgramLine]:
        return [program_line for program_line in self.program.program_lines
                if program_line.end_label == node]

    def outgoing_edges(self, node: int) -> List[ProgramLine]:
        return [program_line for program_line in self.program.program_lines
                if program_line.start_label == node]

    def find_start_label(self) -> int:
        for node in self.nodes:
            if len(self.ingoing_edges(node)) == 0:
                return node
        raise SyntaxError("Could not find a starting label!")
