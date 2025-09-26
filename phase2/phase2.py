import re
import os 

class Node:
    def __init__(self, value, left=None, right=None):
        self.value = value
        self.left = left
        self.right = right

def check_balanced_parentheses(formula):
    count = 0
    for char in formula:
        if char == '(':
            count += 1
        elif char == ')':
            count -= 1
        if count < 0:
            return False
    return count == 0

def validate_characters(formula):
    pattern = r'^[a-z¬∧∨→()\s]*$'
    return bool(re.match(pattern, formula))

def tokenize(formula):
    formula = formula.replace(' ', '')
    tokens = []
    i = 0
    while i < len(formula):
        if formula[i] in '()¬∧∨→':
            tokens.append(formula[i])
        elif formula[i].isalpha() and formula[i].islower():
            tokens.append(formula[i])
        else:
            return None
        i += 1
    return tokens

def parseTree(tokens):
    """
    Constructs and returns the root Node of the parse tree for a list of tokens.
    """
    node, final_pos = _parse_formula_recursive(tokens, 0)
    if node and final_pos == len(tokens):
        return node
    return None

def _parse_formula_recursive(tokens, current_pos_offset):

    def parse_primary_wff_internal(pos):
        if pos >= len(tokens):
            return None, pos

        token = tokens[pos]

        if token.isalpha() and token.islower():
            return Node(token), pos + 1
        
        elif token == '¬':
            child_node, next_pos = parse_primary_wff_internal(pos + 1)
            if child_node:
                return Node('¬', child_node), next_pos
            return None, pos
        
        elif token == '(':
            balance = 0
            end_paren_idx = -1
            for i in range(pos, len(tokens)):
                if tokens[i] == '(':
                    balance += 1
                elif tokens[i] == ')':
                    balance -= 1
                if balance == 0:
                    end_paren_idx = i
                    break
            
            if end_paren_idx == -1:
                return None, pos
            
            inner_tokens = tokens[pos + 1 : end_paren_idx]
            
            inner_node, _ = _parse_formula_recursive(inner_tokens, 0)
            
            if inner_node and (len(inner_tokens) == 0 or _parse_formula_recursive(inner_tokens, 0)[1] == len(inner_tokens)):
                return inner_node, end_paren_idx + 1
            
            return None, pos
        
        return None, pos

    node, final_pos_relative = parse_primary_wff_internal(0)
    if node and final_pos_relative == len(tokens):
        return node, final_pos_relative + current_pos_offset

    outermost_op_index = -1
    depth = 0
    binary_operators = ['∧', '∨', '→']

    for i in range(len(tokens)):
        if tokens[i] == '(':
            depth += 1
        elif tokens[i] == ')':
            depth -= 1
        elif tokens[i] in binary_operators and depth == 0:
            if outermost_op_index != -1:
                return None, 0
            outermost_op_index = i

    if outermost_op_index != -1:
        op = tokens[outermost_op_index]
        left_tokens = tokens[:outermost_op_index]
        right_tokens = tokens[outermost_op_index+1:]

        left_node, left_final_pos = _parse_formula_recursive(left_tokens, 0)
        right_node, right_final_pos = _parse_formula_recursive(right_tokens, 0)

        if (left_node and left_final_pos == len(left_tokens)) and \
            (right_node and right_final_pos == len(right_tokens)):
            return Node(op, left_node, right_node), len(tokens) + current_pos_offset
        
    return None, 0


# CNF Conversion Functions

def _is_literal(node):
    """Checks if a node represents a literal (atom or negated atom)."""
    if node is None:
        return False
    if node.value.isalpha() and node.value.islower():
        return True
    if node.value == '¬' and node.left and node.left.value.isalpha() and node.left.value.islower():
        return True
    return False

def _distribute(cnf1, cnf2):
    """
    Distributes two CNF formulas during an OR operation.
    """
    new_cnf_clauses = []
    for clause1 in cnf1:
        for clause2 in cnf2:
            combined_literals = []
            seen_literals = set()

            def literal_to_unique_str(lit_node):
                if lit_node.value == '¬':
                    return '¬' + lit_node.left.value
                return lit_node.value

            for lit in clause1 + clause2:
                lit_str = literal_to_unique_str(lit)
                if lit_str not in seen_literals:
                    seen_literals.add(lit_str)
                    combined_literals.append(lit)
            
            new_cnf_clauses.append(combined_literals)
    return new_cnf_clauses

def to_cnf(node):
    if node is None:
        return [] # Return empty CNF for empty input

    # Base Cases
    if _is_literal(node):
        return [[node]] # A literal is a CNF with one clause containing that literal

    # Eliminate Implications 
    if node.value == '→':
        # Create a new subtree representing ¬A ∨ B
        new_node = Node('∨', Node('¬', node.left), node.right)
        return to_cnf(new_node) # Recursively convert this new subtree

    #Move Negations Inwards (De Morgan's, Double Negation)
    if node.value == '¬':
        negated_child = node.left
        if negated_child.value == '¬': # ¬¬A  -> A
            return to_cnf(negated_child.left)
        elif negated_child.value == '∧': # ¬(A ∧ B) -> ¬A ∨ ¬B
            new_node = Node('∨', Node('¬', negated_child.left), Node('¬', negated_child.right))
            return to_cnf(new_node)
        elif negated_child.value == '∨': # ¬(A ∨ B) -> ¬A ∧ ¬B
            new_node = Node('∧', Node('¬', negated_child.left), Node('¬', negated_child.right))
            return to_cnf(new_node)
        
        elif negated_child.value == '→': # ¬(A → B) -> A ∧ ¬B
            new_node = Node('∧', negated_child.left, Node('¬', negated_child.right))
            return to_cnf(new_node)
        
        elif _is_literal(node): # This covers the ¬p case
            return [[node]]
        
    # Handle Conjunctions (A ∧ B)
    if node.value == '∧':
        cnf_left = to_cnf(node.left)
        cnf_right = to_cnf(node.right)
        # Combine clauses from both sides: (C1 ∧ C2) ∧ (C3 ∧ C4) = C1 ∧ C2 ∧ C3 ∧ C4
        return cnf_left + cnf_right

    # Handle Disjunctions (A ∨ B) - Apply Distribution
    if node.value == '∨':
        cnf_left = to_cnf(node.left)
        cnf_right = to_cnf(node.right)
        # Apply distributive law: (C_A1 ∧ C_A2) ∨ (C_B1 ∧ C_B2) -> (C_A1 ∨ C_B1) ∧ (C_A1 ∨ C_B2) ∧ ...
        return _distribute(cnf_left, cnf_right)

    # Fallback for unexpected node types (should not happen with valid WFFs)
    return []

def format_cnf_output(cnf_clauses):
    """
    Formats the CNF into the required string output.
    """
    if not cnf_clauses:
        return ""

    formatted_clauses = []
    is_single_clause_cnf = (len(cnf_clauses) == 1)

    for clause in cnf_clauses:
        literal_strings = []
        for literal_node in clause:
            if literal_node.value == '¬':
                literal_strings.append('¬' + literal_node.left.value)
            else:
                literal_strings.append(literal_node.value)
                clause_str = ' ∨ '.join(literal_strings)
        
        if len(clause) > 1 and not is_single_clause_cnf:
            formatted_clauses.append(f"({clause_str})")
        else:
            formatted_clauses.append(clause_str)
            
    return ' ∧ '.join(formatted_clauses)

def process_formula_to_cnf(formula):
    """
    Takes a well-formed formula (WFF) string and converts it to CNF.
    """
    tokens = tokenize(formula)
    parse_tree_root = parseTree(tokens)
    cnf_result = to_cnf(parse_tree_root)
    cnf_string = format_cnf_output(cnf_result)
    print(f"Input Formula: {formula}")
    print(f"CNF Output: {cnf_string}\n")


# --- Main execution block ---
def main():
    # Get the directory where the script itself is located
    script_directory = os.path.dirname(os.path.abspath(__file__))
    # Join that directory path with the filename to create an absolute path
    filename = os.path.join(script_directory, "cnf_tests.txt")

    try:
        with open(filename, 'r', encoding='utf-8') as f:
            for line in f:
                formula = line.strip()
                if formula:
                    process_formula_to_cnf(formula)
    except FileNotFoundError:
        print(f"Error: The file '{filename}' was not found.")
        print("Please ensure 'cnf_tests.txt' is in the same folder as your Python script.")

if __name__ == "__main__":
    main()