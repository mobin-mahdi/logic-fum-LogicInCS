import re
import os
from typing import List, Tuple

class Node:
    """
    Represents a node in the parse tree of a propositional logic formula.
    Each node has a value (an operator like '∧' or an atom like 'p'),
    and optional left and right children.
    """
    def __init__(self, value, left=None, right=None):
        self.value = value
        self.left = left
        self.right = right

# --- Phase 1: Parsing and Formula Validation Functions ---

def check_balanced_parentheses(formula: str) -> bool:
    """Checks if parentheses in a formula are balanced."""
    count = 0
    for char in formula:
        if char == '(':
            count += 1
        elif char == ')':
            count -= 1
        if count < 0:
            return False
    return count == 0

def validate_characters(formula: str) -> bool:
    """Validates if a formula contains only allowed characters for this project."""
    # The pattern allows lowercase letters, operators, parentheses, the contradiction symbol, and spaces.
    pattern = r'^[a-z¬∧∨→⊥()\s]*$'
    return bool(re.match(pattern, formula))

def tokenize(formula: str) -> List[str]:
    """
    Tokenizes a formula string into a list of its components (atoms, operators, parentheses).
    Spaces are removed.
    """
    formula = formula.replace(' ', '')
    if not formula:
        return []
    # Regex to find all valid symbols.
    tokens = re.findall(r'¬|∧|∨|→|⊥|[a-z]|\(|\)', formula)
    return tokens

def parseTree(tokens: List[str]) -> Node:
    """
    Public function to construct and return the root Node of the parse tree.
    It acts as a wrapper for the recursive parsing logic.
    """
    if not tokens:
        return None
    # The recursive parser returns the node and the number of tokens consumed.
    # A valid parse must consume all tokens.
    node, final_pos = _parse_formula_recursive(tokens)
    if node and final_pos == len(tokens):
        return node
    return None

def _parse_formula_recursive(tokens: List[str]) -> Tuple[Node, int]:
    """
    Internal recursive function to parse a list of tokens into a Well-Formed Formula (WFF) tree.
    It handles operator precedence and parenthetical grouping.
    """
    if not tokens:
        return None, 0

    # --- Inner function to parse primary expressions ---
    def parse_primary_wff_internal(pos: int) -> Tuple[Node, int]:
        if pos >= len(tokens):
            return None, pos
        token = tokens[pos]

        if (token.isalpha() and token.islower()) or token == '⊥':
            return Node(token), pos + 1
        
        elif token == '¬':
            child_node, next_pos = parse_primary_wff_internal(pos + 1)
            if child_node:
                return Node('¬', child_node), next_pos
            return None, pos
        
        elif token == '(':
            balance = 1
            end_paren_idx = -1
            for i in range(pos + 1, len(tokens)):
                if tokens[i] == '(': balance += 1
                elif tokens[i] == ')': balance -= 1
                if balance == 0:
                    end_paren_idx = i
                    break
            
            if end_paren_idx != -1:
                inner_tokens = tokens[pos + 1 : end_paren_idx]
                inner_node, inner_final_pos = _parse_formula_recursive(inner_tokens)
                if inner_node and inner_final_pos == len(inner_tokens):
                    return inner_node, end_paren_idx + 1
            return None, pos
        
        return None, pos

    node, final_pos = parse_primary_wff_internal(0)
    if node and final_pos == len(tokens):
        return node, final_pos

    outermost_op_index = -1
    depth = 0
    for i in range(len(tokens) - 1, -1, -1):
        token = tokens[i]
        if token == ')': depth += 1
        elif token == '(': depth -= 1
        elif token in ['→', '∨', '∧'] and depth == 0:
            outermost_op_index = i
            break
            
    if outermost_op_index != -1:
        op = tokens[outermost_op_index]
        left_tokens = tokens[:outermost_op_index]
        right_tokens = tokens[outermost_op_index + 1:]

        left_node, left_consumed = _parse_formula_recursive(left_tokens)
        right_node, right_consumed = _parse_formula_recursive(right_tokens)

        if (left_node and left_consumed == len(left_tokens)) and \
            (right_node and right_consumed == len(right_tokens)):
            return Node(op, left_node, right_node), len(tokens)
        
    return None, 0

# --- Phase 5: Proof Validation Logic ---

def are_trees_structurally_equivalent(node1: Node, node2: Node) -> bool:
    """
    Recursively checks if two parse trees are structurally identical.
    """
    if not node1 and not node2: return True
    if not node1 or not node2: return False
    return (node1.value == node2.value and
            are_trees_structurally_equivalent(node1.left, node2.left) and
            are_trees_structurally_equivalent(node1.right, node2.right))

def validate_natural_deduction_proof(proof_lines: List[str]):
    """
    Validates a full natural deduction proof provided as a list of strings.
    This is the main function for Phase 5.
    """
    proof_state = {}
    scope_level = 0
    scope_path = [None] * 100

    line_parser = re.compile(
        r'^\s*(?P<line_num>\d+)\s+(?P<formula>.+?)\s{2,}(?P<justification>.+?)\s*$'
    )

    for line_text in proof_lines:
        line_text = line_text.rstrip()
        if not line_text.strip(): continue

        if 'BeginScope' in line_text:
            scope_level += 1
            continue
        if 'EndScope' in line_text:
            scope_level -= 1
            scope_path[scope_level + 1] = None
            continue

        match = line_parser.match(line_text)
        if not match: continue
            
        parts = match.groupdict()
        line_num = int(parts['line_num'])
        formula_str = parts['formula'].strip()
        justification_str = parts['justification'].strip()
        
        if not validate_characters(formula_str) or not check_balanced_parentheses(formula_str):
            print(f"Invalid Deduction at Line {line_num}")
            return
        tokens = tokenize(formula_str)
        current_tree = parseTree(tokens)
        if not current_tree:
            print(f"Invalid Deduction at Line {line_num}")
            return
        
        rule_parts = [p.strip() for p in justification_str.split(',')]
        rule_name = rule_parts[0]

        is_valid_step = False
        
        def is_accessible(premise_line_num: int) -> bool:
            if premise_line_num not in proof_state: return False
            premise_scope_level = proof_state[premise_line_num]['scope_level']
            return premise_scope_level <= scope_level

        try:
            if rule_name in ['Premise', 'Assumption']:
                is_valid_step = True
                if rule_name == 'Assumption':
                    scope_path[scope_level] = line_num
            
            elif rule_name == 'Copy':
                premise_line = int(rule_parts[1])
                if is_accessible(premise_line):
                    if are_trees_structurally_equivalent(current_tree, proof_state[premise_line]['tree']):
                        is_valid_step = True
            
            elif rule_name == '∧i':
                p1_line, p2_line = int(rule_parts[1]), int(rule_parts[2])
                if is_accessible(p1_line) and is_accessible(p2_line):
                    p1_tree = proof_state[p1_line]['tree']
                    p2_tree = proof_state[p2_line]['tree']
                    if current_tree.value == '∧' and \
                        are_trees_structurally_equivalent(current_tree.left, p1_tree) and \
                        are_trees_structurally_equivalent(current_tree.right, p2_tree):
                        is_valid_step = True

            elif rule_name == '∧e1':
                p_line = int(rule_parts[1])
                if is_accessible(p_line):
                    p_tree = proof_state[p_line]['tree']
                    if p_tree.value == '∧' and are_trees_structurally_equivalent(current_tree, p_tree.left):
                        is_valid_step = True

            elif rule_name == '∧e2':
                p_line = int(rule_parts[1])
                if is_accessible(p_line):
                    p_tree = proof_state[p_line]['tree']
                    if p_tree.value == '∧' and are_trees_structurally_equivalent(current_tree, p_tree.right):
                        is_valid_step = True
            
            elif rule_name == '∨i1':
                p_line = int(rule_parts[1])
                if is_accessible(p_line):
                    p_tree = proof_state[p_line]['tree']
                    if current_tree.value == '∨' and are_trees_structurally_equivalent(current_tree.left, p_tree):
                        is_valid_step = True

            elif rule_name == '∨i2':
                p_line = int(rule_parts[1])
                if is_accessible(p_line):
                    p_tree = proof_state[p_line]['tree']
                    if current_tree.value == '∨' and are_trees_structurally_equivalent(current_tree.right, p_tree):
                        is_valid_step = True

            elif rule_name == '→e': # Modus Ponens
                ref1_line, ref2_line = int(rule_parts[1]), int(rule_parts[2])
                if is_accessible(ref1_line) and is_accessible(ref2_line):
                    ref1_tree = proof_state[ref1_line]['tree']
                    ref2_tree = proof_state[ref2_line]['tree']
                    # Symmetrical check: allows for (A→B, A) or (A, A→B)
                    # Case 1: First reference is the implication
                    if ref1_tree.value == '→' and \
                        are_trees_structurally_equivalent(ref1_tree.left, ref2_tree) and \
                        are_trees_structurally_equivalent(current_tree, ref1_tree.right):
                        is_valid_step = True
                    # Case 2: Second reference is the implication
                    elif ref2_tree.value == '→' and \
                        are_trees_structurally_equivalent(ref2_tree.left, ref1_tree) and \
                        are_trees_structurally_equivalent(current_tree, ref2_tree.right):
                        is_valid_step = True

            elif rule_name == '→i':
                start_line, end_line = map(int, rule_parts[1].split('-'))
                assumption = proof_state.get(start_line)
                conclusion = proof_state.get(end_line)
                if assumption and conclusion and assumption['is_assumption'] and \
                    assumption['scope_level'] == scope_level + 1 and conclusion['scope_level'] == scope_level + 1:
                    if current_tree.value == '→' and \
                        are_trees_structurally_equivalent(current_tree.left, assumption['tree']) and \
                        are_trees_structurally_equivalent(current_tree.right, conclusion['tree']):
                        is_valid_step = True
            
            elif rule_name == '¬e':
                p1_line, p2_line = int(rule_parts[1]), int(rule_parts[2])
                if is_accessible(p1_line) and is_accessible(p2_line):
                    p1_tree = proof_state[p1_line]['tree']
                    p2_tree = proof_state[p2_line]['tree']
                    is_contradiction = (p1_tree.value == '¬' and are_trees_structurally_equivalent(p1_tree.left, p2_tree)) or \
                                        (p2_tree.value == '¬' and are_trees_structurally_equivalent(p2_tree.left, p1_tree))
                    if is_contradiction and current_tree.value == '⊥':
                        is_valid_step = True

            elif rule_name == '⊥e':
                p_line = int(rule_parts[1])
                if is_accessible(p_line) and proof_state[p_line]['tree'].value == '⊥':
                    is_valid_step = True

            elif rule_name == '¬¬e':
                p_line = int(rule_parts[1])
                if is_accessible(p_line):
                    p_tree = proof_state[p_line]['tree']
                    if p_tree.value == '¬' and p_tree.left and p_tree.left.value == '¬' and \
                        are_trees_structurally_equivalent(current_tree, p_tree.left.left):
                        is_valid_step = True
            
            elif rule_name == 'MT':
                imp_line, neg_con_line = int(rule_parts[1]), int(rule_parts[2])
                if is_accessible(imp_line) and is_accessible(neg_con_line):
                    imp_tree = proof_state[imp_line]['tree']
                    neg_con_tree = proof_state[neg_con_line]['tree']
                    if current_tree.value == '¬' and imp_tree.value == '→' and \
                        neg_con_tree.value == '¬' and \
                        are_trees_structurally_equivalent(imp_tree.right, neg_con_tree.left) and \
                        are_trees_structurally_equivalent(current_tree.left, imp_tree.left):
                        is_valid_step = True
            
            elif rule_name == '∨e':
                disj_line, scope1, scope2 = rule_parts[1], rule_parts[2], rule_parts[3]
                s1_start, s1_end = map(int, scope1.split('-'))
                s2_start, s2_end = map(int, scope2.split('-'))

                # New check: Ensure subproof scopes do not overlap.
                if max(s1_start, s2_start) <= min(s1_end, s2_end):
                    is_valid_step = False # Overlapping scopes are invalid for ∨e.
                elif is_accessible(int(disj_line)):
                    disj_tree = proof_state[int(disj_line)]['tree']
                    assum1, concl1 = proof_state.get(s1_start), proof_state.get(s1_end)
                    assum2, concl2 = proof_state.get(s2_start), proof_state.get(s2_end)

                    if disj_tree.value == '∨' and assum1 and concl1 and assum2 and concl2 and \
                        assum1['is_assumption'] and assum2['is_assumption'] and \
                        assum1['scope_level'] == scope_level + 1 and concl1['scope_level'] == scope_level + 1 and \
                        assum2['scope_level'] == scope_level + 1 and concl2['scope_level'] == scope_level + 1:
                        if are_trees_structurally_equivalent(disj_tree.left, assum1['tree']) and \
                            are_trees_structurally_equivalent(disj_tree.right, assum2['tree']) and \
                            are_trees_structurally_equivalent(concl1['tree'], concl2['tree']) and \
                            are_trees_structurally_equivalent(current_tree, concl1['tree']):
                            is_valid_step = True

                    if disj_tree.value == '∨' and assum1 and concl1 and assum2 and concl2 and \
                        assum1['is_assumption'] and assum2['is_assumption'] and \
                        assum1['scope_level'] == scope_level + 1 and concl1['scope_level'] == scope_level + 1 and \
                        assum2['scope_level'] == scope_level + 1 and concl2['scope_level'] == scope_level + 1:
                        if are_trees_structurally_equivalent(disj_tree.left, assum1['tree']) and \
                            are_trees_structurally_equivalent(disj_tree.right, assum2['tree']) and \
                            are_trees_structurally_equivalent(concl1['tree'], concl2['tree']) and \
                            are_trees_structurally_equivalent(current_tree, concl1['tree']):
                            is_valid_step = True
            
            elif rule_name == '¬i':
                start_line, end_line = map(int, rule_parts[1].split('-'))
                assumption, conclusion = proof_state.get(start_line), proof_state.get(end_line)
                if assumption and conclusion and assumption['is_assumption'] and \
                    conclusion['tree'].value == '⊥' and \
                    assumption['scope_level'] == scope_level + 1 and conclusion['scope_level'] == scope_level + 1:
                    if current_tree.value == '¬' and are_trees_structurally_equivalent(current_tree.left, assumption['tree']):
                        is_valid_step = True

            elif rule_name == '¬¬i':
                p_line = int(rule_parts[1])
                if is_accessible(p_line):
                    p_tree = proof_state[p_line]['tree']
                    if current_tree.value == '¬' and current_tree.left and current_tree.left.value == '¬' and \
                        are_trees_structurally_equivalent(current_tree.left.left, p_tree):
                        is_valid_step = True

            elif rule_name == 'PBC':
                start_line, end_line = map(int, rule_parts[1].split('-'))
                assumption, conclusion = proof_state.get(start_line), proof_state.get(end_line)
                if assumption and conclusion and assumption['is_assumption'] and \
                    conclusion['tree'].value == '⊥' and \
                    assumption['scope_level'] == scope_level + 1 and conclusion['scope_level'] == scope_level + 1:
                    if assumption['tree'].value == '¬' and are_trees_structurally_equivalent(assumption['tree'].left, current_tree):
                        is_valid_step = True
            
            elif rule_name == 'LEM': 
                is_valid_lem = False
                # Case 1: A ∨ ¬A
                if current_tree.value == '∨' and current_tree.right and current_tree.right.value == '¬':
                    if are_trees_structurally_equivalent(current_tree.left, current_tree.right.left):
                        is_valid_lem = True
                # Case 2: ¬A ∨ A
                elif current_tree.value == '∨' and current_tree.left and current_tree.left.value == '¬':
                    if are_trees_structurally_equivalent(current_tree.left.left, current_tree.right):
                        is_valid_lem = True
                
                if is_valid_lem:
                    is_valid_step = True

        except (ValueError, IndexError, AttributeError, TypeError, KeyError):
            is_valid_step = False

        if not is_valid_step:
            print(f"Invalid Deduction at Line {line_num}")
            return
            
        proof_state[line_num] = {
            'tree': current_tree, 
            'scope_level': scope_level,
            'is_assumption': rule_name == 'Assumption',
        }

    print("Valid Deduction")


# --- Main execution block ---
def main():
    """
    Reads a proof from 'proof.txt' and validates it.
    The file is expected to be in the same directory as the script.
    """
    # Get the directory where the script itself is located
    script_directory = os.path.dirname(os.path.abspath(__file__))
    # Join that directory path with the filename to create an absolute path
    filename = os.path.join(script_directory, "proof.txt")

    try:
        with open(filename, 'r', encoding='utf-8') as f:
            input_lines = f.readlines()
        validate_natural_deduction_proof(input_lines)
    except FileNotFoundError:
        print(f"Error: The file '{filename}' was not found.")
        print("Please ensure 'proof.txt' is in the same folder as your Python script.")

if __name__ == "__main__":
    main()
    