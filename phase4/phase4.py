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
    node, final_pos = _parse_formula_recursive(tokens)
    if node and final_pos == len(tokens):
        return node
    return None

def _parse_formula_recursive(tokens):
    if not tokens:
        return None, 0

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

        left_node, left_consumed = _parse_formula_recursive(left_tokens)
        right_node, right_consumed = _parse_formula_recursive(right_tokens)

        if (left_node and left_consumed == len(left_tokens)) and \
            (right_node and right_consumed == len(right_tokens)):
            return Node(op, left_node, right_node), len(tokens)
        
    return None, 0


#  Natural Deduction Rule

def are_trees_structurally_equivalent(node1, node2):
    """
    Checks if two parse trees are structurally equivalent.
    """
    if node1 is None and node2 is None:
        return True
    if node1 is None or node2 is None:
        return False
    
    if node1.value != node2.value:
        return False
    
    return (are_trees_structurally_equivalent(node1.left, node2.left) and
            are_trees_structurally_equivalent(node1.right, node2.right))

def tree_to_formula_string(node, is_outermost_binary=True):
    """
    Converts a parse tree node back to its string representation.
    """
    if node is None:
        return ""

    # Handles atomic propositions
    if node.value.isalpha() and node.value.islower() or node.value == '⊥':
        return node.value

    # Handles negation '¬'
    if node.value == '¬':
        child_str = tree_to_formula_string(node.left, is_outermost_binary=False)
        # Only add parentheses if the child is a negation or needs disambiguation
        if node.left.value == '¬':
            return f"¬({child_str})"
        return f"¬{child_str}"

    # Handles binary operators '∧', '∨', '→'
    if node.value in ['∧', '∨', '→']:
        left_str = tree_to_formula_string(node.left, is_outermost_binary=False)
        right_str = tree_to_formula_string(node.right, is_outermost_binary=False)

        # parenthesis
        if is_outermost_binary:
            return f"{left_str} {node.value} {right_str}"
        else:
            return f"({left_str} {node.value} {right_str})"
    
    return node.value

def run_natural_deduction_rule(input_lines):

    formulas = {}
    rule_line_found = False
    rule_line = ""

    #  Parse formulas section
    for line in input_lines:
        line = line.strip()
        if not line:
            continue
        
        match = re.match(r'^\s*(\d+)\s{4}(.+)$', line)
        if match:
            line_num = int(match.group(1))
            formula_str = match.group(2).strip()

            # Directly tokenize and parse, skipping validation checks
            tokens = tokenize(formula_str)
            tree = parseTree(tokens)
            formulas[line_num] = tree
        else:
            rule_line = line
            rule_line_found = True
            break

    if not rule_line_found:
        print("Rule Cannot Be Applied")
        return

    #  Parse and apply the rule 
    try:
        rule_parts = rule_line.split(',')
        rule_name = rule_parts[0].strip()
        line_numbers_for_rule = [int(n.strip()) for n in rule_parts[1:]]
    except (ValueError, IndexError):
        print("Rule Cannot Be Applied")
        return

    for ln in line_numbers_for_rule:
        if ln not in formulas:
            print("Rule Cannot Be Applied")
            return

    result_node = None

    # Apply the specified Natural Deduction Rule
    
    if rule_name == '∧i':
        if len(line_numbers_for_rule) != 2:
            print("Rule Cannot Be Applied")
            return
        premise1 = formulas[line_numbers_for_rule[0]]
        premise2 = formulas[line_numbers_for_rule[1]]
        result_node = Node('∧', premise1, premise2)
    
    elif rule_name == '∧e1':
        if len(line_numbers_for_rule) != 1:
            print("Rule Cannot Be Applied")
            return
        premise = formulas[line_numbers_for_rule[0]]
        if premise and premise.value == '∧':
            result_node = premise.left
        else:
            print("Rule Cannot Be Applied")
            return

    elif rule_name == '∧e2':
        if len(line_numbers_for_rule) != 1:
            print("Rule Cannot Be Applied")
            return
        premise = formulas[line_numbers_for_rule[0]]
        if premise and premise.value == '∧':
            result_node = premise.right
        else:
            print("Rule Cannot Be Applied")
            return

    elif rule_name == '→e':
        if len(line_numbers_for_rule) != 2:
            print("Rule Cannot Be Applied")
            return
            
        # Use general names: premise1 and premise2
        premise1 = formulas[line_numbers_for_rule[0]]
        premise2 = formulas[line_numbers_for_rule[1]]

        # Scenario 1: premise1 is the implication (A -> B) and premise2 is the antecedent (A)
        if (premise1 and premise1.value == '→' and
            are_trees_structurally_equivalent(premise1.left, premise2)):
            result_node = premise1.right
            
        # Scenario 2: premise2 is the implication (A -> B) and premise1 is the antecedent (A)
        elif (premise2 and premise2.value == '→' and
            are_trees_structurally_equivalent(premise2.left, premise1)):
            result_node = premise2.right
            
        else:
            print("Rule Cannot Be Applied")
            return
    elif rule_name == '¬e':
        if len(line_numbers_for_rule) != 2:
            print("Rule Cannot Be Applied")
            return
        premise1 = formulas[line_numbers_for_rule[0]]
        premise2 = formulas[line_numbers_for_rule[1]]

        if (premise2 and premise2.value == '¬' and are_trees_structurally_equivalent(premise1, premise2.left)) or \
            (premise1 and premise1.value == '¬' and are_trees_structurally_equivalent(premise2, premise1.left)):
            result_node = Node('⊥')
        else:
            print("Rule Cannot Be Applied")
            return

    elif rule_name == '¬¬e':
        if len(line_numbers_for_rule) != 1:
            print("Rule Cannot Be Applied")
            return
        premise = formulas[line_numbers_for_rule[0]]
        if premise and premise.value == '¬' and premise.left and premise.left.value == '¬':
            result_node = premise.left.left
        else:
            print("Rule Cannot Be Applied")
            return

    elif rule_name == 'MT':
        if len(line_numbers_for_rule) != 2:
            print("Rule Cannot Be Applied")
            return
        implication_premise = formulas[line_numbers_for_rule[0]]
        negated_consequent_premise = formulas[line_numbers_for_rule[1]]

        if (implication_premise and implication_premise.value == '→' and
            negated_consequent_premise and negated_consequent_premise.value == '¬' and
            are_trees_structurally_equivalent(implication_premise.right, negated_consequent_premise.left)):
            result_node = Node('¬', implication_premise.left)
        else:
            print("Rule Cannot Be Applied")
            return

    elif rule_name == '¬¬i':
        if len(line_numbers_for_rule) != 1:
            print("Rule Cannot Be Applied")
            return
        premise = formulas[line_numbers_for_rule[0]]
        result_node = Node('¬', Node('¬', premise))
    
    else:
        print("Rule Cannot Be Applied")
        return

    # Print the result
    if result_node:
        print(tree_to_formula_string(result_node, is_outermost_binary=True))
    else:
        print("Rule Cannot Be Applied")

def main():
    """
    Reads natural deduction rule applications from 'nd_tests.txt',
    processes them, and prints the result. Test cases in the file
    should be separated by blank lines.
    """
    # Get the directory where the script itself is located
    script_directory = os.path.dirname(os.path.abspath(__file__))
    filename = os.path.join(script_directory, "nd_tests.txt")

    try:
        with open(filename, 'r', encoding='utf-8') as f:
            content = f.read()
        
        # Split the content into test cases based on one or more empty lines
        test_cases = re.split(r'\n\s*\n', content)
        
        print("--- Running Natural Deduction Tests from File ---")
        for i, test_case_str in enumerate(test_cases, 1):
            if not test_case_str.strip():
                continue
            
            print(f"\n--- Test Case {i} ---")
            input_lines = test_case_str.strip().split('\n')
            
            # Print the input for clarity
            for line in input_lines:
                print(line)
            print("Output:")
            
            run_natural_deduction_rule(input_lines)

    except FileNotFoundError:
        print(f"Error: The file '{filename}' was not found.")
        print("Please ensure 'nd_tests.txt' is in the same folder as your Python script.")

if __name__ == "__main__":
    main()