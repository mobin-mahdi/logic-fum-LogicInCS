import re

# Node class for the Abstract Syntax Tree (AST)
class Node:
    def __init__(self, value, left=None, right=None):
        self.value = value
        self.left = left
        self.right = right

# Tokenizer function
def tokenize(formula):
    #Converts a formula string into a list of tokens.
    formula = formula.replace(' ', '')
    #regex finds all valid symbols. Invalid symbols are simply ignored,
    # and the parser will fail on the resulting malformed token sequence.
    tokens = re.findall(r'[a-z]|¬|∧|∨|→|\(|\)', formula)
    return tokens

# The Parser class implements a recursive descent parser with operator precedence.
class Parser:
    def __init__(self, tokens):
        self.tokens = tokens
        self.pos = 0

    def current_token(self):
        if self.pos < len(self.tokens):
            return self.tokens[self.pos]
        else:
            return None

    def advance(self):
        self.pos += 1

    def parse(self):
        #Public method to start parsing.
        if not self.tokens:
            return None
        node = self.parse_implication()
        # If parsing succeeded but there are still tokens left, the formula is malformed.
        if self.current_token() is not None:
            return None
        return node

    def parse_factor(self):
        #Parses atoms, negations, and parenthesized expressions (highest precedence).
        token = self.current_token()
        if token is None:
            return None
        if token.isalpha() and token.islower():
            self.advance()
            return Node(token)
        if token == '¬':
            self.advance()
            operand = self.parse_factor()
            if operand is None: return None
            return Node('¬', operand)
        if token == '(':
            self.advance()
            node = self.parse_implication()
            if self.current_token() != ')':
                return None
            self.advance()
            return node
        return None

    def parse_term(self):
        #Parses conjunction (∧) and disjunction (∨) (medium precedence, left-associative).
        node = self.parse_factor()

        if node is None: return None
        
        while self.current_token() in ['∧', '∨']:
            op = self.current_token()
            self.advance()
            right_node = self.parse_factor()

            if right_node is None: return None

            node = Node(op, node, right_node)
        return node

    def parse_implication(self):
        #Parses implication (→) (lowest precedence, right-associative).
        node = self.parse_term()

        if node is None: return None

        if self.current_token() in ['→']:
            op = self.current_token()
            self.advance()
            right_node = self.parse_implication()

            if right_node is None: return None

            node = Node(op, node, right_node)
        return node

# Helper to visualize the AST
def print_tree(node, indent=0):
    if not node:
        return
    print('  ' * indent + node.value)
    print_tree(node.left, indent + 1)
    print_tree(node.right, indent + 1)

# Main function to check if a formula is a well-formed formula (WFF).
def is_wff(formula):
    """
    Checks if a formula is well-formed by tokenizing and parsing it.
    It relies on the parser to detect any structural or syntactical errors.
    """
    print(f"Input: \"{formula}\"")
    
    tokens = tokenize(formula)
    parser = Parser(tokens)
    tree = parser.parse()
    
    # If the parser successfully builds a tree and consumes all tokens, the formula is valid.
    # The parser returns None for any error (e.g., "p q", "p ∧", "(p ∧ q", "p # q").
    if tree:
        print("Result: Valid Formula")
        print("--- AST ---")
        print_tree(tree)
        print("-" * 11 + "\n")
    else:
        print("Result: Invalid Formula\n")

# --- Main execution block ---
def main():
    """
    Reads formulas from 'test_cases.txt' and checks if they are WFFs.
    """

    filename = "test_cases.txt"
    try:
        with open(filename, 'r', encoding='utf-8') as f:
            for line in f:
                formula = line.strip()  # Remove leading/trailing whitespace
                if formula:  # Process only non-empty lines
                    is_wff(formula)
    except FileNotFoundError:
        print(f"\nError: The file '{filename}' was not found in the directory above.")
        print("Please check the path and the solutions below.")

# This ensures the main() function is called when the script is run
if __name__ == "__main__":
    main()