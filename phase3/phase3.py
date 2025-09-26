import re
import os  # Import os to build the file path

# Define special symbols for True and False.
TOP = '⊤'
BOTTOM = '⊥'

def tokenize_horn(formula: str):
    """Converts a Horn formula string into a list of tokens."""
    # This regex finds all valid symbols for our Horn formula syntax.
    tokens = re.findall(r'[a-z]|¬|⊤|⊥|→|∧|\(|\)', formula)
    return tokens

class HornParser:
    """
    A parser for Horn formulas.
    It validates that the formula is a conjunction of valid Horn clauses.
    """
    def __init__(self, tokens: list):
        self.tokens = tokens
        self.pos = 0

    def current_token(self):
        """Returns the current token without consuming it."""
        return self.tokens[self.pos] if self.pos < len(self.tokens) else None

    def advance(self):
        """Consumes the current token and moves to the next one."""
        self.pos += 1
    
    def expect(self, expected_token: str):
        """Consumes the current token if it matches the expected one, otherwise returns None."""
        if self.current_token() == expected_token:
            self.advance()
            return True
        return None

    def parse_premise(self):
        """Parses the premise of a Horn clause (left side of →)."""
        if self.current_token() == TOP:
            self.advance()
            return set() # An empty set represents TOP

        premise_vars = set()
        # Expect an atom
        token = self.current_token()
        if not token or not token.isalpha():
            return None # Premise must start with an atom or TOP
        premise_vars.add(token)
        self.advance()

        # Continue parsing if there are more atoms joined by conjunction
        while self.current_token() == '∧':
            self.advance()
            token = self.current_token()
            if not token or not token.isalpha():
                return None # Must be an atom after '∧'
            premise_vars.add(token)
            self.advance()

        return premise_vars

    def parse_clause(self):
        """Parses a single Horn clause: premise → conclusion."""
        premise = self.parse_premise()
        if premise is None:
            return None

        if not self.expect('→'):
            return None

        # Parse conclusion (must be a single atom or BOTTOM)
        conclusion = self.current_token()
        if not conclusion or (conclusion != BOTTOM and not conclusion.isalpha()):
            return None
        self.advance()
        
        return (premise, conclusion)

    def parse(self):
        """
        Public method to start parsing the entire formula.

        Returns a list of clauses or None if the formula is invalid.
        """
        if not self.tokens:
            return [] # An empty formula is valid and satisfiable
            
        clauses = []
        # Case 1: Formula is a conjunction of parenthesized clauses
        if self.current_token() == '(':
            while True:
                if not self.expect('('): return None
                clause = self.parse_clause()
                if clause is None: return None
                if not self.expect(')'): return None
                
                clauses.append(clause)

                if self.current_token() == '∧':
                    self.advance()
                else:
                    break # End of formula
        # Case 2: Formula is a single clause without parentheses
        else:
            clause = self.parse_clause()
            if clause is None: return None
            clauses.append(clause)
        
        # If parsing succeeded but there are still tokens left, the formula is malformed.
        if self.current_token() is not None:
            return None
            
        return clauses

def solve_horn_sat(formula_str: str) -> str:
    """
    Determines the satisfiability of a Horn formula using the new parser style.

    Args:
        formula_str: A string representing the Horn formula.

    Returns:
        A string indicating the result.
    """
    tokens = tokenize_horn(formula_str)
    parser = HornParser(tokens)
    clauses = parser.parse()

    if clauses is None:
        return "Invalid Horn Formula"

    # --- Horn-SAT Marking Algorithm ---
    marked_vars = set()
    
    while True:
        num_marked_before = len(marked_vars)

        for premise, conclusion in clauses:
            if premise.issubset(marked_vars):
                if conclusion != BOTTOM and conclusion not in marked_vars:
                    marked_vars.add(conclusion)
        
        num_marked_after = len(marked_vars)

        if num_marked_before == num_marked_after:
            break

    # Check for contradictions
    for premise, conclusion in clauses:
        if conclusion == BOTTOM and premise.issubset(marked_vars):
            return "Unsatisfiable"

    # If no contradiction, the formula is satisfiable
    if not marked_vars:
        return "Satisfiable"
    else:
        true_vars_str = " ".join(sorted(list(marked_vars)))
        return f"Satisfiable {true_vars_str}"

# --- Main Execution Block ---
def main():
    """
    Reads formulas from 'horn_tests.txt' and solves them.
    The file is expected to be in the same directory as the script.
    """
    # Get the directory where the script itself is located
    script_directory = os.path.dirname(os.path.abspath(__file__))
    # Join that directory path with the filename to create an absolute path
    filename = os.path.join(script_directory, "horn_tests.txt")

    try:
        with open(filename, 'r', encoding='utf-8') as f:
            for i, line in enumerate(f, 1):
                formula = line.strip()
                if formula:
                    result = solve_horn_sat(formula)
                    print(f"Formula {i}: {formula}")
                    print(f"Result:   {result}\n")
    except FileNotFoundError:
        print(f"Error: The file '{filename}' was not found.")
        print("Please ensure 'horn_tests.txt' is in the same folder as your Python script.")

if __name__ == '__main__':
    main()