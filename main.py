# Converter from CFG to CNF(Chomsky Normal Form)

# --------------by Yash Agarwal(E19CSE156) - EB10
# ----------------& Vibhu Upmanyu(E19CSE298) - EB10

ARROW = "->"
OR = "|"
EMPTY = "e"
END_CHAR = "$"
START_VAR_CHAR = "S"


class Rule:
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs


class CYK:
    def __init__(self, rules):
        self.rules = rules
        self.matrix = []

    def run(self):
        input_string = input().replace(" ", "")
        while input_string != END_CHAR:
            self.make_matrix(input_string)
            print("True" if self.start_var_in_last_cell() else "False")
            self.print_matrix()
            input_string = input().replace(" ", "")

    def start_var_in_last_cell(self):
        return START_VAR_CHAR in self.matrix[0][-1]

    def make_matrix(self, string):
        matrix_len = len(string)
        matrix = [[set() for k in range(matrix_len)] for j in range(matrix_len)]
        for i in range(matrix_len):
            matrix[i][i] = self.find_vars_of_product([string[i]])

        for j in range(matrix_len):
            for i in range(j, -1, -1):
                matching_vars = set()
                for counter in range(1, j-i+1):
                    left = j - counter
                    down = (j-i+1) - counter + i
                    # self.matrix = matrix
                    # self.print_matrix()
                    # print(i, left, "|", down, j)
                    for product_1 in matrix[i][left]:
                        for product_2 in matrix[down][j]:
                            concat_vars = [product_1, product_2]
                            matching_vars.update(self.find_vars_of_product(concat_vars))
                matrix[i][j].update(matching_vars)
        self.matrix = matrix

    def find_vars_of_product(self, product):
        matching_vars = set()
        for rule in self.rules:
            for prod in rule.rhs:
                # print("--->" , prod, product)
                if prod == product:
                    matching_vars.add(rule.lhs)
        return matching_vars

    def print_matrix(self):
        for x in self.matrix:
            print(x)


class CNF:
    def __init__(self):
        self.rules = list()
        self.was_in_cnf = True

    def was_in_cnf(self):
        return self.was_in_cnf

    def add_rule(self, lhs, rhs):
        self.rules.append(Rule(lhs, rhs))

    def print_rules(self):
        for rule in self.rules:
            print(rule.lhs + " -> ", end='')
            print(rule.rhs)

    def get_rules(self):
        return self.rules

    @staticmethod
    def make_var_style(counter):
        return "(V" + counter + ")"

    def reduce_vars_to_2(self):
        var_counter = 0
        new_vars = list()
        there_was_change = True
        while there_was_change:
            there_was_change = False
            for rule in self.rules:
                for product in rule.rhs:
                    if len(product) > 2:
                        there_was_change = True
                        self.was_in_cnf = False
                        first_var = product[0]
                        second_var = product[1]
                        product.pop(0)
                        product.pop(0)
                        new_var_product = [first_var,second_var]
                        if new_var_product in new_vars:
                            new_var_name = self.make_var_style(str(new_vars.index(new_var_product)))
                        else:
                            new_var_name = self.make_var_style(str(var_counter))
                            new_vars.append(new_var_product)
                            var_counter += 1
                        product.insert(0, new_var_name)

        for var_char in new_vars:
            new_var_name = self.make_var_style(str(new_vars.index(var_char)))
            self.add_rule(new_var_name, [var_char])

    @staticmethod
    def make_terminal_style(counter):
        return "(T" + counter + ")"

    def make_vars_for_terminals(self):
        var_counter = 0
        new_vars = list()
        for rule in self.rules:
            for product in rule.rhs:
                for i, var_char in enumerate(product):
                    if len(product) > 1 and var_char.islower():
                        self.was_in_cnf = False
                        if var_char in new_vars:
                            new_var_name = self.make_terminal_style(str(new_vars.index(var_char)))
                        else:
                            new_var_name = self.make_terminal_style(str(var_counter))
                            new_vars.append(var_char)
                            var_counter += 1
                        product[i] = var_char.replace(var_char, new_var_name)

        for terminal_char in new_vars:
            new_var_name = self.make_terminal_style(str(new_vars.index(terminal_char)))
            self.add_rule(new_var_name, [[terminal_char]])


class CFG:
    def __init__(self):
        self.rules = set()
        self.nullables = set()
        self.vars_dependency_graph = dict()
        self.generative_vars = set()
        self.reachable_vars = set()

        self.cnf = CNF()
        self.CNF_var_counter = 0

    def add_rule(self, lhs, rhs):
        self.rules.add(Rule(lhs, rhs))

    def input_rules(self):
        self.rules = set()
        input_string = input().replace(" ", "")
        while input_string != END_CHAR:
            var, rule = list(input_string.split(ARROW))
            var_rules = set(rule.split(OR))
            self.add_rule(var, var_rules)
            input_string = input().replace(" ", "")

    def print_rules(self):
        for rule in self.rules:
            print(rule.lhs + " -> ", end='')
            first_for = True
            for product in rule.rhs:
                if not first_for:
                    print(" | ", end="")
                first_for = False

                if isinstance(product, str):
                    print(product, end='')
                else:
                    print("".join(product), end='')


            print()

    def print_cnf(self):
        self.cnf.print_rules()

    
    def find_nullables(self):
        self.nullables = set()
        old_set_size = -1
        while len(self.nullables) != old_set_size:
            old_set_size = len(self.nullables)
            for rule in self.rules:
                if EMPTY in rule.rhs:  
                    self.nullables.add(rule.lhs)
                    rule.rhs.remove(EMPTY)
                    continue

                for product in rule.rhs: 
                    is_nullable = True
                    for var in product:
                        if var not in self.nullables:
                            is_nullable = False
                    if is_nullable:
                        self.nullables.add(rule.lhs)

    def remove_e(self):
        self.find_nullables()
        for nullable_var in self.nullables:
            for rule in self.rules:
                set_old_size = 0
                while len(rule.rhs) != set_old_size:  
                    set_old_size = len(rule.rhs)
                    for product in rule.rhs.copy():
                        for var_char in product:
                            if var_char == nullable_var:
                                s = product.replace(var_char, "", 1)
                                if s != "":
                                    rule.rhs.add(s)


    def make_vars_dependency_graph(self):
        self.vars_dependency_graph = dict()
        for rule in self.rules:
            self.vars_dependency_graph[rule.lhs] = set()
            for product in rule.rhs:
                for var_char in product:
                    if var_char.isupper():
                        self.vars_dependency_graph[rule.lhs].add(var_char)
                        

    def is_unit_product(self, s):
        return len(s) == 1 and s.isupper()

    def get_non_unit_products(self, var_char):
        non_unit_products = set()
        for rule in self.rules:
            if rule.lhs == var_char:
                for product in rule.rhs:
                    if not self.is_unit_product(product):
                        non_unit_products.add(product)
        return non_unit_products

    def get_replace_for_unit_product(self, var_char, visited):
        replacing_products = set()
        if var_char in visited:
            return replacing_products
        visited.append(var_char)

        if var_char not in self.vars_dependency_graph:
            self.remove_products_with_var(var_char)
        else:
            for var in self.vars_dependency_graph[var_char]:
                if var != var_char:
                    replacing_products.update(self.get_non_unit_products(var))
                    replacing_products.update(self.get_replace_for_unit_product(var, visited)) 

        return replacing_products

    def remove_unit_productions(self):
        self.make_vars_dependency_graph()
        for rule in self.rules:
            for product in rule.rhs.copy():
                if self.is_unit_product(product):
                    rule.rhs.update(self.get_replace_for_unit_product(product, []))
                    rule.rhs.remove(product)

    def remove_products_with_var(self, var_char):
        for rule in self.rules:
            for product in rule.rhs.copy():
                if var_char in product:
                    rule.rhs.remove(product)

    def make_generative_vars(self):
        generative_vars = set()
        old_set_size = -1
        while old_set_size != len(generative_vars):
            old_set_size = len(generative_vars)
            for rule in self.rules:
                for product in rule.rhs:
                    is_generative = (len(product) > 0)
                    for var_char in product:
                        if var_char.isupper() and var_char not in generative_vars:
                            is_generative = False
                    if is_generative:
                        generative_vars.add(rule.lhs)
        self.generative_vars = generative_vars

    def remove_non_generatives(self):
        self.make_generative_vars()
        for rule in self.rules.copy():
            if rule.lhs not in self.generative_vars:
                self.remove_products_with_var(rule.lhs)
                self.rules.remove(rule)
            else:
                if len(rule.rhs) == 0:
                    self.rules.remove(rule)

    def make_reachable_vars(self, start_var, visited):
        if start_var in visited:
            return
        visited.append(start_var)
        self.reachable_vars.add(start_var)
        if start_var not in self.vars_dependency_graph: 
            self.remove_products_with_var(start_var)
        else:
            for to_var in self.vars_dependency_graph[start_var]:
                self.make_reachable_vars(to_var, visited)

    def remove_not_reachables(self):
        self.make_vars_dependency_graph()
        self.make_reachable_vars(START_VAR_CHAR, [])
        for rule in self.rules.copy():
            if rule.lhs not in self.reachable_vars:
                self.remove_products_with_var(rule.lhs)
                self.rules.remove(rule)

    # CONVERT TO CHOMSKY NORMAL FORM-----------------------------------------
    def separate_products_make_cnf(self):
        self.CNF_var_counter = 0
        new_vars = list()
        for rule in self.rules:
            new_products = list() 
            for product in rule.rhs:
                new_product = list()  
                for var_char in product:
                    new_product.append(var_char)
                new_products.append(new_product)

            self.cnf.add_rule(rule.lhs, new_products)

    def convert_to_CNF(self):
        self.separate_products_make_cnf()  
        self.cnf.make_vars_for_terminals()
        self.cnf.reduce_vars_to_2()
        self.rules = self.cnf.get_rules()

    def was_in_cnf(self):
        return self.cnf.was_in_cnf

cfg = CFG()
cfg.input_rules()
cfg.remove_e()
cfg.remove_unit_productions()
cfg.remove_non_generatives()
cfg.remove_not_reachables()
print("Converted to Chomsky Normal Form")
cfg.convert_to_CNF()
cfg.print_rules()

# Code by - Yash Agarwal and Vibhu Upmanyu [Bennett University]
