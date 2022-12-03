import copy
import time
#import logging
#from amr_agent import AMR_Agent
# Logger set up
#logger = logging.getLogger()
#logger.setLevel(logging.DEBUG)
#console_handler = logging.StreamHandler()
#console_handler.setLevel(logging.INFO)
#logger.addHandler(console_handler)
#AMR16 = AMR_Agent(16)
#AMR16.connect()
#AMR16.run_forever()



class Agent:
    def __init__(self, name, belief_base, goals):
        self.name = name
        self.belief_base = belief_base
        self.goals = goals
        self.sent_messages = []
        self.received_messages = []
        self.desired_next_state = []


keywords = ["forall", "exists", "not", "and", "implies", "or", "pre", "post", "a-goal", "=", "bel",
            "goal", "True", "False", "send:", "send!", "send?", "sent:", "sent!", "sent?", "adopt", "drop", "insert",
            "delete", "allother",
            "all", "insert"]
symbols = ["(", ")", ".", ",", "[", "]", "|"]


# Retrieve all information from the predicate, the input predicate is contained in a string,
# the output of all information of the predicate are stored in a standard form.
def predicate_information(predicate, constants):
    information = {"name": "", "list_contain": "", "values_in_list": [[], []], "values_in_non_list": [],
                   "variables": []}
    i = 0
    flag = 0
    empty = True
    evaluated = False
    name = ""
    nested = False
    while i < len(predicate):
        if flag == 0 and predicate[i] != '(':
            information["name"] = information["name"] + predicate[i]
        elif flag == 0 and predicate[i] == '(':
            flag = 1
        elif flag == 1 and predicate[i] == '[':
            information["list_contain"] = True
            flag = 2
        elif flag == 1 and predicate[i] != '[':
            information["list_contain"] = False
            name = name + predicate[i]
            flag = 3
        # Store list value in two sublist, need one more flag to store if the second list is empty.
        elif flag == 2 and empty:
            if predicate[i] != ',' and predicate[i] != '|' and predicate[i] != ']':
                name = name + predicate[i]
            elif predicate[i] == '|':
                empty = False
                information["values_in_list"][0].append(name)
                if name not in constants:
                    information["variables"].append(name)
                name = ""
            else:
                information["values_in_list"][0].append(name)
                if name not in constants:
                    information["variables"].append(name)
                name = ""
        elif flag == 2 and not empty:
            if not nested and not evaluated:
                evaluated = True
                if predicate[i] != '[':
                    nested = True
            if not nested:
                if predicate[i] != ',' and predicate[i] != '[' and predicate[i] != ']':
                    name = name + predicate[i]
                elif predicate[i] == ',' or predicate[i] == ']':
                    if name != "":
                        information["values_in_list"][1].append(name)
                        if name not in constants:
                            information["variables"].append(name)
                        name = ""
            elif evaluated and nested:
                if predicate[i] != ']':
                    name = name + predicate[i]
                else:
                    information["values_in_list"][1] = name
                    information["variables"].append(name)
        elif flag == 3:
            if predicate[i] != ',' and predicate[i] != ')':
                name = name + predicate[i]
            elif predicate[i] == ',' or predicate[i] == ')':
                if name != "":
                    information["values_in_non_list"].append(name)
                    if name not in constants:
                        information["variables"].append(name)
                    name = ""
        i = i + 1
    return information


# Process a rule of the inputs
def input_process(rule, constants):
    standard_form = []
    for predicate in rule:
        if predicate in keywords:
            standard_form.append(predicate)
        else:
            standard_form.append(predicate_information(predicate, constants))
    return standard_form


# Process a belief base
def process_bliefs(beliefs, constants):
    processed = []
    for i in beliefs:
        processed.append(predicate_information(i, constants))
    return processed


# Process a goal base
def process_belief_list(belief_list, constants):
    processed = []
    for i in belief_list:
        processed.append(process_bliefs(i, constants))
    return processed


# Transform a predicate to a readble form
def transform_to_normalform(predicate_information):
    predicate = predicate_information['name']
    if predicate_information['values_in_list'] == [[], []] and predicate_information['values_in_non_list'] == [] and \
            predicate_information["variables"] == []:
        return predicate
    if predicate_information['list_contain']:
        predicate = predicate + "(["
        pr = predicate_information['values_in_list'][0]
        i = 0
        while i < len(pr):
            predicate = predicate + pr[i]
            if i < len(pr) - 1:
                predicate = predicate + ','
            else:
                predicate = predicate + '])'
            i = i + 1
    else:
        predicate = predicate + "("
        pr = predicate_information['values_in_non_list']
        i = 0
        while i < len(pr):
            predicate = predicate + pr[i]
            if i < len(pr) - 1:
                predicate = predicate + ','
            else:
                predicate = predicate + ')'
            i = i + 1
    return predicate


# Transform a state list to the readable form
def state_normal_representation(state):
    normal = []
    for item in state:
        normal.append(transform_to_normalform(item))
    return normal


# Transform a rule to the readable form
def rule_normal_representation(rule, constants):
    normal = ""
    for item in rule:
        if type(item) == type(True):
            item = str(item)
        if item in keywords or item in constants:
            normal = normal + str(item) + " "
        else:
            normal = normal + transform_to_normalform(item) + " "
    return normal


# Transform a state list to the readable form
def state_list_normal_representation(states):
    reformed = []
    for state in states:
        reformed.append(state_normal_representation(state))
    return reformed


# Transform a system state to the readable form
def system_state_normal_representation(system_state):
    reformed = {}
    for key in system_state:
        B = system_state[key][0]
        G = system_state[key][1]
        B2 = state_normal_representation(B)
        G2 = state_list_normal_representation(G)
        reformed.update({key: (B2, G2)})
    return reformed


# Transform multiple system state to the readable form
def transform_multi_states_normal(multi_state):
    reformed = []
    for key in multi_state:
        B = state_normal_representation(multi_state[key][0])
        G = state_list_normal_representation(multi_state[key][1])
        D = {key: (B, G)}
        reformed.append(D)
    return reformed


# Transform a mental state to the readable form.
def transform_mental_states_normal(mental_state):
    B = state_normal_representation(mental_state[0])
    G = state_list_normal_representation(mental_state[1])
    return (B, G)


# Test if a system state is a final state
def test_final_state(state):
    for key in state:
        for key2 in state[key]:
            if state[key][key2][1] != []:
                return False
    return True


# Find the all occurrence positions of the keyword in the list, return a list either contain all occurrence of the keyword in the list.
def find_position_in_list(L, keyword):
    i = 0
    store = []
    while i < len(L):
        if L[i] == keyword:
            store.append(i)
        i = i + 1
    return store


# Evaluate if the given variable occurs at the both side of the implication rule
def variable_implication_both_side(rule, var):
    left = False
    right = False
    for predicate in rule[0:find_position_in_list(rule, "implies")[0]]:
        if predicate not in keywords:
            if var in predicate["variables"]:
                left = True
    for predicate in rule[find_position_in_list(rule, "implies")[0] + 1:]:
        if predicate not in keywords:
            if var in predicate["variables"]:
                right = True
    return left and right


# Remove single universal variables only occuring at the one side of implication
def instantiate_universal_variable_implication_single(rule, var, domain):
    previous_symbol_not = False
    instantiated_rule = []
    not_add = False
    for predicate in rule:
        if predicate not in keywords:
            if var in predicate["variables"]:
                for value in domain:
                    if previous_symbol_not and not_add:
                        instantiated_rule.append("not")
                    predicate_copy = copy.deepcopy(predicate)
                    if predicate_copy["list_contain"]:
                        i = 0
                        while i < len(predicate_copy["values_in_list"][0]):
                            if predicate_copy["values_in_list"][0][i] == var:
                                predicate_copy["values_in_list"][0][i] = value
                                predicate_copy["variables"].remove(var)
                            i = i + 1
                    else:
                        i = 0
                        while i < len(predicate_copy["values_in_non_list"]):
                            if predicate_copy["values_in_non_list"][i] == var:
                                predicate_copy["values_in_non_list"][i] = value
                                predicate_copy["variables"].remove(var)
                            i = i + 1
                    instantiated_rule.append(predicate_copy)
                    instantiated_rule.append("and")
                    not_add = True
            else:
                instantiated_rule.append(predicate)
            if instantiated_rule[-1] == "and":
                instantiated_rule = instantiated_rule[:-1]
            previous_symbol_not = False
        else:
            instantiated_rule.append(predicate)
            if predicate == "not":
                previous_symbol_not = True
            else:
                previous_symbol_not = False
    return instantiated_rule


# Remove all universal variables and remove all quantified parts.
def universal_variable_instantiation(L, domain, constants):
    universal_vars = []
    positions = find_position_in_list(L, 'in')
    var_domain = {}
    for pos in positions:
        var_domain.update({L[pos - 1][-1]: L[pos + 1]})
    if positions != []:
        new_L = []
        i = 0
        while i < len(positions):
            if i == 0:
                new_L = new_L + L[0:positions[i]]
                S = new_L[-1]
                S = S + L[positions[i] + 2]
                new_L[-1] = S
            else:
                new_L = new_L + L[positions[i - 1] + 3:positions[i]]
                S = new_L[-1] + L[positions[i] + 2]
                new_L[-1] = S
            i = i + 1
        new_L = new_L + L[positions[-1] + 3:]
        L = new_L
    if L[0] == "forall":
        for i in L[1]:
            if i != "," and i != ".":
                universal_vars.append(i)
        L = L[2:]
    if L[0] == "exists":
        L = L[2:]
    universal_var_single = []
    universal_var_both = []
    rule = input_process(L, constants)
    for var in universal_vars:
        if variable_implication_both_side(rule, var):
            universal_var_both.append(var)
        else:
            universal_var_single.append(var)
    rules = []
    rules_copy = [copy.deepcopy(rule)]

    if universal_var_single != []:
        for new_rule in rules_copy:
            temp = new_rule
            for var in universal_var_single:
                temp = instantiate_universal_variable_implication_single(temp, var, domain[var_domain[var]])
            rules.append(temp)

        rules = [x for x in rules if x not in rules_copy]
    if universal_var_single == []:
        rules.append(rule)
    return rules


# Separate rules into fully instatiated rules and partial instantiated rules
def separate_rules(L, domain, constants):
    universal_instantiated_rules = []
    for rule in L:
        processed_rules = universal_variable_instantiation(rule, domain, constants)
        processed_rules_copy = copy.deepcopy(processed_rules)
        for i in processed_rules_copy:
            universal_instantiated_rules.append(i)
    fully_instantiated_rules = []
    partial_instantiated_rules = []
    for rule in universal_instantiated_rules:
        fully_instantiated = True
        r = 0
        while r < len(rule) and fully_instantiated:
            if rule[r] not in keywords:
                if rule[r]["variables"] != []:
                    fully_instantiated = False
            r = r + 1
        if fully_instantiated:
            fully_instantiated_rules.append(rule)
        partial_instantiated_rules = [x for x in universal_instantiated_rules if x not in fully_instantiated_rules]
    return (fully_instantiated_rules, partial_instantiated_rules)


# Extract all predicates' name of a rule
def predicate_in_rules(rule):
    predicate_names = []
    for predicate in rule:
        if predicate not in keywords:
            if predicate["name"] not in predicate_names:
                predicate_names.append(predicate["name"])
    return predicate_names


# Return the position of a predicate occuring in the rule: use to evaluate if a predicate
# occurs both of the implication.
def predicate_position_implies(predicate_name, rule):
    i = 0
    place = "Unknown"
    while i < len(rule) and place != "right":
        if rule[i] not in keywords:
            if rule[i]["name"] == predicate_name:
                if 'implies' in rule[i + 1:]:
                    place = "Left"
                elif 'implies' in rule[:i] and place != "Left":
                    place = "Right"
                elif 'implies' in rule[:i]:
                    place = "Both"
        i = i + 1
    return place


# For a set of predicates and rules, return a pair containing the position information of each predicate
def predicates_position_in_rules(predicates, rules):
    predicates_position = []
    for i in predicates:
        j = 0
        flag = True
        position = "Unknown"
        while j < len(rules) and flag:
            if position == "Unknown":
                position = predicate_position_implies(i, rules[j])
            elif position == "Left":
                if predicate_position_implies(i, rules[j]) == "Right" or predicate_position_implies(i,
                                                                                                    rules[j]) == "Both":
                    position = "Both"
                    flag = False
            elif position == "Right":
                if predicate_position_implies(i, rules[j]) == "Left" or predicate_position_implies(i,
                                                                                                   rules[j]) == "Both":
                    position = "Both"
                    flag = False
            j = j + 1
        predicates_position.append((i, position))
    return predicates_position


# In a rule, evaluate if all predicates occuring at the leftside belong to the give predicates set.
# This function is usually used to evaluates if the rule should be instantiated at first.
# If all predicates occuring at the leftside only occur at the leftside of all processed rules, then we process the rule at first.
def predicate_in_left_rule(predicates, rule):
    answer = True
    i = 0
    pos = find_position_in_list(rule, 'implies')[0]
    existing_predicates = predicate_in_rules(rule[0:pos])
    while i < len(existing_predicates) and answer:
        if existing_predicates[i] not in predicates:
            answer = False
        i = i + 1
    return answer


# Find suitable substitution
def predicate_existential_variables_instantiation(atoms, predicate, constants):
    substitution = []
    sub_temp = []
    atoms = [atom for atom in atoms if atom["name"] == predicate["name"]]
    if not predicate["list_contain"]:
        predicate_copy = copy.deepcopy(predicate)
        for atom in atoms:
            flag = True
            for var in predicate["variables"]:
                i = 0
                while i < len(predicate_copy["values_in_non_list"]) and flag:
                    if predicate_copy["values_in_non_list"][i] in constants:
                        if atom["values_in_non_list"][i] != predicate_copy["values_in_non_list"][i]:
                            flag = False
                    else:
                        if predicate_copy["values_in_non_list"][i] == var:
                            predicate_copy["values_in_non_list"][i] = atom["values_in_non_list"][i]
                            sub_temp.append((var, atom["values_in_non_list"][i]))
                    i = i + 1
            if sub_temp != []:
                substitution.append(sub_temp)
                sub_temp = []
            predicate_copy = copy.deepcopy(predicate)
    else:
        predicate_copy = copy.deepcopy(predicate)
        for atom in atoms:
            flag = True
            if predicate_copy["values_in_list"][1] == [] and len(predicate_copy["values_in_list"][0]) == len(
                    atom["values_in_list"][0]):
                for var in predicate["variables"]:
                    i = 0
                    while i < len(predicate_copy["values_in_list"][0]) and flag:
                        if predicate_copy["values_in_list"][0][i] in constants:
                            if atom["values_in_list"][0][i] != predicate_copy["values_in_list"][0][i]:
                                flag = False
                        else:
                            if predicate_copy["values_in_list"][0][i] == var:
                                predicate_copy["values_in_list"][0][i] = atom["values_in_list"][0][i]
                                sub_temp.append((var, atom["values_in_list"][0][i]))
                        i = i + 1
                if sub_temp != []:
                    substitution.append(sub_temp)
                    sub_temp = []
                predicate_copy = copy.deepcopy(predicate)
            else:
                if len(predicate_copy["values_in_list"][0]) <= len(atom["values_in_list"][0]) and \
                        predicate_copy["values_in_list"][1] != []:
                    subtract = len(predicate_copy["values_in_list"][0]) - len(atom["values_in_list"][0])
                    list_var = predicate_copy["values_in_list"][1]
                    if len(predicate_copy["values_in_list"][0]) == len(atom["values_in_list"][0]):
                        sub_temp.append((list_var, []))
                    else:
                        second_list = atom["values_in_list"][0][subtract:]
                        sub_temp.append((list_var, second_list))

                    for var in predicate["variables"]:
                        i = 0
                        while i < len(predicate_copy["values_in_list"][0]) and flag:
                            if predicate_copy["values_in_list"][0][i] in constants:
                                if atom["values_in_list"][0][i] != predicate_copy["values_in_list"][0][i]:
                                    flag = False
                            else:
                                if predicate_copy["values_in_list"][0][i] == var:
                                    predicate_copy["values_in_list"][0][i] = atom["values_in_list"][0][i]
                                    sub_temp.append((var, atom["values_in_list"][0][i]))
                            i = i + 1
                    if flag:
                        predicate_copy["variables"].remove(list_var)
                        if sub_temp != []:
                            substitution.append(sub_temp)

                    predicate_copy = copy.deepcopy(predicate)
                    sub_temp = []
    return substitution


# Substitute a predicate with a substitution list.
def substitute_predicate(predicate, substitution):
    for sub in substitution:
        if sub[0] in predicate["variables"]:
            if predicate["list_contain"]:
                if predicate["values_in_list"][1] == sub[0]:
                    predicate["values_in_list"][1] = sub[1]
                    if sub[1] != []:
                        predicate["values_in_list"][0].extend(sub[1])
                        predicate["values_in_list"][1] = []
                else:
                    count = 0
                    while count < len(predicate["values_in_list"][0]):
                        if predicate["values_in_list"][0][count] == sub[0]:
                            predicate["values_in_list"][0][count] = sub[1]
                        count = count + 1
            else:
                count = 0
                while count < len(predicate["values_in_non_list"]):
                    if predicate["values_in_non_list"][count] == sub[0]:
                        predicate["values_in_non_list"][count] = sub[1]
                    count = count + 1
            predicate["variables"].remove(sub[0])
    return predicate


# instantiate the rule contianing variables to fully instantiated rules
def existential_variable_rule_instantiation(existential_rule, atoms, constants):
    instantiated_rule = []
    instantiated_rule.append(existential_rule)
    i = 0
    while i < len(instantiated_rule):
        rule = copy.deepcopy(instantiated_rule[i])
        rule_copy = copy.deepcopy(rule)
        count = 0
        flag = True
        temp = []
        while count < len(rule) and flag:
            predicate = rule[count]
            if predicate not in keywords:
                if predicate["variables"] != []:
                    substitution = predicate_existential_variables_instantiation(atoms, predicate, constants)
                    if substitution != []:
                        flag = False
                        for sub in substitution:
                            rule_store = copy.deepcopy(rule)
                            temp = rule_store[:count]
                            for predicate in rule_store[count:]:
                                if predicate not in keywords:
                                    predicate_update = substitute_predicate(predicate, sub)
                                    temp.append(predicate_update)
                                else:
                                    temp.append(predicate)
                            instantiated_rule.append(temp)
                        instantiated_rule = [x for x in instantiated_rule if x != rule_copy]
                else:
                    temp.append(predicate)
            else:
                temp.append(predicate)
            count = count + 1
        if flag:
            i = i + 1
    return instantiated_rule


# Match the clause of the leftside of a rule with the atoms.
# If it can be matched with a atom, replace it with True, otherwise, replace it with False.
def pattern_mactch_at_left_rule(rule, atoms):
    pos = find_position_in_list(rule, 'implies')[0]
    i = 0
    flag = True
    while i < pos and flag:
        if rule[i] not in keywords:
            if rule[i] in atoms or rule[i] == True:
                rule[i] = True
                if i > 0 and rule[i - 1] == 'not':
                    flag = False
            else:
                rule[i] = False
                if i > 0 and rule[i - 1] != 'not':
                    flag = False
        i = i + 1
    return rule


# If all clause at the leftside of a rule are substitute with Boolean values, we can derive the atoms based on the rule.
# Due to closed world assumption, only True derives atoms.
def derivation_at_right_rule(rule):
    generated_atoms = []
    flag = True
    i = 0
    pos = find_position_in_list(rule, 'implies')[0]
    while i < pos and flag:
        if rule[i] not in keywords:
            if rule[i] != True and (i == 0 or rule[i - 1] != 'not'):
                flag = False
            elif rule[i] == True and (i > 0 and rule[i - 1] == 'not'):
                flag = False
        i = i + 1
    if flag:
        generated_atoms = rule[pos + 1:]
        # generated_atoms = [x for x in generated_atoms if x not in keywords]
    return generated_atoms


# Derive all atoms given a set of atoms, a set of fully instantiated rules, and a set of partial instantiated rules.
def atoms_derivation(atoms, fully_instantiated, partial_instantiated, constants):
    # If there is no more rules, then the atom generation process ends, return all atoms.
    if fully_instantiated == [] and partial_instantiated == []:
        return atoms
    # If there are at least one rule to be evaluate, start the derivation process
    else:
        predicates = []
        # Store all predicates occuring in all rules
        for rule in fully_instantiated + partial_instantiated:
            predicates = predicates + predicate_in_rules(rule)
        predicates = list(set(predicates))
        # Store the predicates only occuring at the leftside of rules
        predicates_at_left = []
        for i in predicates_position_in_rules(predicates, partial_instantiated + fully_instantiated):
            if i[1] == 'Left':
                predicates_at_left.append(i[0])
        # Store all rules which will be processed in the next step
        to_be_match = []
        signal = True
        initial = True
        while signal:
            if initial:
                for rule in partial_instantiated + fully_instantiated:
                    if predicate_in_left_rule(predicates_at_left, rule):
                        to_be_match.append(rule)
                partial_instantiated = [x for x in partial_instantiated if x not in to_be_match]
                fully_instantiated = [x for x in fully_instantiated if x not in to_be_match]
                initial = False
            else:
                to_be_match = partial_instantiated + fully_instantiated
            expand_rule = []
            for rule in to_be_match:
                if rule in fully_instantiated:
                    expand_rule.append(rule)
                else:
                    expand_rule = expand_rule + existential_variable_rule_instantiation(rule, atoms, constants)
            to_be_match = [x for x in expand_rule if x[-1] not in atoms]
            used = []
            interpreted = []
            for rule in to_be_match:
                interpreted.append(pattern_mactch_at_left_rule(rule, atoms))
            for i in interpreted:
                if derivation_at_right_rule(i) != []:
                    if derivation_at_right_rule(i) not in atoms:
                        used.append(i)
                        atoms = atoms + derivation_at_right_rule(i)
            if used == []:
                signal = False
            to_be_match = partial_instantiated + fully_instantiated

    return atoms


# Derive all properties given a belief base, a knowledge base, and a domain.
def state_property_generation(belief_base, knowledge_base, domain, constants):
    rules = []
    for i in knowledge_base:
        rules.append(i.split())
    for i in rules:
        if len(i) == 1:
            belief_base = belief_base + i
    rules = [x for x in rules if x[0] not in belief_base]
    M = separate_rules(rules, domain, constants)
    fully_instantiated = M[0]
    partial_instantiated = M[1]
    atoms_current = []
    for i in belief_base:
        if type(i) == type("1"):
            atoms_current.append(predicate_information(i, constants))
        else:
            atoms_current.append(i)
    atoms = atoms_derivation(atoms_current, fully_instantiated, partial_instantiated, constants)
    return atoms


# Instantiate a rule with a set of substitutions.
def rule_partial_instantiation(rule, substitutions):
    instantiated_rules = []
    for sub in substitutions:
        r = copy.deepcopy(rule)
        instantiated_rule = []
        for predicate in r:
            if predicate in keywords:
                instantiated_rule.append(predicate)
            else:
                instantiated_rule.append(substitute_predicate(predicate, sub))
        instantiated_rules.append(instantiated_rule)
    return instantiated_rules


def action_constraints_analysis(action_constraints, atoms_current_state, atoms_goal_state, domain, constants):
    enabled_condition = []
    constraints = []
    All_Act_Cons_Name = []
    for constraint in action_constraints:
        constraints.append(constraint.split())
    expand_constraints = separate_rules(constraints, domain, constants)
    instantiated_constrains = []
    for i in expand_constraints:
        for j in i:
            instantiated_constrains.append(j)
    current_state_rep = state_normal_representation(atoms_current_state)
    goal_rep = state_normal_representation(atoms_goal_state)
    for constraint in instantiated_constrains:
        act_cons = constraint[-1]
        if act_cons['name'] not in All_Act_Cons_Name:
            All_Act_Cons_Name.append(act_cons['name'])
        a_goal_predicate = []
        if 'a-goal' in constraint:
            pos = find_position_in_list(constraint, 'a-goal')[0]
            a_goal_predicate.append(constraint[pos + 1])
            substitution = predicate_existential_variables_instantiation(atoms_goal_state, a_goal_predicate[0],
                                                                         constants)
            partial_instantiated = rule_partial_instantiation(constraint, substitution)
            fully_instantiated = []
            for rule in partial_instantiated:
                fully_instantiated = fully_instantiated + existential_variable_rule_instantiation(rule,
                                                                                                  atoms_current_state,
                                                                                                  constants)
            for rule in fully_instantiated:
                pos = find_position_in_list(rule, 'a-goal')[0]
                if rule[pos + 1] not in atoms_current_state and rule[pos + 1] in atoms_goal_state:
                    new_rule = [True]
                    i = 0
                    while i < len(rule):
                        if i != pos and i != pos + 1:
                            new_rule.append(rule[i])

                        i = i + 1

                    # store=copy.deepcopy(new_rule)
                    new_rule = pattern_mactch_at_left_rule(new_rule, atoms_current_state)

                    enabled = derivation_at_right_rule(new_rule)
                    if enabled != []:
                        enabled_condition.append(enabled)
        else:
            fully_instantiated = existential_variable_rule_instantiation(constraint, atoms_current_state, constants)
            for rule in fully_instantiated:
                new_rule = pattern_mactch_at_left_rule(rule, atoms_current_state)
                enabled = derivation_at_right_rule(new_rule)
                if enabled != []:
                    enabled_condition.append(enabled)
    return (enabled_condition, All_Act_Cons_Name)


def action_enableness_analysis(action_enableness, atom_current_state, action_constraints, domain, All_Act_Cons_Name,
                               constants):
    Act_Cons_Name = []
    for i in action_constraints:
        Act_Cons_Name.append(i['name'])
    Act_Cons_Name = list(set(Act_Cons_Name))

    atom_current_state_rep = state_normal_representation(atom_current_state)
    enabled_actions = []
    enableness_rule = []
    for enableness in action_enableness:
        enableness_rule.append(enableness.split())
    expand_constraints = separate_rules(enableness_rule, domain, constants)
    instantiated_constrains = []
    for i in expand_constraints:
        for j in i:
            instantiated_constrains.append(j)
    final_constraints = []
    for rule in instantiated_constrains:
        pos1 = find_position_in_list(rule, 'implies')[0]
        pos2 = find_position_in_list(rule, 'not')
        negative_predicates = []
        conclusion = rule[pos1 + 1]
        for pos in pos2:
            negative_predicates.append(rule[pos + 1])
        current_action_constraint = []
        flag_Act_Cons = True
        for predicate in rule[0:pos1]:
            if predicate not in keywords:
                if predicate["name"] in Act_Cons_Name:
                    current_action_constraint = predicate
                    break
                if predicate["name"] in All_Act_Cons_Name:
                    flag_Act_Cons = False
        if flag_Act_Cons:
            final_constraints.append(rule)
        if current_action_constraint != []:
            positive_predicates = [x for x in rule[0:pos1] if
                                   x not in negative_predicates and x != current_action_constraint and x not in keywords]
            operation_rule = []
            for predicate in positive_predicates:
                operation_rule.append(predicate)
                operation_rule.append("and")
            if negative_predicates != []:
                for predicate in negative_predicates:
                    operation_rule.append("not")
                    operation_rule.append(predicate)
                    operation_rule.append("and")
            operation_rule = operation_rule[:-1]
            operation_rule.append("implies")
            operation_rule.append(conclusion)
            if current_action_constraint in action_constraints:
                instanitated_rule = existential_variable_rule_instantiation(operation_rule, atom_current_state,
                                                                            constants)
                for rule in instanitated_rule:
                    new_rule = pattern_mactch_at_left_rule(rule, atom_current_state)
                    if derivation_at_right_rule(new_rule) != []:
                        enabled_actions = enabled_actions + derivation_at_right_rule(new_rule)
            else:
                substitution = predicate_existential_variables_instantiation(action_constraints,
                                                                             current_action_constraint, constants)
                if substitution != []:
                    new_operation_rules = []
                    for sub in substitution:
                        operation_rule_copy = copy.deepcopy(operation_rule)
                        new_rule = []
                        for predicate in operation_rule_copy:
                            if predicate not in keywords:
                                new_rule.append(substitute_predicate(predicate, sub))
                            else:
                                new_rule.append(predicate)
                        new_operation_rules.append(new_rule)
                    instanitated_rule = []
                    for rule in new_operation_rules:
                        instanitated_rule.extend(
                            existential_variable_rule_instantiation(rule, atom_current_state, constants))
                        for rule in instanitated_rule:
                            new_rule = pattern_mactch_at_left_rule(rule, atom_current_state)
                            new_action = derivation_at_right_rule(new_rule)
                            if new_action != []:
                                if new_action[0] not in enabled_actions:
                                    enabled_actions = enabled_actions + new_action
    if enabled_actions == []:
        for rule in final_constraints:
            instanitated_rule = existential_variable_rule_instantiation(rule, atom_current_state, constants)
            for rule in instanitated_rule:
                new_rule = pattern_mactch_at_left_rule(rule, atom_current_state)
                en_Act = derivation_at_right_rule(new_rule)
                if en_Act != []:
                    if en_Act[0] not in enabled_actions:
                        enabled_actions = enabled_actions + en_Act
    return enabled_actions


def communication_analysis(current_agent, all_agents, sent_message_update, action_constraints, domain,
                            constants):
    sent_messages = []
    enableness_rule = []
    for enableness in sent_message_update:
        enableness_rule.append(enableness.split())
    expand_constraints = separate_rules(enableness_rule, domain, constants)
    instantiated_constrains = []
    for i in expand_constraints:
        for j in i:
            instantiated_constrains.append(j)

    if action_constraints != []:
        for constraint_copy in instantiated_constrains:
            constraint = copy.deepcopy(constraint_copy)
            Cons=existential_variable_rule_instantiation(constraint, action_constraints, constants)
            for cons in Cons:
                new_cons = pattern_mactch_at_left_rule(cons, action_constraints)
                new_cons_rep = rule_normal_representation(new_cons, constants)
                generated_info = derivation_at_right_rule(new_cons)
                generated_info_rep = rule_normal_representation(generated_info, constants)
                if generated_info != []:
                    message_type = generated_info[0]['name']
                    agent_info = generated_info[0]['values_in_non_list'][0]
                    received_agents = []
                    if agent_info == 'all':
                        received_agents = all_agents
                    elif agent_info == 'allother':
                        received_agents = copy.deepcopy(all_agents)
                        received_agents.remove(current_agent)
                        received_agents.remove('D')
                    else:
                        received_agents = [agent_info]
                    message_content = generated_info[1]
                    sent_messages.append((message_type, received_agents, message_content))
    return sent_messages


def event_analysis(received_messages, event_processing, atoms_current_state, atoms_goal_state, domain, constants):
    event_updates = {"add_beliefs": [], "delete_beliefs": [], "add_goals": [], "delete_goals": [], "sent_messages": []}
    enableness_rule = []
    atoms_current_state_copy = copy.deepcopy(atoms_current_state)
    atoms_goal_state_copy = copy.deepcopy(atoms_goal_state)
    for enableness in event_processing:
        enableness_rule.append(enableness.split())
    expand_constraints = separate_rules(enableness_rule, domain, constants)
    instantiated_constrains = []
    for i in expand_constraints:
        for j in i:
            instantiated_constrains.append(j)
    communication_processing = []
    non_communication_processing = []
    non_communication_processing_current = []
    communication_keywords = ["send:", "send!", "send?", "sent:", "sent!", "sent?"]
    for constraint in instantiated_constrains:
        flag = True
        for item in constraint:
            if item not in keywords:
                if item['name'] in communication_keywords:
                    flag = False
                    break
        if flag:
            if 'a-goal' in constraint:
                non_communication_processing.append(constraint)
            else:
                non_communication_processing_current.append(constraint)
        else:
            communication_processing.append(constraint)
    current_state_rep = state_normal_representation(atoms_current_state_copy)
    goal_rep = state_normal_representation(atoms_goal_state_copy)
    # processed_received_messages=[]
    processed_received_first_messages = []
    processed_received_second_messages = []
    if received_messages != []:
        for m in received_messages:
            processed_received_first_messages.append(predicate_information(m[0], constants))
            processed_received_second_messages.append(m[1])
        for rule_copy in communication_processing:
            rule = copy.deepcopy(rule_copy)
            p1 = rule[0]
            p2 = rule[1]
            j = 0
            for msg in processed_received_first_messages:
                sub1 = predicate_existential_variables_instantiation([msg], p1, constants)
                sub2 = []
                flag=False
                if sub1 != []:
                    if p2['variables'] != []:
                        msg2 = processed_received_second_messages[j]
                        sub2 = predicate_existential_variables_instantiation([msg2], p2, constants)
                    #Change on 24 Nov.
                    elif p2['variables']==[] and p2['values_in_non_list']==['_']:
                        msg2 = processed_received_second_messages[j]
                        if msg2['values_in_non_list']!=['_']:
                            flag=True

                    if sub2 != []:
                        sub = [sub1[0] + sub2[0]]
                    else:
                        sub = sub1
                    if flag:
                        sub=[]
                    rule = copy.deepcopy(rule_copy)
                    partial_instantiated = rule_partial_instantiation(rule, sub)
                    fully_instantiated = []
                    for rule in partial_instantiated:
                        fully_instantiated = fully_instantiated + existential_variable_rule_instantiation(rule,
                                                                                                          atoms_current_state_copy,
                                                                                                          constants)
                    for rule in fully_instantiated:
                        if rule[0] in processed_received_first_messages and rule[
                            1] in processed_received_second_messages:
                            new_rule = [True]
                            i = 2
                            while i < len(rule):
                                new_rule.append(rule[i])
                                i = i + 1
                            new_rule = pattern_mactch_at_left_rule(new_rule, atoms_current_state_copy)
                            enabled = derivation_at_right_rule(new_rule)
                            if enabled != []:
                                if enabled[0] not in keywords:
                                    message_type = enabled[0]['name']
                                    received_agents = enabled[0]['values_in_non_list']
                                    msg = (message_type, received_agents, enabled[1])
                                    event_updates["sent_messages"].append(msg)
                                elif enabled[0] == "insert":
                                    if enabled[1] not in atoms_current_state_copy:
                                        event_updates["add_beliefs"].append(enabled[1])
                                        atoms_current_state_copy.append(enabled[1])
                                elif enabled[0] == "delete":
                                    if enabled[1] in atoms_current_state_copy:
                                        event_updates["delete_beliefs"].append(enabled[1])
                                        atoms_current_state_copy.remove(enabled[1])
                                elif enabled[0] == "adopt":
                                    if enabled[1] not in atoms_goal_state_copy and enabled[
                                        1] not in atoms_current_state_copy:
                                        event_updates["add_goals"].append(enabled[1])
                                        atoms_goal_state_copy.append(enabled[1])
                                elif enabled[0] == "drop":
                                    if enabled[1] in atoms_goal_state_copy and enabled[1] in atoms_current_state_copy:
                                        event_updates["delete_goals"].append(enabled[1])
                                        atoms_goal_state_copy.remove(enabled[1])
                j = j + 1
    for rule in non_communication_processing:
        a_goal_predicate = []
        pos = find_position_in_list(rule, 'a-goal')[0]
        a_goal_predicate.append(rule[pos + 1])
        substitution = predicate_existential_variables_instantiation(atoms_goal_state_copy, a_goal_predicate[0],
                                                                     constants)
        partial_instantiated = rule_partial_instantiation(rule, substitution)
        fully_instantiated = []
        for rule in partial_instantiated:
            fully_instantiated = fully_instantiated + existential_variable_rule_instantiation(rule,
                                                                                              atoms_current_state_copy,
                                                                                              constants)
        for rule in fully_instantiated:
            pos = find_position_in_list(rule, 'a-goal')[0]
            if rule[pos + 1] not in atoms_current_state_copy and rule[pos + 1] in atoms_goal_state_copy:
                new_rule = [True]
                i = 0
                while i < len(rule):
                    if i != pos and i != pos + 1:
                        new_rule.append(rule[i])
                    i = i + 1
                new_rule = pattern_mactch_at_left_rule(new_rule, atoms_current_state_copy)
                enabled = derivation_at_right_rule(new_rule)
                if enabled != []:
                    if enabled[0] == "insert":
                        if enabled[1] not in atoms_current_state_copy:
                            event_updates['add_beliefs'].append(enabled[1])
                            atoms_current_state_copy.append(enabled[1])
                    elif enabled[0] == "delete":
                        if enabled[1] in atoms_current_state_copy:
                            event_updates["delete_beliefs"].append(enabled[1])
                            atoms_current_state_copy.remove(enabled[1])
                    elif enabled[0] == "adopt":
                        if enabled[1] not in atoms_goal_state_copy and enabled[1] not in atoms_current_state_copy:
                            event_updates['add_goals'].append(enabled[1])
                            atoms_goal_state_copy.append(enabled[1])
                    elif enabled[0] == "drop":
                        if enabled[1] in atoms_goal_state_copy and enabled[1] in atoms_current_state_copy:
                            event_updates["delete_goals"].append(enabled[1])
                            atoms_goal_state_copy.remove(enabled[1])
    for rule in non_communication_processing_current:
        partial_instantiated = [rule]
        fully_instantiated = []
        for rule in partial_instantiated:
            fully_instantiated = fully_instantiated + existential_variable_rule_instantiation(rule,
                                                                                              atoms_current_state_copy,
                                                                                              constants)
        for rule in fully_instantiated:
            rule = pattern_mactch_at_left_rule(rule, atoms_current_state_copy)
            enabled = derivation_at_right_rule(rule)
            if enabled != []:
                if enabled[0] == "insert":
                    if enabled[1] not in atoms_current_state_copy:
                        event_updates['add_beliefs'].append(enabled[1])
                        atoms_current_state_copy.append(enabled[1])
                elif enabled[0] == "delete":
                    if enabled[1] in atoms_current_state_copy:
                        event_updates["delete_beliefs"].append(enabled[1])
                        atoms_current_state_copy.remove(enabled[1])
                elif enabled[0] == "adopt":
                    if enabled[1] not in atoms_goal_state_copy and enabled[1] not in atoms_current_state_copy:
                        event_updates['add_goals'].append(enabled[1])
                        atoms_goal_state_copy.append(enabled[1])
                elif enabled[0] == "drop":
                    if enabled[1] in atoms_goal_state_copy and enabled[1] in atoms_current_state_copy:
                        event_updates["delete_goals"].append(enabled[1])
                        atoms_goal_state_copy.remove(enabled[1])

    return event_updates


def state_transformer(enable_actions, current_state, knowledge_base, action_specification, domain, constants):
    current_beliefs = state_property_generation(current_state, knowledge_base, domain, constants)
    cur_bel_rep = state_normal_representation(current_beliefs)
    Act_Name = []
    for i in enable_actions:
        Act_Name.append(i['name'])
    Act_Name = list(set(Act_Name))
    effect = []
    for key in action_specification:
        if key in Act_Name:
            effect.append(action_specification[key].split())
    expand_constraints = separate_rules(effect, domain, constants)
    instantiated_constrains = []
    for i in expand_constraints:
        for j in i:
            instantiated_constrains.append(j)
    next_state_beliefs = []
    for rule in instantiated_constrains:
        new_beliefs = copy.deepcopy(current_state)
        pos = find_position_in_list(rule, 'implies')[0]
        remove_predicates = []
        add_predicates = []
        previous_not = False
        for predicate in rule[0:pos]:
            if predicate not in keywords:
                if predicate["name"] in list(action_specification.keys()):
                    current_enabled_action = predicate
                    break
        substitution = predicate_existential_variables_instantiation(enable_actions, current_enabled_action, constants)
        if substitution != []:
            rule = [x for x in rule if x != current_enabled_action]
            rule_copy = copy.deepcopy(rule)

            for sub in substitution:
                count = 0
                while count < len(rule):
                    if rule[count] not in keywords:
                        rule[count] = substitute_predicate(rule[count], sub)
                    count = count + 1
                instantiated_rules = existential_variable_rule_instantiation(rule, current_beliefs, constants)
                for rule2 in instantiated_rules:

                    remove_predicates_copy = copy.deepcopy(remove_predicates)
                    add_predicates_copy = copy.deepcopy(add_predicates)
                    pos = find_position_in_list(rule2, 'implies')[0]
                    for predicate in rule2[pos + 1:]:
                        if predicate not in keywords:
                            if previous_not:
                                remove_predicates_copy.append(predicate)
                            else:
                                add_predicates_copy.append(predicate)
                            previous_not = False
                        elif predicate == 'not':
                            previous_not = True
                        else:
                            previous_not = False
                    new_rule = pattern_mactch_at_left_rule(rule2, current_beliefs)
                    if derivation_at_right_rule(new_rule) != []:
                        for predicate in add_predicates_copy:
                            new_beliefs.append(predicate)
                        for predicate in remove_predicates_copy:
                            new_beliefs.remove(predicate)
                        next_state_beliefs.append(new_beliefs)
                    new_beliefs = copy.deepcopy(current_state)
                rule = copy.deepcopy(rule_copy)
    return next_state_beliefs


def equal_state(state1, state2):
    flag = 0
    for i in state1:
        for j in state2:
            if i == j:
                flag = flag + 1
    if flag == len(state1):
        return True
    else:
        return False


def equal_transition(transitions, transition):
    flag = True
    for tr in transitions:
        for key in tr:
            if tr[key] == transition:
                flag = False
                break
    return flag


def test_substate(state1, state2):
    if state1 == []:
        return False
    for i in state1:
        if i not in state2:
            return False
    return True


def equal_substate(state1, state2):
    flag = 0
    for i in state1:
        for j in state2:
            if i == j:
                flag = flag + 1
    if flag == len(state1) and flag == len(state2):
        return True
    else:
        return False


def equal_state(state1, state2):
    flag = True
    if state1.keys() == state2.keys():
        for key in state1:
            state1_beliefs = state1[key][0]
            state1_goals = state1[key][1]
            state2_beliefs = state2[key][0]
            state2_goals = state2[key][1]
            if not equal_substate(state1_beliefs, state2_beliefs) or state1_goals != state2_goals:
                flag = False
    return flag


def equal_transition(transitions, transition):
    flag = True
    for tr in transitions:
        for key in tr:
            if tr[key] == transition:
                flag = False
                break
    return flag


def empty_dict(D):
    for key in D:
        if D[key] != []:
            return False
    return True


def exists_state_property(agent, state, state_properties_dict):
    for key in state_properties_dict:
        if agent in state_properties_dict[key].keys():
            state1 = state_properties_dict[key][agent][0][0]
            state1_rep = state_normal_representation(state1)
            state2 = state[0]
            state2_rep = state_normal_representation(state2)
            if equal_substate(state1, state2):
                return key
        else:
            return None
    return None


def safety_checking(atoms_rep, safety):
    flag_safe = True
    for s in safety:
        if s not in atoms_rep:
            return False
    return flag_safe


def DM_generation(agents, knowledge_base, constraints_of_action_generation,
                  enableness_of_actions,  action_specification, sent_message_update,
                  event_processing, domain, constants, dummy_agents, safety, error_messages, prior_beliefs):
    active_agents = []
    remaining_goals = {}
    for agent in agents:
        name = agent.name
        if name not in dummy_agents:
            if agent.goals!=[]:
                active_agents.append(name)
                remaining_goals.update({name: agent.goals})
    current_state = {}
    current_state_rep = {}
    all_agents_name = []
    #common_beliefs_rep = copy.deepcopy(common_beliefs)
    # Add current state
    for agent in agents:
        all_agents_name.append(agent.name)
        if agent.name not in dummy_agents:
            agent.belief_base.extend(prior_beliefs)
        B = process_bliefs(agent.belief_base, constants)
        G = process_belief_list(agent.goals, constants)
        current_state.update({agent.name: (B, G)})
        normal_B = state_normal_representation(B)
        normal_G = state_list_normal_representation(G)
        current_state_rep.update({agent.name: (normal_B, normal_G)})

    count_goal = 0
    enabled_sent_messages_dict = {}
    goal_management = {}
    initial_count_goal = copy.deepcopy(count_goal)
    for agent in agents:
        desired_loop = len(agent.goals)
        goal_management.update({agent.name: (initial_count_goal, desired_loop)})
    enabled_action_dict = {}
    next_move_dict = {}
    substate_dict = {}
    substate_dict_rep = {}
    substate_goal_management = {}
    loop_count = 0
    adopted_goals_dict = {}
    adopted_goals_dict_rep = {}
    for agent in agents:
        substate_dict.update({agent.name: current_state[agent.name]})
        substate_dict_rep.update({agent.name: transform_mental_states_normal(current_state[agent.name])})

    # Error message checking
    error_info = error_message_processing(agents, error_messages)
    loop_max=6
    loop_count=0
    # Evaluate if the decision-making module already generated a feasible action for an agent
    non_termination = True
    change_beliefs = False
    print_goal_change=True
    while non_termination and loop_count<loop_max:
        last_enabled_sent_messages_dict=copy.deepcopy(enabled_sent_messages_dict)
        loop_count = loop_count + 1
        if loop_count>=2:
            MM=1
        # For non-dummy agents, adapt their goals to the currrent beleifs
        # Add the condition: if there is no error messgae in the current belief base. (To be discussed.)
        for agent in agents:
            name = agent.name
            dummy_flag = False
            if name in dummy_agents:
                dummy_flag = True
            if not dummy_flag:
                substate = substate_dict[name]
                current_belief_base = substate[0]
                current_belief_base_rep = state_normal_representation(current_belief_base)
                atom_current = state_property_generation(current_belief_base, knowledge_base, domain, constants)
                atom_current_rep = state_normal_representation(atom_current)

                # Achieved goal checking
                subgoal = substate[1]
                subgoal_rep = state_list_normal_representation(subgoal)
                if len(substate[1]) > 0:
                    current_focus = substate[1][0]
                else:
                    current_focus = substate[1]
                current_focus_copy = copy.deepcopy(current_focus)
                for goal in current_focus_copy:
                    if goal in atom_current:
                        subgoal[0].remove(goal)
                    if subgoal[0] != []:
                        substate_dict[name] = (substate_dict[name][0], subgoal)
                        substate_dict_rep[name] = transform_mental_states_normal(substate_dict[name])
                    elif len(subgoal) == 1:
                        substate_dict[name] = (substate_dict[name][0], [])
                        substate_dict_rep[name] = transform_mental_states_normal(substate_dict[name])
                        desired_loop = goal_management[name][1]
                        goal_management[name] = (desired_loop, desired_loop)
                    else:
                        substate_dict[name] = (substate_dict[name][0], subgoal[1:])
                        substate_dict_rep[name] = transform_mental_states_normal(substate_dict[name])
                        current_loop = goal_management[name][0]
                        desired_loop = goal_management[name][1]
                        goal_management[name] = (current_loop + 1, desired_loop)
                        agent.desired_next_state = []

            current_goal = goal_management[name][0]
            desired_goal = goal_management[name][1]
            substate_goal_management.update({name: (current_goal, desired_goal)})

        # Check if all non-dummy agents achieve their goals.
        goal_achieved = True
        for agent in agents:
            name = agent.name
            if name not in dummy_agents:
                if goal_management[name][0] != goal_management[name][1]:
                    goal_achieved = False
                    break

        # Generate safe decision-making
        active_flag_dict={}
        for agent in agents:
            enabled_sent_messages = []
            enabled_actions = []
            enabled_constrains=[]
            name = agent.name
            dummy_flag = False
            if name in dummy_agents:
                dummy_flag = True

            error_goal_change = False
            if error_info[name] != [] and error_info[name]!=['E4']:
                if agent.goals[0] == ["located(charging)", "at(5)"]:
                    error_goal_change = True
                    if print_goal_change:
                        print(name, "changes the goal due to the error information:", error_info[name][0],'.')
                        print_goal_change=False

                agent.belief_base=[x for x in agent.belief_base if x not in error_info[name]]
                B=process_bliefs(agent.belief_base,constants)
                G=substate_dict[name][1]
                substate_dict[name]=(B,G)


            # Control the number of enabled constraints(actions)
            flag_continue = True
            substate = substate_dict[name]
            current_belief_base = substate[0]
            current_belief_base_rep = state_normal_representation(current_belief_base)
            atom_current = state_property_generation(current_belief_base, knowledge_base, domain, constants)
            atom_current_rep = state_normal_representation(atom_current)
            current_goal = goal_management[name][0]
            desired_goal = goal_management[name][1]
            S1 = set(current_belief_base_rep)
            #Change
            if agent.desired_next_state!=[] and type(agent.desired_next_state)!=type({}):
                if type(agent.desired_next_state[0])==type(""):
                    S2 = set(agent.desired_next_state)
            #Change on 24.Nov
            elif agent.desired_next_state==[]:
                S2=set(agent.desired_next_state)
            else:
                S2=set(["False"])

            if error_info[name] == [] and not S2.issubset(S1) and agent.desired_next_state!=[] and not error_goal_change:
                active_flag = False
            else:
                active_flag=True
            active_flag_dict.update({name:active_flag})
            if current_goal == desired_goal and not dummy_flag:
                enabled_action_dict[name] = []
            elif current_goal < desired_goal and not dummy_flag and active_flag:
                substate_dict.update({name: substate})
                substate_dict_rep.update({name: transform_mental_states_normal(substate)})
                # Current focus is the MAS is focusing on.
                if len(substate[1]) > 0:
                    current_focus = substate[1][0]
                else:
                    current_focus = substate[1]
                atom_goal = state_property_generation(current_focus, knowledge_base, domain, constants)
                atom_goal_rep = state_normal_representation(atom_goal)
                # Error message checking
                # Generate safe decision-making, safe state checking
                if error_info[name] == ['E4'] and name in active_agents:
                    print(name, " crashed!")
                    ACA=action_constraints_analysis([constraints_of_action_generation[-1]], atom_current, atom_goal, domain,
                                                              constants)
                    enabled_constrains = ACA[0]
                    All_Act_Cons_Name = ACA[1]
                    enabled_constrains = sum(enabled_constrains, [])
                    enabled_constrains_rep = state_normal_representation(enabled_constrains)
                    enabled_constrains_rep = list(set(enabled_constrains_rep))
                    enabled_constrains = []
                    for i in enabled_constrains_rep:
                        enabled_constrains.append(predicate_information(i, constants))

                    enabled_sent_messages= communication_analysis(name, all_agents_name, sent_message_update,
                                                                   enabled_constrains, domain,
                                                                   constants)
                    if enabled_sent_messages!=[]:
                        if name not in enabled_sent_messages_dict.keys():
                            enabled_sent_messages_dict.update({name:enabled_sent_messages})
                        else:
                            for m in enabled_sent_messages:
                                if m not in enabled_sent_messages_dict[name]:
                                    enabled_sent_messages_dict[name].append(m)
                    agent.belief_base = []
                    agent.goals = []
                    agent.desired_next_state=[]
                    substate_dict[name] = ([], [])
                    substate_dict_rep[name]=([],[])
                    for ag in agents:
                        if ag.name == 'D':
                            ag.goals.extend(remaining_goals[name])
                            processed_goals = process_belief_list(ag.goals, constants)
                            substate_dict['D'] = ([], processed_goals)
                            substate_dict_rep['D'] = transform_mental_states_normal(substate_dict['D'])
                    active_agents.remove(name)
                elif error_info[name] == ['E4'] and name not in active_agents:
                    enabled_actions=[]
                    enabled_sent_messages=[]
                    agent.belief_base = []
                    agent.goals = []
                    agent.desired_next_state = []
                elif error_info[name] == [] or error_goal_change:
                    for constraint in constraints_of_action_generation:
                        if flag_continue:
                            # Single decision-making generation
                            ACA = action_constraints_analysis([constraint], atom_current, atom_goal, domain,
                                                              constants)
                            enabled_constrains = ACA[0]
                            All_Act_Cons_Name = ACA[1]
                            enabled_constrains = sum(enabled_constrains, [])
                            enabled_constrains_rep = state_normal_representation(enabled_constrains)
                            enabled_constrains_rep = list(set(enabled_constrains_rep))
                            enabled_constrains = []
                            for i in enabled_constrains_rep:
                                enabled_constrains.append(predicate_information(i, constants))
                            if enabled_constrains != []:
                                flag_continue = False
                        else:
                            break
                    enabled_actions = action_enableness_analysis(enableness_of_actions, atom_current,
                                                                 enabled_constrains, domain, All_Act_Cons_Name,
                                                                 constants)
                # Error message checking
                # Abondon goal / redistribute goals to other agents
                # Generate safe decision-making

                else:  # error_info[name]!='E4', reset the focused goal to [located(charging), at(5)]
                    enabled_actions=[]
                    # the decision-making module abondons the current goal
                    if len(substate_dict[name][1]) > 1:
                        substate_dict[name] = (substate_dict[name][0], substate_dict[name][1][1:])
                        substate_dict_rep[name] = transform_mental_states_normal(substate_dict[name])
                    else:
                        goal1 = predicate_information("located(charging)", constants)
                        goal2 = predicate_information("at(5)", constants)
                        substate_dict[name] = (substate_dict[name][0], [[goal1, goal2]])
                        substate_dict_rep[name] = transform_mental_states_normal(substate_dict[name])
                    if len(substate_dict[name][1]) > 0:
                        current_focus = substate_dict[name][1][0]
                    else:
                        current_focus = substate_dict[name][1]
                    atom_goal = state_property_generation(current_focus, knowledge_base, domain, constants)
                    atom_goal_rep = state_normal_representation(atom_goal)

                enabled_actions_rep = state_normal_representation(enabled_actions)
                if enabled_actions == [] and error_info[name] == []:
                    enabled_sent_messages = communication_analysis(name, all_agents_name, sent_message_update,
                                                                   enabled_constrains, domain,
                                                                   constants)
                elif enabled_actions==[] and error_goal_change:
                    enabled_sent_messages = communication_analysis(name, all_agents_name, sent_message_update,
                                                                   enabled_constrains, domain,
                                                                   constants)
                    if enabled_sent_messages!=[]:
                        if name not in enabled_sent_messages_dict.keys():
                            enabled_sent_messages_dict.update({name:enabled_sent_messages})
                        else:
                            for m in enabled_sent_messages:
                                if m not in enabled_sent_messages_dict[name]:
                                    enabled_sent_messages_dict[name].append(m)
                if error_info[name] != ['E4']:
                    last_received_messages = agent.received_messages
                    enabled_event_update = event_analysis(last_received_messages, event_processing, atom_current,
                                                          atom_goal, domain, constants)
                    agent.received_messages = []


                    if enabled_event_update['sent_messages'] != []:
                        enabled_sent_messages_dict.update({agent.name: []})
                        for m in enabled_event_update['sent_messages']:
                            agent.sent_messages = agent.sent_messages + [m]
                        Sending_Msg = enabled_event_update['sent_messages']

                        if enabled_sent_messages_dict[name] == []:
                            enabled_sent_messages_dict[name] = Sending_Msg
                        else:
                            for m in Sending_Msg:
                                if m not in enabled_sent_messages_dict[name]:
                                    enabled_sent_messages_dict[name].append(m)

                    inserted_beliefs = enabled_event_update['add_beliefs']
                    inserted_beliefs_rep = state_normal_representation(inserted_beliefs)
                    deleted_beliefs = enabled_event_update['delete_beliefs']
                    deleted_beliefs_rep = state_normal_representation(deleted_beliefs)
                    adopted_goals = enabled_event_update['add_goals']
                    adopted_goals_rep = state_normal_representation(adopted_goals)
                    dropped_goals = enabled_event_update['delete_goals']
                    dropped_goals_rep = state_normal_representation(dropped_goals)
                    if name in adopted_goals_dict.keys():
                        adopted_goals_dict[name] = adopted_goals_dict[name] + adopted_goals
                        adopted_goals_dict_rep[name] = adopted_goals_dict_rep[name] + adopted_goals_rep
                    else:
                        adopted_goals_dict.update({name: adopted_goals})
                        adopted_goals_dict_rep.update({name: adopted_goals_rep})
                    if inserted_beliefs != []:
                        substate_dict[name] = (substate_dict[name][0] + inserted_beliefs, substate_dict[name][1])
                        substate_dict_rep[name] = transform_mental_states_normal(substate_dict[name])
                    if deleted_beliefs != []:
                        new_beliefs = [x for x in substate_dict[name][0] if x not in deleted_beliefs]
                        substate_dict[name] = (new_beliefs, substate_dict[name][1])
                        substate_dict_rep[name] = transform_mental_states_normal(substate_dict[name])
                    if adopted_goals != []:
                        for goal in adopted_goals:
                            if goal not in substate_dict[name][1][0]:
                                substate_dict[name] = (substate_dict[name][0],
                                                       [substate_dict[name][1][0] + [goal]] + substate_dict[name][1][
                                                                                              1:])
                                substate_dict_rep[name] = transform_mental_states_normal(substate_dict[name])

            elif current_goal < desired_goal and not dummy_flag and not active_flag:
                #For non-active agents, they keep communication function in the reasoning cycle.
                enabled_sent_messages=[]
                substate_dict.update({name: substate})
                substate_dict_rep.update({name: transform_mental_states_normal(substate)})
                # Current focus is the MAS is focusing on.
                if len(substate[1]) > 0:
                    current_focus = substate[1][0]
                else:
                    current_focus = substate[1]
                atom_goal = state_property_generation(current_focus, knowledge_base, domain, constants)
                atom_goal_rep = state_normal_representation(atom_goal)
                last_received_messages = agent.received_messages
                enabled_event_update = event_analysis(last_received_messages, event_processing, atom_current,
                                                      atom_goal, domain, constants)
                agent.received_messages = []
                if enabled_event_update['sent_messages'] != []:
                    enabled_sent_messages_dict.update({agent.name:[]})
                    for m in enabled_event_update['sent_messages']:
                        agent.sent_messages = agent.sent_messages + [m]
                    Sending_Msg = enabled_event_update['sent_messages']

                    if enabled_sent_messages_dict[name] == []:
                        enabled_sent_messages_dict[name] = Sending_Msg
                    else:
                        for m in Sending_Msg:
                            if m not in enabled_sent_messages_dict[name]:
                                enabled_sent_messages_dict[name].append(m)

            elif dummy_flag and not goal_achieved:
                substate_dict.update({name: substate})
                substate_dict_rep.update({name: transform_mental_states_normal(substate)})
                atom_current_rep = state_normal_representation(atom_current)
                last_received_messages = agent.received_messages
                if len(substate[1]) > 0:
                    current_focus = substate[1][0]
                else:
                    current_focus = substate[1]
                #atom_goal = state_property_generation(current_focus, knowledge_base, domain, constants)
                atom_goal=[]
                ACA = action_constraints_analysis(constraints_of_action_generation, atom_current, atom_goal, domain,
                                                  constants)
                enabled_constrains = ACA[0]
                All_Act_Cons_Name = ACA[1]
                enabled_constrains = sum(enabled_constrains, [])
                enabled_constrains_rep = state_normal_representation(enabled_constrains)
                enabled_constrains_rep = list(set(enabled_constrains_rep))
                enabled_constrains = []
                for i in enabled_constrains_rep:
                    enabled_constrains.append(predicate_information(i, constants))
                enabled_actions = []
                enabled_sent_messages = communication_analysis(name, all_agents_name, sent_message_update,
                                                               enabled_constrains, domain, constants)
                if name in enabled_sent_messages_dict.keys():
                    enabled_sent_messages_dict[name]=enabled_sent_messages
                else:
                    enabled_sent_messages_dict.update({name: enabled_sent_messages})
                sent_messages = []
                if enabled_sent_messages!=[]:
                    for m in enabled_sent_messages:
                        sent_messages.append(m)
                agent.sent_messages = sent_messages
                last_received_messages = agent.received_messages
                enabled_event_update = event_analysis(last_received_messages, event_processing, atom_current,
                                                      atom_goal, domain, constants)
                if enabled_event_update['sent_messages'] != []:
                    for m in enabled_event_update['sent_messages']:
                        agent.sent_messages = agent.sent_messages + [m]

                    Sending_Msg = enabled_event_update['sent_messages']

                    if enabled_sent_messages_dict[name] == []:
                        enabled_sent_messages_dict[name] = Sending_Msg

                    else:
                        if Sending_Msg!=[]:
                            for m in Sending_Msg:
                                if m not in enabled_sent_messages_dict[name]:
                                    enabled_sent_messages_dict[name].append(m)



                inserted_beliefs = enabled_event_update['add_beliefs']
                inserted_beliefs_rep = state_normal_representation(inserted_beliefs)
                deleted_beliefs = enabled_event_update['delete_beliefs']
                deleted_beliefs_rep = state_normal_representation(deleted_beliefs)
                if inserted_beliefs != []:
                    change_beliefs=True
                    substate_dict[name] = (substate_dict[name][0] + inserted_beliefs, substate_dict[name][1])
                    substate_dict_rep[name] = transform_mental_states_normal(substate_dict[name])
                if deleted_beliefs != []:
                    change_beliefs=True
                    new_beliefs = [x for x in substate_dict[name][0] if x not in deleted_beliefs]
                    substate_dict[name] = (new_beliefs, substate_dict[name][1])
                    substate_dict_rep[name] = transform_mental_states_normal(substate_dict[name])

            flag_unsafe = True
            sent_flag = False
            if enabled_sent_messages!=[]:
                sent_flag=True
            elif name in enabled_sent_messages_dict.keys():
                if enabled_sent_messages_dict[name]!=[]:
                    sent_flag=True

            if enabled_actions != []:
                for en_action in enabled_actions:
                    if flag_unsafe:
                        substate = substate_dict[name]
                        current_belief_base = substate[0]
                        if error_info[name]!=[]:
                           current_belief_base=[x for x in current_belief_base if x['name'][0]!='E']
                        current_belief_base_rep = state_normal_representation(current_belief_base)
                        possible_next_beliefs = []
                        en_action_dict_form = [en_action]
                        possible_next_beliefs = possible_next_beliefs + state_transformer(
                            en_action_dict_form,
                            current_belief_base,
                            knowledge_base,
                            action_specification,
                            domain, constants)

                        possible_next_beliefs_rep = state_list_normal_representation(possible_next_beliefs)[0]
                        possible_next_beliefs_rep = [x for x in possible_next_beliefs_rep if x not in error_messages]
                        atoms_next_state = state_property_generation(possible_next_beliefs[0],
                                                                     knowledge_base,
                                                                     domain, constants)
                        atoms_next_state_rep = state_normal_representation(atoms_next_state)
                        if safety_checking(atoms_next_state_rep, safety[name]):
                            flag_unsafe = False
                            next_move_dict.update({name: transform_to_normalform(en_action)})
                            agent.desired_next_state = possible_next_beliefs[0]
                    else:
                        break


            elif sent_flag:
                sent_M=[]
                if enabled_sent_messages!=[]:
                    for m in enabled_sent_messages:
                        sent_M.append(m)
                if name in enabled_sent_messages_dict.keys():
                    if enabled_sent_messages_dict[name]!=[]:
                        for m in enabled_sent_messages_dict[name]:
                            if m not in sent_M:
                                sent_M.append(m)
                #if sent_M!=[]:
                #    print("Sent")
                #    print(name)
                #    for m in sent_M:
                #        print(m[0], m[1], transform_to_normalform(m[2]))
                substate = substate_dict[name]
                current_belief_base = substate[0]
                current_belief_base_rep = state_normal_representation(current_belief_base)
                possible_next_beliefs = current_belief_base
                agent.sent_messages = sent_M
                # for b in possible_next_beliefs:
                possible_next_beliefs_rep = state_normal_representation(possible_next_beliefs)
                if active_flag_dict[agent.name]:
                    if error_info[agent.name]==[]:
                        agent.desired_next_state = possible_next_beliefs_rep
                    else:
                        agent.desired_next_state=[]

            elif error_info[name]!=[] and 'E4' not in error_info[name]:
                current_belief_base = [x for x in current_belief_base if x['name'][0] != 'E']
                current_belief_base_rep = state_normal_representation(current_belief_base)
                agent.desired_next_state=current_state_rep

        for agent in agents:
            sender_name = agent.name
            if agent.sent_messages != []:
                sent = agent.sent_messages
                update_sent = []
                if len(sent) > 1:
                    for s in sent:
                        if s not in update_sent:
                            update_sent.append(s)
                    agent.sent_messages = update_sent
                for sent_message in agent.sent_messages:
                    receivers_name = sent_message[1]
                    receivers = []
                    for name in receivers_name:
                        for agent in agents:
                            if agent.name == name:
                                receivers.append(agent)
                                break
                    for receiver in receivers:
                        if sent_message[0] == "send:":
                            msg = "sent:(" + sender_name + ")"
                            receiver.received_messages.append((msg, sent_message[2]))
                        elif sent_message[0] == "send!":
                            msg = "sent!(" + sender_name + ")"
                            receiver.received_messages.append((msg, sent_message[2]))
                        else:
                            msg = "sent?(" + sender_name + ")"
                            receiver.received_messages.append((msg, sent_message[2]))

            agent.belief_base = substate_dict_rep[agent.name][0]
            agent.goals = substate_dict_rep[agent.name][1]
        for agent in agents:
            agent.sent_messages = []

        if last_enabled_sent_messages_dict!={} and enabled_sent_messages_dict=={}:
            non_termination = False

        elif not empty_dict(next_move_dict) and loop_count>3:
            non_termination = False
        elif goal_achieved or active_agents==[] and loop_count>3:
            non_termination=False


    for agent in agents:
        name = agent.name
        agent.sent_messages=[]
        agent.received_messages=[]
        if name not in dummy_agents:
            if name in next_move_dict.keys():
                if agent.goals != []:
                    agent.goals = substate_dict_rep[agent.name][1]
                    next_state=agent.desired_next_state
            else:
                if agent.goals != []:
                    agent.goals = substate_dict_rep[agent.name][1]
                if active_flag_dict[name]:
                    agent.belief_base=substate_dict_rep[agent.name][0]
                    agent.goals=substate_dict_rep[agent.name][1]
                    next_state = process_bliefs(agent.belief_base, constants)
                    NS = [x for x in next_state if x['name'] != 'released']
                    agent.desired_next_state = NS
                else:
                    next_state = process_bliefs(agent.desired_next_state, constants)
                    NS = [x for x in next_state if x['name'] != 'released']
                    agent.desired_next_state = NS
        else:
            if change_beliefs:
                agent.belief_base = copy.deepcopy(agent.desired_next_state)
            agent.desired_next_state=[]
    # Move conflicting information of each agent.
    common_beliefs_update(agents, prior_beliefs, active_agents,dummy_agents)

    # The remaining goals will be redistributed only when there is still at least one active agent.
    redistr_flag=False
    for key in error_info:
        if 'E4' in error_info[key]:
            redistr_flag=True
            break
    for agent in agents:
        name=agent.name
        #if error_info[name]!=[]:
        if 'E4' in error_info[name]:
            agent.desired_next_state=[]
    if redistr_flag:
        active_agents=[]
        for agent in agents:
            name=agent.name
            if agent.name not in dummy_agents:
                if error_info[name]==[]:
                    if agent.belief_base!=[]:
                        active_agents.append(name)
    if active_agents != [] and redistr_flag:
        redistribute_goals(agents, active_agents, dummy_agents)
    return (agents, next_move_dict)


# Require further improvement.
def redistribute_goals(agents, active_agents, dummy_agents):
    control_agent = []
    for agent in agents:
        name = agent.name
        # The communication information agents will not have any meaningful goals, and the control agent has no beleifs.
        if name not in active_agents and name in dummy_agents:
            if agent.goals != []:
                remaining_goals = agent.goals
                agent.goals = []
            else:
                remaining_goals=[]
    i = 0
    while i < len(remaining_goals):
        for agent in agents:
            name = agent.name
            if name in active_agents:
                added_goals = remaining_goals[i:i + 1]
                agent.goals.extend(added_goals)
                if added_goals!=[]:
                    print(name, " received new goals.")
                i = i + 1
    return


def separate_common_beliefs(agent_beliefs, common_beliefs):
    non_common_beliefs = []
    shared_beliefs = {}
    for belief in agent_beliefs:
        k = belief['name']
        if k in common_beliefs.keys():
            if k not in shared_beliefs.keys():
                shared_beliefs.update({k: [belief]})
            else:
                shared_beliefs[k].append(belief)
        else:
            non_common_beliefs.append(belief)
    return (shared_beliefs, non_common_beliefs)


def common_beliefs_update(agents, prior_beliefs, active_agents,dummy_agents):
    for agent in agents:
        name = agent.name
        if name in active_agents:
            next_state = state_normal_representation(agent.desired_next_state)
            NS = [x for x in next_state if x not in prior_beliefs]
            agent.desired_next_state = NS
        elif name not in dummy_agents:
            next_state = agent.desired_next_state
            NS = [x for x in next_state if x not in prior_beliefs]
            agent.desired_next_state = state_normal_representation(NS)

def error_message_processing(agents, error_messages):
    error_info = {}
    # Error message checking
    for agent in agents:
        name = agent.name
        flag_error = False
        for e in error_messages:
            if not flag_error:
                if e in agent.belief_base:
                    error_info[name] = [e]
                    flag_error = True
            else:
                break
        if not flag_error:
            error_info[name] = []
    return error_info

def translation(info_dict,workpiece,last_holding,last_location):
    belief_base=[]
    for key in info_dict:
        if key=='Position':
            pos=info_dict[key][1:]
            place_info='at('+pos+')'
            belief_base.append(place_info)
            if int(pos)>1 and int(pos)<9:
                assigned_info='assigned('+pos+')'
                belief_base.append(assigned_info)
            else:
                if last_location!='':
                    if 1 < int(last_location) and int(last_location) < 9:
                        released_info = 'released(' + last_location + ')'
                        belief_base.append(released_info)

        elif key=='Docked':
            if info_dict[key]=='True':
                docking_info = 'docked('+pos+')'
                belief_base.append(docking_info)
        elif key=='Holding':
            if info_dict[key]=='True':
                holding_info='holding('+str(workpiece)+')'
                belief_base.append(holding_info)
            else:
                if last_holding:
                    delivery_info = 'on(' + str(workpiece) + ','+pos+')'
                    #drop_info = 'dropped(' +workpiece +')'
                    belief_base.append(delivery_info)
                    #belief_base.append(drop_info)
        elif key=='Battery':
            level = str(int(info_dict[key][1:])-1)
            battery_info = 'battery(' + level + ')'
            belief_base.append(battery_info)
        else:
            error=info_dict[key]
            if error!='None':
                belief_base.append(error)
    return belief_base

def action_interpretation(next_move_dict,constants):
    AMR_action_dict={}
    for key in next_move_dict:
        action=next_move_dict[key]
        if action==[]:
            AMR_action_dict.update({key:''})
        else:
            processed_action=predicate_information(action,constants)
            if processed_action['name']=='pickup':
                AMR_action_dict.update({key:'pickup'})
            elif processed_action['name']=='dropoff':
                AMR_action_dict.update({key: 'dropoff'})
            elif processed_action['name'] == 'dock':
                AMR_action_dict.update({key: 'dock'})
            elif processed_action['name']=='charging':
                AMR_action_dict.update({key: 'charging'})
            else:
                name=processed_action['name'][0:4]
                start=processed_action["values_in_non_list"][0]
                destination=processed_action["values_in_non_list"][1]
                action=name+'(P'+start+', P'+destination+')'
                AMR_action_dict.update({key: action})
    return AMR_action_dict
def no_special(text):
    import re
    text = re.sub("[^a-zA-Z0-9 ]+", "", text)
    return text

def update_common_beliefs(prior_beliefs, beliefs,constants):
    prior_beliefs = process_bliefs(prior_beliefs, constants)
    for b in beliefs:
        processed_b = predicate_information(b, constants)
        predicate_name = processed_b['name']
        if predicate_name == 'on':
            if processed_b not in prior_beliefs:
                prior_beliefs.append(processed_b)

        elif predicate_name == 'holding':
            Old_B = copy.deepcopy(prior_beliefs)
            for item in Old_B:
                if item['name'] == 'on':
                    if item["values_in_non_list"][0] == processed_b["values_in_non_list"][0]:
                        prior_beliefs.remove(item)
    prior_beliefs = state_normal_representation(prior_beliefs)
    return prior_beliefs

def task_planner(agents, knowledge_base, constraints_of_action_generation,
                 enableness_of_actions, action_specification, sent_message_update,
                 event_processing, domain, constants, dummy_agents, safety, error_messages,
                 prior_beliefs):
    #from time import sleep
    #sleep(1.5)
    agent_sensor_info_dict={}

    for agent in agents:
        if agent.name not in dummy_agents:
            test = input("Which test do you want to pereform? (Please enter 1-5.)")
            sensor_info_list = info_parse(test)
            agent_sensor_info_dict.update({agent.name:sensor_info_list})

    flag_task = False
    for agent in agents:
        if agent.goals != []:
            flag_task = True
            break

    i=0
    last_holding_dict={}
    last_location_dict={}
    delivery_error_dict={}
    for agent in agents:
        if agent.name not in dummy_agents:
            last_holding_dict.update({agent.name:False})
            last_location_dict.update({agent.name:""})
            delivery_error_dict.update({agent.name:0})

    N = 0
    for key in agent_sensor_info_dict:
        if len(agent_sensor_info_dict[key])>N:
            N=len(agent_sensor_info_dict[key])

    while flag_task and i<N:
        for agent in agents:
            if agent.name not in dummy_agents:
                sensor_info_list=agent_sensor_info_dict[agent.name]
                if i>=len(sensor_info_list):
                    info_dict=sensor_info_list[-1]
                else:
                    info_dict=sensor_info_list[i]

                piece_N = 100
                if agent.goals != []:
                    if agent.goals[0] != []:
                        g = agent.goals[0][0]
                        processed = predicate_information(g, constants)
                        if processed['name'] == 'delivered':
                            piece_N = processed['values_in_non_list'][1]

                #the prior information only relates with the change of the holding information
                holding_change=False
                old_last_holding=last_holding_dict[agent.name]
                old_last_location=last_location_dict[agent.name]
                agent.belief_base = agent.belief_base+ translation(info_dict,piece_N,old_last_holding,old_last_location)
                last_location = info_dict['Position'][1]
                if info_dict['Holding'] == 'True':
                    last_holding = True
                else:
                    last_holding = False
                last_holding_dict[agent.name] = last_holding
                last_location_dict[agent.name]=last_location
                holding_change= not (last_holding==old_last_holding)
                if holding_change:
                    prior_beliefs=update_common_beliefs(prior_beliefs,agent.belief_base,constants)
                if info_dict['Error'] == 'E3':
                    delivery_error_dict[agent.name]= delivery_error_dict[agent.name] + 1

        print("Cycle"+str(i+1))
        for agent in agents:
            name=agent.name
            #print(name,agent.belief_base)

        # Error message checking
        # error_info = error_message_processing(agents,error_messages)
        generated_info = DM_generation(agents, knowledge_base, constraints_of_action_generation,
                                       enableness_of_actions,  action_specification,
                                       sent_message_update,
                                       event_processing, domain, constants, dummy_agents, safety, error_messages,
                                       prior_beliefs)

        agents_info = generated_info[0]
        generated_actions = generated_info[1]
        AMR_actions = action_interpretation(generated_actions,constants)
        for key in AMR_actions:
            if key=='A1' and AMR_actions[key]!='':
                action=AMR_actions[key]
                #AMR16.send_action(action)
        for agent in agents_info:
            #print(agent.name)
            #print(agent.belief_base)
            if agent.name not in dummy_agents:
                NS = agent.desired_next_state
                for s in NS:
                    processed_s = predicate_information(s, constants)
                    if processed_s['name'] == "assigned":
                        agent.desired_next_state.remove(s)
                agent.belief_base = []
                if agent.goals==[]:
                    agent.desired_next_state=[]
                #agent.belief_base=[]
            #print(agent.belief_base)
            #print(agent.goals)
            #print(agent.desired_next_state)
            #agent.sent_messages=[]
            #agent.received_messages=[]
        for key in generated_actions:
            print(key, generated_actions[key])
            processed_action = predicate_information(generated_actions[key], constants)


        i=i+1
        #Work for single agent
        # The task planner will continue there is no goals for the active agents.
        # All active agents achieved their goals.
        # Or there is no active agents
        flag_task = False
        for agent in agents:
            if agent.name not in dummy_agents:
                if agent.goals != []:
                    flag_task = True
                    break
        if empty_dict(generated_actions) and flag_task:
            print("Waiting for new information!")
        if not flag_task:
            print("No active goals!")
    return agents

def info_parse(test):
    sensor_info_list = []
    file_name = "MG_0" + test + ".txt"
    f = open(file_name, "r")
    for line in f.readlines():
        if line[0] == '{':
            L = line.split()
            processed_L = []
            for i in L:
                processed_L.append(no_special(i))
            dict = {}
            i = 0
            while i < len(processed_L):
                dict.update({processed_L[i]: processed_L[i + 1]})
                i = i + 2
            sensor_info_list.append(dict)
    f.close()

    return sensor_info_list

def info_parse2(test):
    sensor_info_list = []
    file_name = "MG_0" + test + ".txt"
    f = open(file_name, "r")
    log_info=f.readlines()
    log_info=[x for x in log_info if x[0]=='{']
    L1=[]
    for item in log_info:
        if L1==[] or L1[-4:].count(item)<4 :
            L1.append(item)

    for line in L1:
        L = line.split()
        processed_L = []
        for i in L:
            processed_L.append(no_special(i))
        dict = {}
        i = 0
        while i < len(processed_L):
            dict.update({processed_L[i]: processed_L[i + 1]})
            i = i + 2
        sensor_info_list.append(dict)
    f.close()
    return sensor_info_list
