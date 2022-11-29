#For a property P, find its key in the dictionary storing properties.
def symbol_property(agent,P,dict_properties):
    symbol=[]
    for p in P:
        for k in dict_properties:
            if dict_properties[k]==(agent,p):
                symbol.append(k)
                break
    return symbol

#Given a state, search the key in the state dictionary.
def state_search(s, state_check):
    for key in state_check:
        if key==s:
            return state_check[key]

def state_map2(states):
    dict_state={}
    count=0
    for s in states:
        if s=='I':
            dict_state.update({count:s})
        else:
            dict_state.update({count:s})
        count=count+1
    return dict_state

#Map state to a number
def state_map(states):
    state_check={}
    count=0
    for s in states:
        if s=='I':
            state_check.update({s:count})
        else:
            state_check.update({s: count})
        count=count+1
    return state_check

def state_search2(s, state_check):
    for key in state_check:
        if state_check[key]==s:
            return key

def action_search(action,dict_actions):
    loop=len(action)
    i=1
    result="("
    for item in action:
        for key in dict_actions:
            if item ==dict_actions[key]:
                if i<loop:
                    result=result+key+','

                else:
                    result = result + key + ')'
                    return result
                break
        i = i + 1

def map_transition(transition,dict_state,dict_actions):
    return ((state_search2(transition[0],dict_state),action_search(transition[1],dict_actions),state_search2(transition[2],dict_state)))


def interface_generation(system, transitions, properties):
    # Compute all distict properties.
    property_list = []
    for key in properties:
        for agent in properties[key]:
            property_list = property_list + (properties[key][agent])
    property_list = list(set(property_list))
    property_dict = {}
    for key in properties:
        for agent in properties[key]:
            property_dict.update({agent: properties[key][agent]})
    # Store all properties in a dictionary, and assign a name to each property
    dict_properties2 = {}
    count_p = 1
    for p in property_list:
        dict_properties2.update({"p" + str(count_p): p})
        count_p = count_p + 1
    dict_properties = {}
    count_p = 1
    for agent in property_dict:
        for p in property_dict[agent]:
            dict_properties.update({"p" + str(count_p): (agent, p)})
            count_p = count_p + 1
    # trans is a dictionary storing all next states of the current state.
    trans = {}
    for n in transitions:
        for key in n:
            if n[key][0] not in trans.keys():
                trans.update({n[key][0]: [n[key][2]]})
            else:
                for t in trans:
                    if t == n[key][0]:
                        trans[t].append(n[key][2])
    # A dictionary store state and its proeprty in the symbolic way.
    s_properties_normal = {}

    for key in properties:
        s_properties_normal[key] = {}
        for agent in properties[key]:
            s_properties_normal[key][agent] = symbol_property(agent, properties[key][agent], dict_properties)

    # Extract all states
    system_states = []
    for s in system:
        system_states.append(s)

    # A dictionary storing the states
    dict_state = state_map(system_states)
    dict_state2 = state_map2(system_states)
    actions = []
    for transition in transitions:
        for key in transition:
            act = transition[key][1]
            actions = actions + act
    actions = list(set(actions))
    dict_actions = {}
    count_act = 1
    for act in actions:
        flag = True
        for key in dict_actions:
            if act == dict_actions[key]:
                flag = False
                break
        if flag:
            dict_actions.update({"action" + str(count_act): act})
            count_act = count_act + 1
    for i in transitions:
        for key in i:
            print(map_transition(i[key], dict_state2, dict_actions))
    final_state = state_search("S" + str(len(system) - 1), dict_state)
    # Generate the interface to Prism/Storm
    f = open("test1.pm", "w+")
    f.write("dtmc" + '\n' + '\n')
    f.write("module test" + '\n')
    f.write("  s: [0.." + str(len(system) - 1) + "]  init 0 ;" + '\n')
    # Initialize all properties based on their value in the initial state.
    initial=[]
    for key in s_properties_normal['I']:
        initial=initial+s_properties_normal['I'][key]
    for i in dict_properties:
        f.write("  " + i + ":bool")  # +'  init false;\n')
        if i in initial:
            f.write('   init true;\n')
        else:
            f.write('   init false;\n')
    f.write("\n")

    for t in trans:
        if len(trans[t]) == 1:
            f.write("     []")
            P1 = []
            for agent in s_properties_normal[t]:
                P1 = P1 + s_properties_normal[t][agent]
            current_s = state_search(t, dict_state)
            f.write('s=' + str(current_s))
            for key in dict_properties:
                if key in P1:
                    f.write('  &(' + key + '= true)  ')
                else:
                    f.write('  &(' + key + '= false)  ')

            P2 = []
            for agent in s_properties_normal[trans[t][0]]:
                P2 = P2 + s_properties_normal[trans[t][0]][agent]
            next_s = state_search(trans[t][0], dict_state)

            f.write("->" + "(s'=" + str(next_s) + ')')
            for key in dict_properties:
                if key in P2:
                    f.write('  &(' + key + '\'= true)  ')
                else:
                    f.write('  &(' + key + '\'= false)  ')
            f.write(';\n')
        else:
            K = len(trans[t])
            f.write("     []")
            P1=[]
            for agent in s_properties_normal[t]:
                P1=P1+s_properties_normal[t][agent]
            # print(P1)
            current_s = state_search(t, dict_state)
            f.write('s=' + str(current_s))
            for key in dict_properties:
                if key in P1:
                    f.write('  &(' + key + '= true)  ')
                else:
                    f.write('  &(' + key + '= false)  ')

            P2 = s_properties_normal[trans[t][0]]
            P2 = []
            for agent in s_properties_normal[trans[t][0]]:
                P2 = P2 + s_properties_normal[trans[t][0]][agent]
            next_s = state_search(trans[t][0], dict_state)
            f.write("->" + "1/" + str(K) + ": (s'=" + str(next_s) + ')')
            for key in dict_properties:
                if key in P2:
                    f.write('  &(' + key + '\'= true)  ')
                else:
                    f.write('  &(' + key + '\'= false)  ')
            next_states = trans[t][1:]
            for s in next_states:
                P2 = []
                for agent in s_properties_normal[s]:
                    P2 = P2 + s_properties_normal[s][agent]
                next_s = state_search(s, dict_state)
                f.write(" + 1/" + str(K) + ": (s'=" + str(next_s) + ')')
                for key in dict_properties:
                    if key in P2:
                        f.write('  &(' + key + '\'= true)  ')
                    else:
                        f.write('  &(' + key + '\'= false)  ')
            f.write(";\n")
    f.write('     []s=' + str(final_state) + '-> (s\'=' + str(final_state) + ");\n")
    f.write("\n\n endmodule")

    f.close()
    f = open("Specifications01.txt", "w+")
    f.write("The states are:\n")
    for key in dict_state2:
        f.write(str(key) + ": " + dict_state2[key] + '\n')
    f.write("The actions are:\n")
    for key in dict_actions:
        f.write(key + ": " + ''.join(dict_actions[key]) + '\n')
    f.write("The properties are:\n")

    for key in dict_properties:
        f.write(key + ": " + ''.join(dict_properties[key]) + '\n')

    f.close()
    f = open("test2.pm", "w+")
    f.write("dtmc" + '\n' + '\n')
    f.write("module test" + '\n')
    f.write("  s: [0.." + str(len(system) - 1) + "]  init 0 ;" + '\n')

    # Initialize all properties based on their value in the initial state.
    initial = []
    for key in s_properties_normal['I']:
        initial = initial + s_properties_normal['I'][key]

    for i in dict_properties:
        f.write("  " + i + ":bool")  # +'  init false;\n')
        if i in initial:
            f.write('   init true;\n')
        else:
            f.write('   init false;\n')
    f.write("\n")

    for t in transitions:
        for key in t:
            transition_symbol = map_transition(t[key], dict_state2, dict_actions)
            f.write("   []"+' s=' + str(transition_symbol[0]))
            P1=[]
            for agent in s_properties_normal[dict_state2[transition_symbol[0]]]:
                P1=P1+s_properties_normal[dict_state2[transition_symbol[0]]][agent]
            for key in dict_properties:
                if key in P1:
                    f.write('  &(' + key + '= true)  ')
                else:
                    f.write('  &(' + key + '= false)  ')
                    "(s'="
            f.write('->' + "(s'=" + str(transition_symbol[2]) + ")")

            P2=[]
            for agent in s_properties_normal[dict_state2[transition_symbol[2]]]:
                P2=P2+s_properties_normal[dict_state2[transition_symbol[2]]][agent]
            for key in dict_properties:
                if key in P2:
                    f.write('  &(' + key + '\'= true)  ')
                else:
                    f.write('  &(' + key + '\'= false)  ')
            f.write(';\n')
    f.write('     []s=' + str(final_state) + '-> (s\'=' + str(final_state) + ");\n")
    f.write("\n\n endmodule")
    f.close()
    return

