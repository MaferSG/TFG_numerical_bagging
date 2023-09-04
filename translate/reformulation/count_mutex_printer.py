import options
import re
from collections import OrderedDict


def add_count_mutexes(baggable_types_list):

    if options.writeout_reformulation_logic:
        print('Generating count mutexes')

    exact = open('exactlyoneMutexes.txt', 'w+')
    mutexfwd = open('mutexgroupfwdMutexes.txt', 'w+')
    num_exacts = 0
    num_fwds = 0
    
    for baggable_type in baggable_types_list:
        for macropredicate in [baggable_type.macropredicate] + baggable_type.goal_macropredicates:
            for bag_obj in list(OrderedDict.fromkeys([x.bagged_object for x in macropredicate.bag_mapping])):
                init_atoms = list(OrderedDict.fromkeys(macropredicate.ground_all_at_zero(bag_obj, True)))
                bag_size = len([x for x in macropredicate.bag_mapping if x.bagged_object == bag_obj])
                
                for atom in init_atoms:
                    
                    num_exacts = num_exacts + 1
                    
                    # Create the exactly one mutex groups (ie. either 0 or 1 or 2 or ...)
                    exact.write("[ExactlyOne_fw\t" + "\t".join([str(atom).replace("?num", [n.number_object.name for n in macropredicate.counts if n.number == x][0]) for x in range(0, bag_size + 1)]) + "]\n")
                    
                    # Create the mutex group forward mutexes (eg. if there are 5 in the bag and 5 with these values, then we know that there cant be 3 with those values)
                    for i in range(1, bag_size+1):
                        i_num_obj_name = [n.number_object.name for n in macropredicate.counts if n.number == i][0]
                        for j in range(1, i+1):
                            if i + j <= bag_size:
                                continue
                            j_num_obj_name = [n.number_object.name for n in macropredicate.counts if n.number == j][0]
                            
                            for other_atom in init_atoms:
                                if other_atom == atom:
                                    continue
                                mutexfwd.write("[MutexGroup_fw\t" + str(atom).replace("?num", i_num_obj_name) + "\t" + str(other_atom).replace("?num", j_num_obj_name) + "]\n")
                                num_fwds = num_fwds + 1
               
                         
    if options.writeout_reformulation_logic:
       print(num_exacts, "ExactlyOne mutexes generated")  
       print(num_fwds, "MutexGroup mutexes generated") 
                    
    exact.close()
    mutexfwd.close()

    
