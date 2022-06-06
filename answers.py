###########################################################################
## answers.py - Code template for Project Functional Dependencies
###########################################################################

## If you need to import library put it below

## Change the function below with your student number.
def student_number():
    return 'A0248373X'


## Q1a. Determine the closure of a given set of attribute S the schema R and functional dependency F
def closure(R, F, S):
    R = R.copy()
    F = F.copy()
    S = S.copy()

    attributes_closure = S
    closure_change_flag = True

    while (closure_change_flag):
        closure_change_flag = False
        for fd in F:
            if include_attributes(attributes_closure, fd[0]):
                for attribue in fd[1]:
                    if attributes_closure.count(attribue) == 0:
                        attributes_closure.append(attribue)
                F.remove(fd)
                closure_change_flag = True
                break

    if len(attributes_closure) > 1:
        attributes_closure.sort()
    return attributes_closure


## Q1b. Determine all attribute closures excluding superkeys that are not candidate keys given the schema R and functional dependency F
def all_closures(R, F):
    R = R.copy()
    F = F.copy()
    candidate_keys = []
    all_closures_sets = []

    # all possible subset of attributes; the result return by all_possible_subsets(r) has been sorted as [['A'],['B'],['C'],['A','B'],['A','C'],['B','C'].....]
    all_subsets = all_possible_subsets(R)

    # iterate all possible subset of attributes
    for set in all_subsets:
        # when a set of attribute is super key but not candidate keys, set "is_super_not_candidate" to True
        is_super_not_candidate = False;
        for candidate in candidate_keys:
            if include_attributes(set, candidate):
                is_super_not_candidate = True
                break

        if is_super_not_candidate:
            continue
        else:
            temp_closure = closure(R, F, set)
            all_closures_sets.append([set, temp_closure])

            # Judge whether it is candidate key
            if len(temp_closure) == len(R):
                candidate_keys.append(set)
    return all_closures_sets


## Q2a. Return a minimal cover of the functional dependencies of a given schema R and functional dependencies F.
def min_cover(R, FD):
    R = R.copy()
    FD = FD.copy()
    sigma = FD.copy()

    # The RHS of Σ are singletons.
    sigma1 = []
    for fd in sigma:
        if len(fd[1]) > 1:
            for attribue in fd[1]:
                sigma1.append([fd[0], [attribue]]);
        else:
            sigma1.append(fd)

    # The LHS of Σ is not redundant (no extraneous attributes)
    sigma2 = []
    for fd in sigma1:
        temp_fd = fd.copy()
        find_redundant = True
        while (find_redundant):
            find_redundant = False
            if len(temp_fd[0]) == 1:
                break
            else:
                for X in temp_fd[0]:
                    temp_set = temp_fd[0].copy()
                    temp_set.remove(X)
                    if include_attributes(closure(R, FD, temp_set), X):
                        find_redundant = True
                        temp_fd = [temp_set, temp_fd[1]]
                        break
        sigma2.append(temp_fd)

    # preprocessing
    # remove trivial
    origin_sigma2 = sigma2.copy()
    for fd in origin_sigma2:
        if include_attributes(fd[0], fd[1]):
            sigma2.remove(fd)

    # remove duplicate
    origin_sigma2 = sigma2.copy()
    sigma2 = []
    for fd in origin_sigma2:
        if sigma2.count(fd) == 0:
            sigma2.append(fd)

    # Σ is minimal, no redundant FD.
    sigma3 = sigma2.copy()
    for fd in sigma2.copy():
        if (include_attributes(fd[0], fd[1])):
            sigma3.remove(fd)
        else:
            sigma3.remove(fd)
            if include_attributes(closure(R, sigma3, fd[0]), fd[1]):
                continue
            else:
                sigma3.append(fd)
    return sigma3


## Q2b. Return all minimal covers reachable from the functional dependencies of a given schema R and functional dependencies F.
def min_covers(R, FD):
    '''
    Explain the rationale of the algorithm here.
    step0: sigma =  FD
    step1: use sigma to obtain sigma1; The RHS of sigma1 are singletons
    step2.1: use sigma1 to obtain sigma2; The LHS of sigma2 are set of all possible simplified LHS base on sigma1
    step2.2: use sigma2 to obtain all_sigma2; each item in all_sigma2 is a sigma that the LHS is not redundant
    step3.1: preprocessing: for each sigma in all_sigma2 remove trivial fd
    step3.2: preprocessing: for each sigma in all_sigma2 remove duplicate fd
    step3.3: preprocessing: remove duplicate sigma in all_sigma2
    step4.1: for each sigma in all_sigma2. iterate each fd in each sigma, check whether the fd is redundant;
            for each sigma, the final all_sigma3 include possible non-redundant result base on each sigma
    step4.2: minimal_covers include all the possible result base on all_sigma2
    '''
    R = R.copy()
    FD = FD.copy()
    sigma = FD.copy()

    # The RHS of Σ are singletons.
    sigma1 = []
    for fd in sigma:
        if len(fd[1]) > 1:
            for attribue in fd[1]:
                sigma1.append([fd[0], [attribue]]);
        else:
            sigma1.append(fd)

    # The LHS of Σ is not redundant (no extraneous attributes)
    # iterate each fd in sigma1, get all possible simplified LHS
    sigma2 = []
    for fd in sigma1:
        is_parent_of_simplified_LHS = False;
        fd_possible_simplified_LHS = []

        for LHS in all_possible_subsets(fd[0]):
            for simplified_LHS in fd_possible_simplified_LHS:
                if include_attributes(LHS, simplified_LHS):
                    is_parent_of_simplified_LHS = True
                    break
            if is_parent_of_simplified_LHS:
                continue
            else:
                if include_attributes(closure(R, sigma1, LHS), fd[1]):
                    fd_possible_simplified_LHS.append(LHS)

        sigma2.append([fd_possible_simplified_LHS, fd[1]])

    all_sigma2 = []
    for fd in sigma2:
        previous_all_sigma2 = all_sigma2.copy()
        all_sigma2 = []
        if len(previous_all_sigma2) > 0:
            for each in previous_all_sigma2:
                if len(fd[0]) == 0:
                    temp = each.copy()
                    temp.append(fd)
                    all_sigma2.append(temp)
                    continue
                for LHS in fd[0]:
                    temp = each.copy()
                    temp.append([LHS, fd[1]])
                    all_sigma2.append(temp)
        else:
            for LHS in fd[0]:
                all_sigma2.append([[LHS, fd[1]]])

    # preprocessing: remove trivial fd
    origin_all_sigma2 = all_sigma2.copy()
    all_sigma2 = []
    for each_sigma2 in origin_all_sigma2:
        origin_each_sigma2 = each_sigma2.copy()
        for fd in origin_each_sigma2:
            if include_attributes(fd[0], fd[1]):
                each_sigma2.remove(fd)
        all_sigma2.append(each_sigma2)

    # preprocessing: remove duplicate fd
    origin_all_sigma2 = all_sigma2.copy()
    all_sigma2 = []
    for each_sigma2 in origin_all_sigma2:
        origin_each_sigma2 = each_sigma2.copy()
        each_sigma2 = []
        for fd in origin_each_sigma2:
            if each_sigma2.count(fd) == 0:
                each_sigma2.append(fd)
        all_sigma2.append(each_sigma2)

    # after 2 previous preprocessing steps: remove duplicate sigma2 in all_sigma2
    origin_all_sigma2 = all_sigma2.copy()
    all_sigma2 = []
    for each_sigma2 in origin_all_sigma2:
        each_sigma2.sort()
        if all_sigma2.count(each_sigma2) == 0:
            all_sigma2.append(each_sigma2)

    minimal_covers = []
    # iterate each sigma2 in all sigma2 to get all minimal covers reachable from the functional dependencies
    for each_sigma2 in all_sigma2:
        all_sigma3 = [each_sigma2.copy()]

        # iterate each fd in each sigma2, check whether the fd is redundant; for each sigma2, the final all_sigma3 include possible non-redundant result
        for fd in each_sigma2:
            previous_all_sigma3 = all_sigma3.copy()
            all_sigma3 = []
            for each in previous_all_sigma3:
                each.remove(fd)
                if include_attributes(closure(R, each, fd[0]), fd[1]):
                    temp = each.copy()
                    all_sigma3.append(temp)
                    each.append(fd)
                    all_sigma3.append(each)
                else:
                    each.append(fd)
                    all_sigma3.append(each)

        for each in all_sigma3:
            each.sort()
        all_sigma3 = sorted(all_sigma3, key=lambda i: len(i))

        origin_all_sigma3 = all_sigma3.copy()
        for each_x in all_sigma3:
            for each_y in origin_all_sigma3:
                if len(each_y) > len(each_x):
                    is_redundant = True
                    for fd in each_x:
                        if each_y.count(fd) == 0:
                            is_redundant = False
                            break
                    if is_redundant:
                        if all_sigma3.count(each_y) == 0:
                            continue
                        else:
                            all_sigma3.remove(each_y)

        # sort
        for each in all_sigma3:
            each.sort()
        all_sigma3.sort()

        # avoid duplicate result
        for each in all_sigma3:
            if minimal_covers.count(each) == 0:
                minimal_covers.append(each)

    return minimal_covers


## Q2c. Return all minimal covers of a given schema R and functional dependencies F.
def all_min_covers(R, FD):
    '''
    Explain the rationale of the algorithm here.
    step1: in order to get  all minimal covers of a given schema R and functional dependencies F(sigma), we need to first
            compute sigma+(sigma_plus)
    step2: remove the information which is not essential of sigma+, to get the "minimal sigma+" (sigma_plus_min)
    step3: get all minimal covers by call min_covers(R,sigma_plus_min)
    '''
    R = R.copy()
    FD = FD.copy()
    sigma_plus = all_closures(R, FD)

    # consider the LHS of some fd is null
    for fd in FD:
        if len(fd[0])==0:
            sigma_plus.append(fd)

    # remove trivial in sigma_plus
    sigma_plus_origin = sigma_plus.copy()
    for fd in sigma_plus_origin:
        if include_attributes(fd[0], fd[1]):
            sigma_plus.remove(fd)

    # RHS = RHS - LHS
    sigma_plus_origin = sigma_plus.copy()
    sigma_plus = []
    for fd in sigma_plus_origin:
        for attribute in fd[0]:
            if fd[1].count(attribute) != 0:
                fd[1].remove(attribute)
        sigma_plus.append([fd[0], fd[1]])

    # remove redundant fd to get sigma_plus_min
    sigma_plus_min = []
    for fd_x in sigma_plus:
        could_removed = False
        for fd_y in sigma_plus:
            if fd_x == fd_y:
                continue
            if include_attributes(fd_x[0], fd_y[0]) and include_attributes(fd_y[1], fd_x[1]):
                could_removed = True
                break
        if could_removed == False:
            sigma_plus_min.append(fd_x)

    # use the sigma_plus_min as the FD to get the all minimal covers
    result = min_covers(R, sigma_plus_min)
    return result


## You can add additional functions below
# judge attribute set y whether is a subset of attribute set x
def include_attributes(X, Y):
    include_flag = True
    for attribute_y in Y:
        if X.count(attribute_y) == 0:
            include_flag = False;
            return include_flag;
    return include_flag;


# return all possible subsets of a given set；returns in ascending order of subsets' length
def all_possible_subsets(X):
    all_subsets = []
    # set X length
    X_length = len(X);
    for i in range(2 ** X_length):
        temp_set = [];
        for j in range(X_length):
            if ((i >> j) % 2 == 1):
                temp_set.append(X[j])
        if (len(temp_set) != 0):
            all_subsets.append(temp_set)
    all_subsets = sorted(all_subsets, key=lambda i: str(len(i)) + i[0])
    return all_subsets


## Main functions
def main():
    ### Test case from the project
    R = ['A', 'B', 'C', 'D']
    FD = [[['A', 'B'], ['C']], [['C'], ['D']]]

    print(closure(R, FD, ['A']))
    print(closure(R, FD, ['A', 'B']))
    print(all_closures(R, FD))

    R = ['A', 'B', 'C', 'D', 'E', 'F']
    FD = [[['A'], ['B', 'C']], [['B'], ['C', 'D']], [['D'], ['B']], [['A', 'B', 'E'], ['F']]]
    print(min_cover(R, FD))

    R = ['A', 'B', 'C']
    FD = [[['A'], ['B']], [['B'], ['C']], [['C'], ['A']]]
    print(min_covers(R, FD))
    print(all_min_covers(R, FD))

    ### Add your own additional test cases if necessary
    # test Function include_attributes
    # print(include_attributes(['A', 'B', 'C'], ['A']))
    # print(include_attributes(['A', 'B', 'C'], ['A', 'B']))
    # print(include_attributes(['A', 'B', 'C'], ['A', 'B', 'C']))
    # print(include_attributes(['A', 'B', 'C'], ['B', 'C']))
    # print(include_attributes(['A', 'B', 'C'], ['D']))
    # print(include_attributes(['A', 'B', 'C'], ['A', 'D']))

    # test Function all_possible_subsets
    # print(all_possible_subsets(['A', 'B', 'C', 'D']))

    # test Function closure
    # R = ['A', 'B', 'C', 'D', 'E']
    # FD = [[['A', 'B'], ['C', 'D', 'E']], [['A', 'C'], ['B', 'D', 'E']], [['B'], ['C']], [['C'], ['B']], [['C'], ['D']],
    #       [['B'], ['E']], [['C'], ['E']]]
    # print(closure(R, FD, ['A']))
    # print(closure(R, FD, ['A', 'B']))
    # print(closure(R, FD, ['B', 'C']))
    # print(all_closures(R, FD))

    # R = ['A', 'B', 'C', 'D', 'E']
    # FD = [[['A', 'B'], ['C']], [['D'], ['D', 'B']], [['B'], ['E']], [['E'], ['D']],
    #       [['A', 'B', 'D'], ['A', 'B', 'C', 'D']]]
    # print(all_closures(R, FD))

    # test function min_covers
    # tutorial
    # R = ['A', 'B', 'C', 'D', 'E']
    # FD = [[['A', 'B'], ['C']], [['D'], ['D', 'B']], [['B'], ['E']], [['E'], ['D']],
    #       [['A', 'B', 'D'], ['A', 'B', 'C', 'D']]]
    # print(min_cover(R, FD))
    # print(min_covers(R, FD))

    # slide
    # R = ['A', 'B', 'C', 'D', 'E']
    # FD = [[['A', 'B'], ['C', 'D', 'E']], [['A', 'C'], ['B', 'D', 'E']], [['B'], ['C']], [['C'], ['B']], [['C'], ['D']],
    #       [['B'], ['E']], [['C'], ['E']]]
    # print(min_covers(R, FD))

    # R = ['A', 'B', 'C', 'D', 'E']
    # FD = [[['A', 'B'], ['C', 'D', 'E']], [['A', 'D'], ['B', 'C', 'E']], [['A', 'E'], ['B', 'C', 'D']],
    #       [['B'], ['D', 'E']], [['D'], ['B', 'E']], [['E'], ['B', 'D']]]
    # print(min_cover(R, FD))
    # print(min_covers(R, FD))

    # test function all_min_covers
    # R = ['A', 'B', 'C']
    # FD = [[['A'],['B']],[['B'],['C']],[['C'],['A']]]
    # print(all_min_covers(R, FD))

    # tutorial
    # R = ['A', 'B', 'C', 'D', 'E']
    # FD = [[['A', 'B'], ['C']], [['D'], ['D', 'B']], [['B'], ['E']], [['E'], ['D']],
    #       [['A', 'B', 'D'], ['A', 'B', 'C', 'D']]]
    # print(all_min_covers(R, FD))


if __name__ == '__main__':
    main()
