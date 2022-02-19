###########################################################################
## answers.py - Code template for Project Functional Dependencies
###########################################################################

## If you need to import library put it below

## Change the function below with your student number.
def student_number():
    return 'A0123456X'

## Q1a. Determine the closure of a given set of attribute S the schema R and functional dependency F
def closure(R, F, S):
    return []

## Q1b. Determine all attribute closures excluding superkeys that are not candidate keys given the schema R and functional dependency F
def all_closures(R, F): 
    return []
    
## Q2a. Return a minimal cover of the functional dependencies of a given schema R and functional dependencies F.
def min_cover(R, FD): 
    return []

## Q2b. Return all minimal covers reachable from the functional dependencies of a given schema R and functional dependencies F.
def min_covers(R, FD):
    '''
    Explain the rationale of the algorithm here.
    '''
    return []

## Q2c. Return all minimal covers of a given schema R and functional dependencies F.
def all_min_covers(R, FD):
    '''
    Explain the rationale of the algorithm here.
    '''
    return []

## You can add additional functions below



## Main functions
def main():
    ### Test case from the project
    R = ['A', 'B', 'C', 'D']
    FD = [[['A', 'B'], ['C']], [['C'], ['D']]]

    print(closure(R, FD, ['A']))
    print(closure(R, FD, ['A', 'B']))
    print(all_closures(R, FD))

    R = ['A', 'B', 'C', 'D', 'E', 'F']
    FD = [[['A'], ['B', 'C']], [['B'], ['C','D']], [['D'], ['B']], [['A','B','E'], ['F']]]
    print(min_cover(R, FD)) 

    R = ['A', 'B', 'C']
    FD = [[['A'], ['B']], [['B'], ['C']], [['C'], ['A']]] 
    print(min_covers(R, FD))
    print(all_min_covers(R, FD)) 

    ### Add your own additional test cases if necessary


if __name__ == '__main__':
    main()



