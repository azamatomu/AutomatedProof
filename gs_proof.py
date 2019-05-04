from math import factorial

n = 2
m = 3
UNIT_COMPREHENSION = True


def allVoters():
    return range(n)


def allAlternatives():
    return range(m)


def allProfiles():
    return range(factorial(m) ** n)


def nthPerm(num, mylist):
    length = len(mylist)
    if length > 1:
        pos = num // factorial(length-1)
        restnum = num - pos * factorial(length-1)
        restlist = mylist[:pos] + mylist[pos+1:]
        return [mylist[pos]] + nthPerm(restnum, restlist)
    else:
        return [mylist[0]]


def preference(i, r):
    fact = factorial(m)
    return (r % (fact ** (i+1))) // (fact ** i)


def prefers(i, x, y, r):
    mylist = nthPerm(preference(i, r), list(allAlternatives()))
    return mylist.index(x) < mylist.index(y)


def top(i, x, r):
    mylist = nthPerm(preference(i, r), list(allAlternatives()))
    return mylist.index(x) == 0


def alternatives(condition):
    return [x for x in allAlternatives() if condition(x)]


def voters(condition):
    return [i for i in allVoters() if condition(i)]


def profiles(condition):
    return [r for r in allProfiles() if condition(r)]


def posLiteral(r, x):
    return r * m + x + 1


def negLiteral(r, x):
    return (-1) * posLiteral(r, x)


def cnfAtLeastOne():
    cnf = []
    for r in allProfiles():
        cnf.append([posLiteral(r, x) for x in allAlternatives()])
    return cnf


def cnfResolute():
    cnf = []
    for r in allProfiles():
        for x in allAlternatives():
            for y in alternatives(lambda y: x < y):
                cnf.append([negLiteral(r, x), negLiteral(r, y)])
    return cnf


def cnfSurjective():
    cnf = []
    for x in allAlternatives():
        cnf.append([posLiteral(r, x) for r in allProfiles()])
    return cnf


def iVariants(i, r1, r2):
    return all(preference(j, r1) == preference(j, r2) for j in voters(lambda j: j != i))


def cnfStrategyProof():
    cnf = []
    for i in allVoters():
        for r1 in allProfiles():
            for r2 in profiles(lambda r2: iVariants(i, r1, r2)):
                for x in allAlternatives():
                    for y in alternatives(lambda y: prefers(i, x, y, r1)):
                        cnf.append([negLiteral(r1, y), negLiteral(r2, x)])
    return cnf


def cnfNondictatorial():
    cnf = []
    for i in allVoters():
        clause = []
        for r in allProfiles():
            for x in alternatives(lambda x: top(i, x, r)):
                clause.append(negLiteral(r, x))
        cnf.append(clause)
    return cnf


if __name__ == '__main__':
    from pylgl import solve

    if UNIT_COMPREHENSION:
        print('Permutation on [1, 2, 3] :')
        for i in range(6):
            print(f'\tPermutation {i + 1} : {nthPerm(i, [1, 2, 3])}')

    cnf = (cnfAtLeastOne() + cnfResolute() + cnfSurjective() +
           cnfStrategyProof() + cnfNondictatorial())

    print(cnf[0])
    print(len(cnf))
    print(solve(cnf))

    print(f'There are {len(cnfStrategyProof())} strategyproof voting rules.')
