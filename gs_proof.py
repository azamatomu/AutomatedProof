from math import factorial

n = 2
m = 3


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


def posLiteralUnique(r, x):
    return (factorial(m)**n)*m + r * m + x + 1


def negLiteralUnique(r, x):
    return (-1) * posLiteralUnique(r, x)


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


def cnfDefinitionQ():
    cnf = []
    for x in allAlternatives():
        for r in allProfiles():
            cnf.append([negLiteralUnique(r, x), posLiteral(r, x)])
            for y in alternatives(lambda y: y != x):
                cnf.append([negLiteralUnique(r, x), negLiteral(r, y)])

            clause = [posLiteralUnique(r, x), negLiteral(r, x)]
            for y in alternatives(lambda y: y != x):
                clause.append(posLiteral(r, y))
            cnf.append(clause)

    return cnf


def notMostPreferred(i, r1, r2, x):
    pref = nthPerm(preference(i, r1), list(allAlternatives()))
    x_pos = pref.index(x)
    clause = []
    for i in range(x_pos):
        clause.append(posLiteral(r2, pref[i]))
    clause.append(negLiteral(r2, pref[x_pos]))
    return clause


def notLeastPreferred(i, r1, r2, x):
    pref = nthPerm(preference(i, r1), list(allAlternatives()))
    x_pos = pref.index(x)
    clause = []
    for i in range(len(pref)-1-x_pos):
        clause.append(posLiteral(r2, pref[-(i+1)]))
    clause.append(negLiteral(r2, pref[x_pos]))
    return clause


def cnfOptimistProof():
    cnf = []
    for i in allVoters():
        for r1 in allProfiles():
            for r2 in profiles(lambda r2: iVariants(i, r1, r2)):
                for x in allAlternatives():
                    for y in alternatives(lambda y: prefers(i, x, y, r1)):
                        cnf.append(notMostPreferred(i, r1, r1, y) +
                                   notMostPreferred(i, r1, r2, x))
    return cnf


def cnfPessimistProof():
    cnf = []
    for i in allVoters():
        for r1 in allProfiles():
            for r2 in profiles(lambda r2: iVariants(i, r1, r2)):
                for x in allAlternatives():
                    for y in alternatives(lambda y: prefers(i, x, y, r1)):
                        cnf.append(notLeastPreferred(i, r1, r1, y) +
                                   notLeastPreferred(i, r1, r2, x))
    return cnf


def cnfNonimposed():
    cnf = []
    for x in allAlternatives():
        clause = []
        for r in allProfiles():
            clause.append(posLiteralUnique(r, x))
        cnf.append(clause)

    return cnf


def cnfStronglyNondictatorial():
    cnf = []
    for i in allVoters():
        clause = []
        for r in allProfiles():
            x = list(alternatives(lambda x: top(i, x, r)))[0]
            clause.append(negLiteral(r, x))
        cnf.append(clause)

    return cnf


if __name__ == '__main__':
    from pylgl import solve, itersolve

    padding = 60

    # TEST
    cnf = (cnfAtLeastOne() + cnfResolute() + cnfSurjective() +
           cnfStrategyProof() + cnfNondictatorial())
    assert solve(cnf) == 'UNSAT'

    # Q1
    print(' Question 1 '.center(padding, '-'))

    base = cnfAtLeastOne() + cnfResolute() + cnfStrategyProof()

    cnf = base
    rules_res_sp = list(itersolve(cnf))
    print(f'Number of resolute strategy-proof rules : {len(rules_res_sp)}')

    cnf = base + cnfSurjective()
    rules_res_sp_sur = list(itersolve(cnf))
    print(f'\tNumber of which are surjective : {len(rules_res_sp_sur)}')

    cnf = base + cnfNondictatorial()
    rules_res_sp_non = list(itersolve(cnf))
    print(f'\tNumber of which are dictatorial : {len(rules_res_sp_non)}\n')

    # Q2
    print(' Question 2 '.center(padding, '-'))

    definition_q = cnfDefinitionQ()
    non_imposition = cnfNonimposed()
    print(f'Number of clauses for the definition of q : {len(definition_q)}')
    print(f'Number of clauses for non-imposition : {len(non_imposition)}')

    optimistic = cnfOptimistProof()
    pessimistic = cnfPessimistProof()
    print(
        f'Number of clauses for the immunity against optimistic voters : {len(optimistic)}')
    print(
        f'Number of clauses for the immunity against pessimistic voters : {len(pessimistic)}')

    strongly_non_dictatorial = cnfStronglyNondictatorial()
    print(
        f'Number of clauses for strong non-dictatoriality : {len(strongly_non_dictatorial)}')

    # print(cnf[0])
    # print(len(cnf))
    # print(solve(cnf))
    # print(f'There are {len(cnfStrategyProof())} strategyproof voting rules.')
