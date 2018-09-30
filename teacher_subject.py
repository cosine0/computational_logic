#!/usr/bin/env python3.6
import itertools

try:
    import z3
except ImportError:
    pass


def main():
    number_of_teachers = int(input('Number of teachers: '))
    number_of_subjects = int(input('Number of subjects: '))
    k = int(input('k: '))

    subject_to_teachers = [[] for _ in range(number_of_subjects)]
    for teacher in range(number_of_teachers):
        can_teach = input(f'Indexes of subjects "teacher {teacher}" can teach (separated by spaces):')
        if not can_teach:
            continue
        for subject in can_teach.split():
            subject_to_teachers[int(subject)].append(teacher)

    z3_code = ''
    for teacher in range(number_of_teachers):
        z3_code += f'(declare-const teach_{teacher} Bool)\n'

    z3_code += '(define-fun f () Bool (and\n'
    cases = []
    for subset in itertools.combinations(range(number_of_teachers), k):
        subset = set(subset)
        case_terms = []
        for teacher in range(number_of_teachers):
            if teacher in subset:
                case_terms.append(f'teach_{teacher}')
            else:
                case_terms.append(f'(not teach_{teacher})')

        if len(case_terms) == 1:
            cases.append(f'  {case_terms[0]}')
        elif len(case_terms) >= 2:
            cases.append('  (and ' + ' '.join(case_terms) + ')')

    z3_code += ' (or\n'
    z3_code += '\n'.join(cases)
    z3_code += ')\n'

    for subject in range(number_of_subjects):
        subject_terms = []
        for teacher in subject_to_teachers[subject]:
            subject_terms.append(f'teach_{teacher}')

        if len(subject_terms) == 1:
            z3_code += f' {subject_terms[0]}\n'
        elif len(subject_terms) >= 2:
            z3_code += ' (or ' + ' '.join(subject_terms) + ')\n'

    z3_code += '))\n'
    z3_code += '(assert f)\n'
    z3_code += '(check-sat)\n'

    while True:
        what_to_do = input("What to print ('z3', 'check', 'model', or 'exit'): ")
        if what_to_do == 'z3':
            print(z3_code)
        elif what_to_do == 'check':
            solver = z3.Solver()
            solver.from_string(z3_code)
            print(solver.check())
        elif what_to_do == 'model':
            solver = z3.Solver()
            solver.from_string(z3_code)
            solver.check()
            print(solver.model())
        elif what_to_do == 'exit':
            break


if __name__ == '__main__':
    main()
