#!/usr/bin/env python3.6
import itertools

try:
    import z3
except ImportError:
    pass


def main():
    number_of_vertices = int(input('Number of vertices: '))
    number_of_colors = int(input('Number of colors: '))

    edges = set()
    while True:
        edge = input('Input one edge (indexes of 2 vertices separated by spaces, empty line when you are done): ')
        if not edge:
            break

        first_vertex, second_vertex = map(int, edge.split())
        edges.add(tuple(sorted([first_vertex, second_vertex])))

    z3_code = ''
    for vertex in range(number_of_vertices):
        for color in range(number_of_colors):
            z3_code += f'(declare-const col_{vertex}_{color} Bool)\n'

    z3_code += '(define-fun f () Bool (and\n'
    one_color_terms = []
    for vertex in range(number_of_vertices):
        has_color_terms = []
        for color in range(number_of_colors):
            has_color_terms.append(f'col_{vertex}_{color}')

        if len(has_color_terms) == 1:
            one_color_terms.append(f' has_color_terms[0]')
        if len(has_color_terms) >= 2:
            one_color_terms.append(' (or ' + ' '.join(has_color_terms) + ')')

        for color1, color2 in itertools.combinations(range(number_of_colors), 2):
            one_color_terms.append(f' (or (not col_{vertex}_{color1}) (not col_{vertex}_{color2}))')

    adjacent_terms = []
    for vertex1, vertex2 in edges:
        for color in range(number_of_colors):
            adjacent_terms.append(f' (or (not col_{vertex1}_{color}) (not col_{vertex2}_{color}))')

    z3_code += '\n'.join(one_color_terms + adjacent_terms)

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
            model = solver.model()
            print(model)

            results = dict()
            for decl in model.decls():
                results[decl.name()] = model.get_interp(decl)

            vertex_color = [None] * number_of_vertices
            for vertex in range(number_of_vertices):
                for color in range(number_of_colors):
                    if z3.is_true(results[f'col_{vertex}_{color}']):
                        vertex_color[vertex] = color
                        break
            for vertex in range(number_of_vertices):
                print(f'vertex {vertex} -> color {vertex_color[vertex]}')
        elif what_to_do == 'exit':
            break


if __name__ == '__main__':
    main()
