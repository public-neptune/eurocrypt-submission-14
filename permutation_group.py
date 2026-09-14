"""Small permutation primitives shared by reconstruction and tests."""


def compose(first, second):
    """Apply ``first`` and then ``second``."""
    return [second[x] for x in first]


def invert(permutation):
    result = [0] * len(permutation)
    for point, image in enumerate(permutation):
        result[image] = point
    return result


def word_perm(word, generators, degree):
    value = list(range(degree))
    for generator in word:
        value = compose(value, generators[generator])
    return value


def schreier_sims_order(generators, degree):
    """Return the generated group order with a compact Schreier--Sims chain."""
    generators = [tuple(generator) for generator in generators]

    def orbit_transversal(point, values):
        transversal = {point: tuple(range(degree))}
        queue = [point]
        while queue:
            source = queue.pop()
            for generator in values:
                target = generator[source]
                if target not in transversal:
                    transversal[target] = compose(
                        transversal[source], generator)
                    queue.append(target)
        return transversal

    levels = []

    def strip(permutation, selected_levels):
        for point, transversal, _generators in selected_levels:
            image = permutation[point]
            if image not in transversal:
                return permutation, False
            permutation = compose(permutation, invert(transversal[image]))
        return permutation, all(
            permutation[point] == point for point in range(degree))

    def close(start):
        point, transversal, values = levels[start]
        for representative in list(transversal.values()):
            for generator in values:
                product = compose(representative, generator)
                correction = transversal[product[point]]
                schreier = compose(product, invert(correction))
                if any(schreier[i] != i for i in range(degree)):
                    residue, is_identity = strip(schreier, levels[start + 1:])
                    if not is_identity:
                        add_generator(residue, start + 1)

    def add_generator(permutation, depth):
        for selected in range(depth, len(levels)):
            point, _transversal, values = levels[selected]
            values.append(tuple(permutation))
            levels[selected] = (
                point, orbit_transversal(point, values), values)
            close(selected)
            return
        for point in range(degree):
            if permutation[point] != point:
                values = [tuple(permutation)]
                levels.append((point, orbit_transversal(point, values), values))
                close(len(levels) - 1)
                return

    for generator in generators:
        residue, is_identity = strip(list(generator), levels)
        if not is_identity:
            add_generator(residue, 0)

    order = 1
    for _point, transversal, _generators in levels:
        order *= len(transversal)
    return order
