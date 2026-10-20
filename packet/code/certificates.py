"""Finite absence certificates with a small checker independent of both searches.

In a triangulation with exactly two common neighbours across every edge,
each initial triangle has a unique continuation avoiding its preceding
vertex. A certificate lists the complete simple continuation of *every*
admissible initial triangle, and why it cannot continue. The checker never
calls gsw.FacialWalk or gsw.reference_find.
"""


def starts(adj):
    return {(u, v, w) for u in range(len(adj)) if len(adj[u]) == 5
            for v in adj[u] if len(adj[v]) == 6
            for w in adj[u] if w in adj[v]}


def absent_certificate(adj, *, hex_only=False):
    rows = []
    neighbours = list(map(set, adj))
    for seed in sorted(starts(adj)):
        path = list(seed)
        while True:
            if hex_only and len(adj[path[-1]]) != 6:
                # The third vertex cannot be an endpoint of a length>=4 path.
                reason = 'interior_degree5'
                break
            a, b, c = path[-3:]
            possible = (neighbours[b] & neighbours[c]) - {a}
            if len(possible) != 1:
                raise ValueError('unique continuation prerequisite not met')
            nxt = possible.pop()
            if nxt in path:
                reason = 'repeated_vertex'
                break
            path.append(nxt)
            if len(path) % 2 == 0 and len(adj[nxt]) == 5 and len(adj[c]) == 6:
                raise ValueError('cannot certify absence: admissible path found')
        rows.append(dict(start=seed, path=path, stop=reason))
    return dict(schema=1, predicate='hex_interior' if hex_only else 'literal_definition1',
                adjacency=adj, maximal_paths=rows)


def check_certificate(cert):
    """Check exhaustive root coverage and every deterministic continuation."""
    adj = cert['adjacency']
    hex_only = cert['predicate'] == 'hex_interior'
    if cert.get('schema') != 1 or cert['predicate'] not in ('hex_interior', 'literal_definition1'):
        raise ValueError('invalid certificate schema/predicate')
    # This explicitly verifies the unique-continuation assumption globally.
    for u, row in enumerate(adj):
        for v in row:
            if len([w for w in row if w in adj[v]]) != 2:
                raise ValueError('not exactly two common neighbours')
    expected = starts(adj)
    seen = set()
    for row in cert['maximal_paths']:
        path, seed = row['path'], tuple(row['start'])
        if seed not in expected or seed in seen or tuple(path[:3]) != seed:
            raise ValueError('invalid/duplicate starting triangle')
        seen.add(seed)
        if len(path) != len(set(path)) or len(path) < 3:
            raise ValueError('invalid simple path')
        for i in range(3, len(path)):
            options = [w for w in adj[path[i - 2]]
                       if w in adj[path[i - 1]] and w != path[i - 3]]
            if options != [path[i]]:
                raise ValueError('wrong continuation')
            # With a hex-only predicate a degree-five vertex can only end a
            # valid even-order path, never be an interior vertex.
            if hex_only and len(adj[path[i - 1]]) != 6:
                raise ValueError('continued through forbidden interior vertex')
            if (i + 1) % 2 == 0 and len(adj[path[i]]) == 5 and len(adj[path[i - 1]]) == 6:
                raise ValueError('certificate contains an admissible endpoint')
        if hex_only and len(adj[path[-1]]) != 6:
            if row['stop'] != 'interior_degree5':
                raise ValueError('wrong stopping reason')
        else:
            u, v, w = path[-3:]
            options = [x for x in adj[v] if x in adj[w] and x != u]
            if len(options) != 1 or options[0] not in path or row['stop'] != 'repeated_vertex':
                raise ValueError('certificate stopped before the path was exhausted')
    if seen != expected:
        raise ValueError('missing starting triangles')
    return dict(starts=len(seen), path_vertices=sum(len(r['path']) for r in cert['maximal_paths']))


def cluster_sizes(adj, degree):
    unseen = {u for u, row in enumerate(adj) if len(row) == degree}
    sizes = []
    while unseen:
        queue = [unseen.pop()]
        for u in queue:
            for v in adj[u]:
                if v in unseen:
                    unseen.remove(v)
                    queue.append(v)
        sizes.append(len(queue))
    return sorted(sizes, reverse=True)
