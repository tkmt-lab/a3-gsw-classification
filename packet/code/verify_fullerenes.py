"""Small, generator-independent checks of spherical fullerene duals.

Only the <=255-vertex planar_code dialects needed by P1 are accepted.
Canonical forms are exact bytes, not hashes. Every directed root edge and
both global orientations are tried (roots of minimum degree suffice).
At each newly reached vertex, the incoming edge fixes the cyclic order;
BFS labels then encode every adjacency. Thus this minimizes over rooted
maps. For simple spherical triangulations (3-connected), uniqueness of
embedding makes this also an abstract-graph isomorphism invariant.
"""
from __future__ import annotations


class InvalidGraph(ValueError):
    pass


def read_planar_code(stream, *, allow_empty=False):
    """Yield zero-based cyclic adjacency lists; reject malformed/truncated data."""
    header = bytearray()
    while not header.endswith(b"<<"):
        byte = stream.read(1)
        # fullgen writes its header only upon emitting its first graph.
        # Opt in explicitly: truncated or nonempty headerless input still fails.
        if not byte and not header and allow_empty:
            return
        if not byte or len(header) >= 32:
            raise InvalidGraph("missing/invalid planar_code header")
        header.extend(byte)
    if bytes(header) not in (b">>planar_code<<", b">>planar_code le<<",
                            b">>planar_code be<<"):
        raise InvalidGraph("unsupported planar_code header")
    while raw := stream.read(1):
        n = raw[0]
        if n == 0:
            raise InvalidGraph("16-bit planar_code is outside P1's scope")
        rows = []
        for _ in range(n):
            row = []
            while True:
                raw = stream.read(1)
                if not raw:
                    raise InvalidGraph("truncated adjacency list")
                if raw == b"\0":
                    break
                if raw[0] > n or len(row) >= n - 1:
                    raise InvalidGraph("invalid neighbour/oversized adjacency list")
                row.append(raw[0] - 1)
            rows.append(tuple(row))
        yield tuple(rows)


def validate_dual(adj):
    """Check simple connected spherical triangulation with degrees 5/6."""
    n = len(adj)
    if not 12 <= n <= 255:
        raise InvalidGraph("dual order outside 12..255")
    for u, row in enumerate(adj):
        if len(row) not in (5, 6):
            raise InvalidGraph("degree must be 5 or 6")
        if u in row or len(set(row)) != len(row):
            raise InvalidGraph("loop or repeated neighbour")
        if any(v < 0 or v >= n or u not in adj[v] for v in row):
            raise InvalidGraph("out-of-range or nonreciprocal edge")
    if sum(len(row) == 5 for row in adj) != 12:
        raise InvalidGraph("expected exactly twelve degree-5 vertices")
    reached, todo = {0}, [0]
    for u in todo:
        for v in adj[u]:
            if v not in reached:
                reached.add(v)
                todo.append(v)
    if len(reached) != n:
        raise InvalidGraph("disconnected graph")
    # The face permutation on darts is (u,v) -> (v, successor_v(u)).
    successor = {(u, v): (v, adj[v][(adj[v].index(u) + 1) % len(adj[v])])
                 for u, row in enumerate(adj) for v in row}
    remaining = set(successor)
    faces = 0
    while remaining:
        start = next(iter(remaining))
        dart, face = start, []
        while dart in remaining:
            remaining.remove(dart)
            face.append(dart[0])
            dart = successor[dart]
        if dart != start or len(face) != 3 or len(set(face)) != 3:
            raise InvalidGraph("face is not a simple triangle")
        faces += 1
    edges = len(successor) // 2
    if n - edges + faces != 2:
        raise InvalidGraph("embedding is not spherical (Euler characteristic != 2)")
    return {"dual_vertices": n, "edges": edges, "faces": faces,
            "carbon_vertices": faces}


def canonical_form(adj):
    """Return full, lossless rooted-map minimum; call after validate_dual."""
    n = len(adj)
    # Cache rotations once per graph, including the global reflected order.
    rotations = [{}, {}]
    for u, row in enumerate(adj):
        for i, parent in enumerate(row):
            rotations[0][u, parent] = row[i:] + row[:i]
            reverse = row[:i + 1][::-1] + row[i + 1:][::-1]
            rotations[1][u, parent] = reverse
    best = None
    degree = min(map(len, adj))
    for root, row in enumerate(adj):
        if len(row) != degree:
            continue
        for neighbour in row:
            for rotation in rotations:
                labels = [-1] * n
                labels[root] = 0
                vertices, parents = [root], [neighbour]
                code = bytearray([n])
                equal = best is not None
                for u, parent in zip(vertices, parents):
                    order = rotation[u, parent]
                    block = bytearray([len(order)])
                    for v in order:
                        if labels[v] == -1:
                            labels[v] = len(vertices)
                            vertices.append(v)
                            parents.append(u)
                        block.append(labels[v])
                    if equal:
                        bound = best[len(code):len(code) + len(block)]
                        if block > bound:
                            break
                        equal = block == bound
                    code.extend(block)
                else:
                    candidate = bytes(code)
                    if best is None or candidate < best:
                        best = candidate
    return best


def check_unique(graphs):
    seen = set()
    for adj in graphs:
        validate_dual(adj)
        code = canonical_form(adj)
        if code in seen:
            raise InvalidGraph("isomorphic duplicate")
        seen.add(code)
    return seen
