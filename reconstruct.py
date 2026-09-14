#!/usr/bin/env python3
"""Recover symmetric-group or SL(2,343) generators from an instance."""
import argparse, gzip, hashlib, json, os, select, signal, struct, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from permutation_group import word_perm, schreier_sims_order
from stream_instance import iter_rules, parse_coupling
from recover_coupled import (recover_alpha, recover_alpha_psl,
                             projective_alignments, symmetric_alignments,
                             CouplingRecoveryError)

UP, LO = "ABCDEFGHIJKLMNOPQRSTUVWXYZ", "abcdefghijklmnopqrstuvwxyz"


class BackendFailure(RuntimeError):
    pass


class SearchBudgetExpired(TimeoutError):
    pass


def log(m):
    print(m, file=sys.stderr, flush=True)


def _remaining_time(deadline):
    if deadline is None:
        return None
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise SearchBudgetExpired("search wall budget expired")
    return remaining


def _invoke_candidate(callback, candidate, deadline):
    remaining = _remaining_time(deadline)
    if remaining is None:
        return callback(candidate, deadline)

    def expired(_signum, _frame):
        raise SearchBudgetExpired("search wall budget expired")

    started = time.monotonic()
    try:
        previous_handler = signal.signal(signal.SIGALRM, expired)
        previous_timer = signal.setitimer(signal.ITIMER_REAL, remaining)
    except (AttributeError, ValueError):
        result = callback(candidate, deadline)
    else:
        try:
            result = callback(candidate, deadline)
        finally:
            elapsed = time.monotonic() - started
            signal.setitimer(signal.ITIMER_REAL, 0)
            signal.signal(signal.SIGALRM, previous_handler)
            previous_remaining = max(0.0, previous_timer[0] - elapsed)
            if previous_remaining:
                signal.setitimer(signal.ITIMER_REAL, previous_remaining,
                                 previous_timer[1])
    _remaining_time(deadline)
    return result


def _backend_status(name, returncode, diagnostics):
    statuses = [line.split(maxsplit=1)[1]
                for line in diagnostics.splitlines()
                if line.startswith("STATUS ") and len(line.split(maxsplit=1)) == 2]
    if len(statuses) != 1:
        raise BackendFailure(
            f"{name} exited {returncode} without one terminal status")
    status = statuses[0]
    expected = {"EXHAUSTED": {0, 1}, "CANDIDATE_LIMIT": {0},
                "INCONCLUSIVE": {3}}
    if status not in expected or returncode not in expected[status]:
        raise BackendFailure(
            f"{name} exited {returncode} with invalid status {status!r}")
    return status


def _cache_fingerprint(path, **options):
    stat = os.stat(path)
    return {"source": os.path.abspath(path), "size": stat.st_size,
            "mtime_ns": stat.st_mtime_ns, **options}


def _file_digest(path):
    digest = hashlib.blake2b(digest_size=16)
    with open(path, "rb") as source:
        for block in iter(lambda: source.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def _atomic_gzip_json(path, value):
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=".henbane-cache-", suffix=".json.gz",
                                     dir=os.path.dirname(path) or ".")
    os.close(fd)
    try:
        with gzip.open(temporary, "wt", encoding="utf-8") as target:
            json.dump(value, target, separators=(",", ":"))
        os.replace(temporary, path)
    finally:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass


def _decode_pools(value):
    return ([(tuple(u), tuple(v)) for u, v in value["upper"]],
            [(tuple(u), tuple(v)) for u, v in value["lower"]],
            value["couplings"], value.get("data", {}))

def _read_exact(source, size):
    value = source.read(size)
    if len(value) != size:
        raise ValueError("truncated native preprocessing harvest")
    return value


def _read_native_harvest(path):
    with open(path, "rb") as source:
        if _read_exact(source, 8) != b"HENPRE3\0":
            raise ValueError("invalid native preprocessing harvest")

        def integer(code):
            return struct.unpack(code, _read_exact(source, struct.calcsize(code)))[0]

        def string():
            return _read_exact(source, integer("<I")).decode("ascii")

        def pairs(alphabet):
            offset = ord(alphabet)
            return [(tuple(ord(char) - offset for char in string()),
                     tuple(ord(char) - offset for char in string()))
                    for _ in range(integer("<I"))]

        upper = pairs("A")
        lower = pairs("a")
        couplings = []
        for _ in range(integer("<I")):
            coupling = parse_coupling(string(), string())
            if coupling is None:
                raise ValueError("invalid coupling in native harvest")
            couplings.append(coupling)
        data = {}
        for name in ("challenge", "zeros", "ones"):
            data[name] = [string() for _ in range(integer("<I"))]
        if source.read(1):
            raise ValueError("trailing data in native preprocessing harvest")
    return upper, lower, couplings, data


def prepare_inputs(path, preprocessor, poolcap=5000, coupcap=2000,
                   cache_path=None, deadline=None):
    """Select the production relation/coupling pools with the native streamer."""
    if not os.path.isfile(preprocessor):
        raise RuntimeError(f"native preprocessor is missing: {preprocessor}")
    fingerprint = _cache_fingerprint(
        path, version=4,
        poolcap=poolcap, coupcap=coupcap,
        preprocessor=os.path.abspath(preprocessor),
        preprocessor_digest=_file_digest(preprocessor))
    if cache_path:
        try:
            with gzip.open(cache_path, "rt", encoding="utf-8") as source:
                cached = json.load(source)
            if cached.get("fingerprint") == fingerprint:
                pools = _decode_pools(cached["pools"])
                log(f"[cache] prepared inputs: {cache_path}")
                return pools
        except (FileNotFoundError, OSError, ValueError, KeyError,
                json.JSONDecodeError):
            pass

    started = time.time()
    fd, harvest = tempfile.mkstemp(suffix=".prepared")
    os.close(fd)
    decompressor = subprocess.Popen(
        ["gzip", "-dc", path], stdout=subprocess.PIPE)
    command = [preprocessor, "--out", harvest,
               "--poolcap", str(poolcap), "--coupcap", str(coupcap)]
    try:
        try:
            native = subprocess.run(
                command, stdin=decompressor.stdout,
                timeout=_remaining_time(deadline))
        except subprocess.TimeoutExpired as error:
            raise SearchBudgetExpired("search wall budget expired") from error
        decompressor.stdout.close()
        try:
            decompressor_status = decompressor.wait(
                timeout=_remaining_time(deadline))
        except subprocess.TimeoutExpired as error:
            raise SearchBudgetExpired("search wall budget expired") from error
        if native.returncode or decompressor_status:
            raise RuntimeError(
                f"native preprocessing failed (native={native.returncode}, "
                f"gzip={decompressor_status})")
        upper, lower, couplings, data = _read_native_harvest(harvest)
    finally:
        if decompressor.stdout is not None and not decompressor.stdout.closed:
            decompressor.stdout.close()
        if decompressor.poll() is None:
            decompressor.terminate()
            decompressor.wait()
        try:
            os.unlink(harvest)
        except FileNotFoundError:
            pass
    pools = {"upper": upper, "lower": lower,
             "couplings": couplings, "data": data}
    if cache_path:
        _atomic_gzip_json(cache_path, {
            "fingerprint": fingerprint, "pools": pools})
        log(f"[cache] wrote prepared inputs in {time.time() - started:.1f}s: "
            f"{cache_path}")
    return _decode_pools(pools)


def parity_pattern(relations, d):
    """Unique odd sign character forced by the relations, or None."""
    m = []
    for u, v in relations:
        e = [0] * d
        for c in u:
            e[c] ^= 1
        for c in v:
            e[c] ^= 1
        m.append(e)
    piv, ri = {}, 0
    for col in range(d):
        sel = next((r for r in range(ri, len(m)) if m[r][col]), None)
        if sel is None:
            continue
        m[ri], m[sel] = m[sel], m[ri]
        for r in range(len(m)):
            if r != ri and m[r][col]:
                m[r] = [x ^ y for x, y in zip(m[r], m[ri])]
        piv[col] = ri
        ri += 1
    free = [c for c in range(d) if c not in piv]
    if len(free) != 1:
        return None
    s = [0] * d
    s[free[0]] = 1
    for col, r in piv.items():
        s[col] = m[r][free[0]]
    return s if any(s) else None


def closure_relations(challenge, case, max_total, closure_bin,
                      cache_path=None, deadline=None):
    """Run closure over one case; return (relations, orders)."""
    fingerprint = _cache_fingerprint(
        challenge, version=5, case=case, max_total=max_total,
        closure=os.path.abspath(closure_bin),
        closure_digest=_file_digest(closure_bin))
    if cache_path:
        try:
            with gzip.open(cache_path, "rt", encoding="utf-8") as source:
                cached = json.load(source)
            if cached.get("fingerprint") == fingerprint:
                log(f"[cache] closure/{case}: {cache_path}")
                return ([(tuple(u), tuple(v)) for u, v in cached["relations"]],
                        cached["orders"])
        except (FileNotFoundError, OSError, ValueError, KeyError, json.JSONDecodeError):
            pass
    fd, harvest = tempfile.mkstemp(suffix=".harvest")
    os.close(fd)
    zcat = subprocess.Popen(["zcat", challenge], stdout=subprocess.PIPE)
    closure_cmd = [closure_bin, "--case", case,
                   "--out", harvest, "--max-emit", str(max_total)]
    try:
        try:
            cl = subprocess.run(
                closure_cmd, stdin=zcat.stdout, stderr=subprocess.PIPE,
                text=True, timeout=_remaining_time(deadline))
        except subprocess.TimeoutExpired as error:
            raise SearchBudgetExpired("search wall budget expired") from error
        zcat.stdout.close()
        try:
            zcat_status = zcat.wait(timeout=_remaining_time(deadline))
        except subprocess.TimeoutExpired as error:
            raise SearchBudgetExpired("search wall budget expired") from error
    except BaseException:
        try:
            os.unlink(harvest)
        except FileNotFoundError:
            pass
        raise
    finally:
        if zcat.stdout is not None and not zcat.stdout.closed:
            zcat.stdout.close()
        if zcat.poll() is None:
            zcat.terminate()
            zcat.wait()
    if cl.returncode or zcat_status:
        try:
            os.unlink(harvest)
        except FileNotFoundError:
            pass
        raise RuntimeError(
            f"closure preprocessing failed (closure={cl.returncode}, "
            f"zcat={zcat_status}):\n{cl.stderr[-4000:]}")
    orders = None
    for line in cl.stderr.splitlines():
        if line.startswith("orders:"):
            orders = [int(x) for x in line.split()[1:]]
    rels = []
    with open(harvest) as f:
        for line in f:
            v = list(map(int, line.split()))
            if not v:
                continue
            lu, lv = v[0], v[1 + v[0]]
            if lu + lv <= max_total:
                rels.append((tuple(v[1:1 + lu]), tuple(v[2 + lu:2 + lu + lv])))
    os.unlink(harvest)
    if cache_path:
        _atomic_gzip_json(cache_path, {
            "fingerprint": fingerprint, "relations": rels, "orders": orders})
    return rels, orders


def shortest(relations, cap):
    seen, out = set(), []
    for u, v in sorted(relations, key=lambda r: (len(r[0]) + len(r[1]), r)):
        k = (u, v) if u <= v else (v, u)
        if u == v or k in seen:
            continue
        seen.add(k)
        out.append((u, v))
        if len(out) >= cap:
            break
    return out


def cancel_pair(left, right):
    """Cancel the common group-word prefix and suffix exactly."""
    prefix = 0
    limit = min(len(left), len(right))
    while prefix < limit and left[prefix] == right[prefix]:
        prefix += 1
    suffix = 0
    while (suffix < limit - prefix
           and left[len(left) - 1 - suffix] == right[len(right) - 1 - suffix]):
        suffix += 1
    left_end = len(left) - suffix if suffix else len(left)
    right_end = len(right) - suffix if suffix else len(right)
    left, right = left[prefix:left_end], right[prefix:right_end]
    return (left, right) if left <= right else (right, left)


def cancelled_shortest(relations, cap):
    reduced = []
    for u, v in relations:
        u, v = cancel_pair(u, v)
        if u != v:
            reduced.append((u, v))
    return shortest(reduced, cap)


def permutation_force_prefix(relations, d, seeds):
    """Return the maximal force prefix from ``seeds``."""
    known = set(seeds)
    chain = []
    while len(known) < d:
        choices = []
        for index, (left, right) in enumerate(relations):
            unknown = [generator for generator in left + right
                       if generator not in known]
            if len(unknown) == 1:
                choices.append((len(left) + len(right), index,
                                unknown[0], (left, right)))
        if not choices:
            break
        _length, _index, generator, relation = min(choices)
        known.add(generator)
        chain.append(relation)
    return chain, frozenset(known)


def permutation_force_chain(relations, d, seeds):
    """Return a force prefix only when it assigns every generator."""
    chain, known = permutation_force_prefix(relations, d, seeds)
    return chain if len(known) == d else None


def whole_permutation_portfolio(relations, d, cap):
    """Preserve the strongest force prefix, then short relators."""
    candidates = []
    for first in range(d):
        for second in range(first + 1, d):
            chain, known = permutation_force_prefix(
                relations, d, (first, second))
            candidates.append((-len(known),
                               sum(len(u) + len(v) for u, v in chain),
                               first, second, chain))
    chain = min(candidates)[-1] if candidates else []
    selected = []
    seen = set()

    def add(relation):
        left, right = relation
        key = (left, right) if left <= right else (right, left)
        if left != right and key not in seen and len(selected) < cap:
            seen.add(key)
            selected.append(relation)

    for relation in chain:
        add(relation)
    for relation in cancelled_shortest(relations, cap):
        add(relation)
    return selected


def cache_file(cache_dir, challenge, kind, *parts):
    if not cache_dir:
        return None
    identity = "|".join((os.path.abspath(challenge), kind, *map(str, parts)))
    digest = hashlib.blake2b(identity.encode(), digest_size=8).hexdigest()
    base = os.path.basename(challenge).split(".json")[0]
    return os.path.join(cache_dir, f"{base}.{kind}.{digest}.json.gz")


def write_flat(path, n, d, rels):
    with open(path, "w") as f:
        f.write(f"{n} {d} {len(rels)}\n")
        for u, v in rels:
            f.write(f"{len(u)} " + " ".join(map(str, u)) +
                    f" {len(v)} " + " ".join(map(str, v)) + "\n")


def write_matrix_flat(path, d, rels):
    """Write a representation-free matrix presentation (D, R, then words)."""
    with open(path, "w") as target:
        target.write(f"{d} {len(rels)}\n")
        for left, right in rels:
            target.write(f"{len(left)} " + " ".join(map(str, left)) +
                         f" {len(right)} " + " ".join(map(str, right)) + "\n")


def _drain_candidate_stdout(job):
    lines = []
    stream = job["stdout"]
    while not job.get("stdout_eof"):
        try:
            chunk = os.read(stream.fileno(), 1 << 16)
        except BlockingIOError:
            break
        if not chunk:
            job["stdout_eof"] = True
            break
        job["stdout_buffer"] += chunk
        while b"\n" in job["stdout_buffer"]:
            line, job["stdout_buffer"] = job["stdout_buffer"].split(b"\n", 1)
            lines.append(line.decode("ascii", "strict"))
    if job.get("stdout_eof") and job["stdout_buffer"]:
        lines.append(job["stdout_buffer"].decode("ascii", "strict"))
        job["stdout_buffer"] = b""
    return lines


def _parse_psl_candidate(line, d, psl2):
    values = line.split()
    if values[:1] == ["M"]:
        if len(values) != 1 + 4 * d:
            return None
        try:
            raw = list(map(int, values[1:]))
            matrices = tuple(tuple(raw[4 * index:4 * index + 4])
                             for index in range(d))
            if not all(psl2.mcanonical(matrix) == matrix
                       and psl2.mis_psl(matrix) for matrix in matrices):
                return None
            return matrices
        except (ValueError, ZeroDivisionError):
            return None
    return None


def _stop_psl_jobs(jobs, grace=5.0, deadline=None):
    """Broadcast TERM, wait once for the whole set, then KILL stragglers."""
    alive = [job["process"] for job in jobs if job["process"].poll() is None]
    for process in alive:
        try:
            os.killpg(process.pid, signal.SIGTERM)
        except ProcessLookupError:
            pass
    shutdown_deadline = time.monotonic() + grace
    if deadline is not None:
        shutdown_deadline = min(shutdown_deadline, deadline)
    while alive and time.monotonic() < shutdown_deadline:
        alive = [process for process in alive if process.poll() is None]
        if alive:
            time.sleep(max(0.0, min(
                0.05, shutdown_deadline - time.monotonic())))
    for process in alive:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    for job in jobs:
        process = job["process"]
        try:
            process.wait()
        except ChildProcessError:
            pass
        job["stdout"].close()
        job["stderr"].close()


def holds(tup, pool, n):
    return all(word_perm(u, tup, n) == word_perm(v, tup, n) for u, v in pool)


def _verifier_result(name, completed):
    lines = completed.stdout.splitlines()
    detail = next((line for line in lines
                   if line.startswith(("RULES FAIL", "CLASSIFICATION FAIL"))),
                  next((line for line in lines if line.startswith("RULES ")),
                       completed.stderr.strip() or completed.stdout.strip()))
    if completed.returncode == 0:
        return True, detail
    if completed.returncode == 1:
        return False, detail
    raise BackendFailure(
        f"{name} exited {completed.returncode}: {detail or 'no diagnostics'}")


def _run_verifier(name, command):
    try:
        completed = subprocess.run(
            command, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, check=False)
    except OSError as error:
        raise BackendFailure(f"{name} failed to start: {error}") from error
    return _verifier_result(name, completed)


def check_complete_symmetric_rules(challenge, tup, n, case, executable):
    """Stream every public internal rule for ``case`` through the native verifier."""
    letters = UP if case == "upper" else LO
    command = [executable, challenge, "-n", str(n),
               "--rules-only", "--case", case]
    for index, permutation in enumerate(tup):
        command += ["-g", letters[index], *map(str, permutation)]
    return _run_verifier("symmetric verifier", command)


def check_complete_symmetric_pair(challenge, alpha, beta, n, executable):
    """Stream every internal and mixed rule for a two-copy candidate."""
    command = [executable, challenge, "-n", str(n), "--rules-only"]
    for letters, tup in ((LO, alpha), (UP, beta)):
        for index, permutation in enumerate(tup):
            command += ["-g", letters[index], *map(str, permutation)]
    return _run_verifier("symmetric verifier", command)


def check_complete_projective_rules(challenge, matrices, case, executable):
    """Stream every projected internal rule through the independent verifier."""
    letters = UP if case == "upper" else LO
    command = [executable, challenge, "--projective", "--rules-only",
               "--case", case]
    for index, matrix in enumerate(matrices):
        command += ["-g", letters[index], *map(str, matrix)]
    return _run_verifier("SL verifier", command)


def check_complete_projective_pair(challenge, alpha, beta, executable):
    """Stream every projected internal and mixed rule for two PSL tuples."""
    command = [executable, challenge, "--projective", "--rules-only"]
    for letters, matrices in ((LO, alpha), (UP, beta)):
        for index, matrix in enumerate(matrices):
            command += ["-g", letters[index], *map(str, matrix)]
    return _run_verifier("SL verifier", command)


def check_complete_sl_lift(challenge, generators, labels, executable):
    """Verify all exact SL rules and labeled words for a lifted pair/tuple."""
    command = [executable, challenge]
    for letter, matrix in sorted(generators.items()):
        command += ["-g", letter, *map(str, matrix)]
    command += ["--labels", labels]
    return _run_verifier("SL verifier", command)


def infer_dimension(relations, case, couplings=(), classification=None):
    """Infer a contiguous tuple width without assuming every letter is present."""
    indices = [letter for left, right in relations for letter in left + right]
    for coupling in couplings:
        fields = ("V", "W") if case == "upper" else ("u",)
        indices.extend(letter for field in fields for letter in coupling[field])
    alphabet = UP if case == "upper" else LO
    for words in (classification or {}).values():
        for word in words:
            indices.extend(alphabet.index(letter) for letter in word if letter in alphabet)
    return max(indices, default=-1) + 1


def recover_sl_solutions(challenge, tup, case, classification, alpha=None):
    """Return every compatible exact SL lift and its central classification."""
    import psl2_343 as psl2
    from psl2_343 import sl

    matrices = {}
    tuple_letters = UP if case == "upper" else LO
    for index, permutation in enumerate(tup):
        matrices[tuple_letters[index]] = psl2.matrix_from_permutation(permutation)
    if alpha is not None:
        for index, permutation in enumerate(alpha):
            matrices[LO[index]] = psl2.matrix_from_permutation(permutation)

    relations = ((left, right) for left, right in iter_rules(challenge))
    recoveries = sl.recover_lift_candidates(
        matrices,
        classification.get("zeros", ()),
        classification.get("ones", ()),
        relations,
    )
    solutions = []
    for recovery in recoveries:
        labels = sl.classify(
            classification.get("challenge", ()), recovery.generators)
        details = {
            "negative_identity": list(sl.NEGATIVE_IDENTITY),
            "generators": {letter: list(matrix)
                           for letter, matrix in sorted(recovery.generators.items())},
            "base_lift_signs": recovery.signs,
            "rank": recovery.rank,
            "nullity": recovery.nullity,
            "lift_candidates": recovery.solution_count,
            "equations": recovery.equations,
            "relation_equations": recovery.relation_equations,
        }
        solutions.append((labels, details))
    return solutions


def recover_sl_solution(challenge, tup, case, classification, alpha=None):
    """Return the first deterministic compatible exact SL lift."""
    return recover_sl_solutions(challenge, tup, case, classification, alpha)[0]


def solve_tuple(challenge, case, pool, n, d, args, accept_candidate=None,
                deadline=None):
    if accept_candidate is None:
        accept_candidate = lambda candidate, _deadline: candidate
    if deadline is None and not args.exhaustive:
        deadline = time.monotonic() + args.budget
    try:
        _remaining_time(deadline)
    except SearchBudgetExpired:
        log(f"[search] INCONCLUSIVE after {args.budget}s")
        return None
    orders = [0] * d
    if d > 5:
        raise RuntimeError("the production closure format supports at most five generators")
    try:
        cl_rels, cl_orders = closure_relations(
            challenge, case, args.max_total, args.closure,
            cache_path=cache_file(args.cache_dir, challenge, "closure", case,
                                  args.max_total, "production"),
            deadline=deadline)
        _remaining_time(deadline)
    except SearchBudgetExpired:
        log(f"[search] INCONCLUSIVE after {args.budget}s")
        return None
    if cl_orders:
        orders = cl_orders[:d]
    rels = cl_rels + pool
    log(f"[closure] relations={len(cl_rels)} pool={len(pool)} orders={orders}")
    if args.target == "sl2_343":
        import psl2_343 as psl2
        psl_portfolio = whole_permutation_portfolio(rels, d, args.max_rules)
        log(f"[psl/matrix] relations={len(psl_portfolio)} "
            f"order-multiples={orders} "
            f"node-limit={'unbounded' if args.exhaustive else args.psl_node_limit} "
            f"budget={'unbounded' if args.exhaustive else str(args.budget) + 's'}")

        def accept(matrices):
            if any(psl2.word_element(u, matrices) != psl2.word_element(v, matrices)
                   for u, v in pool):
                return None
            permutations = [psl2.permutation(matrix) for matrix in matrices]
            if schreier_sims_order(permutations, psl2.DEGREE) != psl2.GROUP_ORDER:
                return None
            if args.exhaustive:
                certified, detail = check_complete_projective_rules(
                    challenge, matrices, case, args.henbane_sl_verify)
                if not certified:
                    log(f"[psl/matrix] complete-corpus rejection: {detail}")
                    return None
            candidate = [list(psl2.permutation(matrix)) for matrix in matrices]
            return _invoke_candidate(accept_candidate, candidate, deadline)

        fd, flat = tempfile.mkstemp(suffix=".flat")
        os.close(fd)
        write_matrix_flat(flat, d, psl_portfolio)
        try:
            matrix_workers = max(1, min(args.workers, 30))
            if matrix_workers != args.workers:
                log(f"[psl/matrix] capped workers at {matrix_workers} "
                    f"(requested {args.workers})")
            started_search = time.time()
            jobs = []
            accepted = None
            interrupted = False
            backend_errors = []
            try:
                for worker in range(matrix_workers):
                    try:
                        remaining = _remaining_time(deadline)
                    except SearchBudgetExpired:
                        interrupted = True
                        break
                    cmd = [
                        args.henbane_psl_matrix,
                        flat,
                        "-o", *map(str, orders),
                        "-b", str(-1 if args.exhaustive else args.psl_node_limit),
                        "--timeout", str(-1 if remaining is None else remaining),
                        "--rep-shard", str(worker), str(matrix_workers),
                        "--stop-after", str(0 if args.exhaustive
                                             else args.psl_candidates),
                    ]
                    stderr = tempfile.TemporaryFile(mode="w+")
                    try:
                        process = subprocess.Popen(
                            cmd, stdout=subprocess.PIPE, stderr=stderr,
                            start_new_session=True)
                    except BaseException:
                        stderr.close()
                        raise
                    if process.stdout is None:
                        stderr.close()
                        raise RuntimeError("failed to open PSL candidate pipe")
                    os.set_blocking(process.stdout.fileno(), False)
                    jobs.append({"process": process, "stdout": process.stdout,
                                 "stderr": stderr, "worker": worker,
                                 "checked": False, "stdout_buffer": b"",
                                 "stdout_eof": False, "candidates": 0,
                                 "status": None})
                while not interrupted and any(not job["checked"] for job in jobs):
                    try:
                        _remaining_time(deadline)
                    except SearchBudgetExpired:
                        interrupted = True
                        break
                    progressed = False
                    for job in jobs:
                        process = job["process"]
                        if job["checked"]:
                            continue
                        for line in _drain_candidate_stdout(job):
                            progressed = True
                            job["candidates"] += 1
                            matrices = _parse_psl_candidate(line, d, psl2)
                            if matrices is None:
                                continue
                            try:
                                accepted = accept(matrices)
                            except SearchBudgetExpired:
                                interrupted = True
                                break
                            if accepted is not None:
                                log(f"[psl/matrix] live candidate accepted "
                                    f"worker={job['worker']}")
                                break
                        if accepted is not None or interrupted:
                            break
                        if process.poll() is None:
                            continue
                        for line in _drain_candidate_stdout(job):
                            progressed = True
                            job["candidates"] += 1
                            matrices = _parse_psl_candidate(line, d, psl2)
                            if matrices is None:
                                continue
                            try:
                                accepted = accept(matrices)
                            except SearchBudgetExpired:
                                interrupted = True
                                break
                            if accepted is not None:
                                break
                        job["checked"] = True
                        job["stderr"].seek(0)
                        diagnostics = job["stderr"].read()
                        for line in diagnostics.splitlines():
                            if line.startswith("STATS"):
                                log(f"[psl/matrix] worker={job['worker']} "
                                    f"candidates={job['candidates']} {line}")
                        try:
                            job["status"] = _backend_status(
                                f"PSL worker {job['worker']}",
                                process.returncode, diagnostics)
                        except BackendFailure as error:
                            backend_errors.append(error)
                        if accepted is not None or interrupted:
                            break
                    if accepted is not None or interrupted:
                        break
                    if not progressed:
                        time.sleep(0.05)
            finally:
                _stop_psl_jobs(jobs, deadline=deadline)
            if accepted is not None:
                log(f"[psl/matrix] accepted in "
                    f"{time.time() - started_search:.1f}s")
                return accepted
            if backend_errors:
                raise BackendFailure("; ".join(map(str, backend_errors)))
            if interrupted:
                log(f"[psl/matrix] INCONCLUSIVE after {args.budget}s")
                return None
            statuses = [job["status"] for job in jobs]
            if args.exhaustive and any(status != "EXHAUSTED"
                                       for status in statuses):
                raise BackendFailure(
                    f"PSL exhaustive traversal ended with statuses {statuses}")
            if args.exhaustive:
                log("[psl/matrix] EXHAUSTED")
            return None
        finally:
            os.unlink(flat)

    portfolio = whole_permutation_portfolio(rels, d, args.max_rules)
    fd, flat = tempfile.mkstemp(suffix=".flat")
    os.close(fd)
    write_flat(flat, n, d, portfolio)
    parity = parity_pattern(portfolio, d)
    fact = 1
    for k in range(2, n + 1):
        fact *= k
    log(f"[henbane] relations={len(portfolio)} orders={orders} "
        f"workers={args.workers} budget={args.budget}s")
    try:
        parity_args = ["-p", *map(str, parity)] if parity is not None else []
        cmd = [args.henbane, flat, "-n", str(n), "-d", str(d),
               "-w", str(args.workers), "--all-candidates",
               "-o", *map(str, orders)] + parity_args
        t = time.time()
        stderr = tempfile.TemporaryFile(mode="w+")
        try:
            p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=stderr,
                                 start_new_session=True)
        except BaseException:
            stderr.close()
            raise
        if p.stdout is None:
            stderr.close()
            raise RuntimeError("failed to open symmetric candidate pipe")
        os.set_blocking(p.stdout.fileno(), False)
        job = {"stdout": p.stdout, "stdout_buffer": b"", "stdout_eof": False}
        candidates = 0
        accepted = None
        interrupted = False
        try:
            while True:
                try:
                    _remaining_time(deadline)
                except SearchBudgetExpired:
                    log(f"[henbane] INCONCLUSIVE after {args.budget}s")
                    interrupted = True
                    break
                for line in _drain_candidate_stdout(job):
                    candidates += 1
                    vals = line.split()
                    if len(vals) != d * n:
                        continue
                    try:
                        values = list(map(int, vals))
                    except ValueError:
                        continue
                    cand = [values[j * n:(j + 1) * n] for j in range(d)]
                    if not holds(cand, pool, n) or schreier_sims_order(
                            [tuple(row) for row in cand], n) != fact:
                        continue
                    if args.exhaustive:
                        certified, detail = check_complete_symmetric_rules(
                            challenge, cand, n, case,
                            args.henbane_symmetric_verify)
                        if not certified:
                            log(f"[henbane] candidate {candidates} rejected by "
                                f"complete corpus: {detail}")
                            continue
                    try:
                        accepted = _invoke_candidate(
                            accept_candidate, cand, deadline)
                    except SearchBudgetExpired:
                        log(f"[henbane] INCONCLUSIVE after {args.budget}s")
                        interrupted = True
                        break
                    if accepted is not None:
                        break
                if accepted is not None or interrupted or job["stdout_eof"]:
                    break
                timeout = 1.0
                if deadline is not None:
                    timeout = deadline - time.monotonic()
                    if timeout <= 0:
                        log(f"[henbane] INCONCLUSIVE after {args.budget}s")
                        interrupted = True
                        break
                    timeout = min(timeout, 1.0)
                select.select([p.stdout], [], [], timeout)
        finally:
            if (p.poll() is None and job["stdout_eof"]
                    and accepted is None and not interrupted):
                wait_timeout = 0.2
                if deadline is not None:
                    wait_timeout = min(
                        wait_timeout, max(0.0, deadline - time.monotonic()))
                try:
                    if wait_timeout:
                        p.wait(timeout=wait_timeout)
                except subprocess.TimeoutExpired:
                    pass
            if p.poll() is None:
                os.killpg(p.pid, signal.SIGTERM)
                wait_timeout = 10.0
                if deadline is not None:
                    wait_timeout = min(
                        wait_timeout, max(0.0, deadline - time.monotonic()))
                try:
                    if wait_timeout:
                        p.wait(timeout=wait_timeout)
                except subprocess.TimeoutExpired:
                    pass
                if p.poll() is None:
                    os.killpg(p.pid, signal.SIGKILL)
                    p.wait()
            else:
                p.wait()
            p.stdout.close()
            stderr.seek(0)
            diagnostics = stderr.read()
            stderr.close()
        for line in diagnostics.splitlines():
            log(line)
        if accepted is not None:
            mode = "complete" if args.exhaustive else "bounded"
            log(f"[henbane] {mode} candidate {candidates} accepted in "
                f"{time.time() - t:.3f}s")
            return accepted
        if not interrupted:
            status = _backend_status("symmetric backend", p.returncode,
                                     diagnostics)
            if args.exhaustive and status != "EXHAUSTED":
                raise BackendFailure(
                    f"symmetric exhaustive traversal ended with status {status}")
        if args.exhaustive and not interrupted:
            log(f"[henbane] EXHAUSTED after {candidates} portfolio survivors")
        else:
            log(f"[henbane] no certified solution in {time.time() - t:.1f}s")
    finally:
        os.unlink(flat)
    return None


def main():
    ap = argparse.ArgumentParser(description="Solve an instance with henbane.")
    ap.add_argument("challenge")
    ap.add_argument("-n", type=int,
                    help="solve in S_n; omit for the SL(2,343) target")
    ap.add_argument("-w", "--workers", type=int,
                    default=min(os.cpu_count() or 1, 30))
    ap.add_argument("--budget", type=int, default=3600,
                    help="end-to-end wall budget (s)")
    ap.add_argument("--exhaustive", action="store_true",
                    help="uncapped search with complete-corpus certification")
    ap.add_argument("--cache-dir", default=os.path.join(HERE, ".henbane-cache"),
                    help="persistent preprocessing cache (empty disables)")
    ap.add_argument("--out", help="write the recovered tuple json here")
    a = ap.parse_args()
    if a.workers < 1:
        ap.error("--workers must be positive")
    if not a.cache_dir:
        a.cache_dir = None
    a.max_rules = 3500
    a.max_total = 18
    a.closure = os.path.join(HERE, "build", "closure")
    a.henbane = os.path.join(HERE, "build", "henbane")
    a.henbane_symmetric_verify = os.path.join(
        HERE, "build", "henbane-symmetric-verify")
    a.preprocessor = os.path.join(HERE, "build", "preprocess")
    a.psl_node_limit = 10_000_000
    a.henbane_psl_matrix = os.path.join(HERE, "build", "henbane-psl-matrix")
    a.henbane_sl_verify = os.path.join(HERE, "build", "henbane-sl-verify")
    a.psl_candidates = 16
    a.target = "symmetric" if a.n is not None else "sl2_343"
    n = a.n if a.n is not None else 344
    t0 = time.time()
    deadline = None if a.exhaustive else time.monotonic() + a.budget

    log(f"[read] preparing {os.path.basename(a.challenge)} ...")
    try:
        upper, lower, couplings, classification = prepare_inputs(
            a.challenge, a.preprocessor, poolcap=5000, coupcap=2000,
            cache_path=cache_file(a.cache_dir, a.challenge,
                                  "prepared", 5000, 2000),
            deadline=deadline)
    except SearchBudgetExpired:
        log(f"[FAIL] reconstruction inconclusive after {a.budget}s")
        sys.exit(1)
    two_copy = bool(couplings and upper and lower)
    if two_copy:
        case, pool = "upper", upper
        d = max(infer_dimension(upper, "upper", couplings, classification),
                infer_dimension(lower, "lower", couplings, classification))
        log(f"[read] two-copy: B-pool={len(upper)} A-pool={len(lower)} "
            f"couplings={len(couplings)} d={d}")
    else:
        pool = upper or lower
        case = "upper" if upper else "lower"
        d = infer_dimension(pool, case, classification=classification)
        log(f"[read] single-copy: pool={len(pool)} case={case} d={d}")
    if d < 1 or d > 26:
        log(f"[FAIL] inferred generator count D={d}, expected 1..26"); sys.exit(1)
    target_label = ("SL(2,343) via its PSL quotient"
                    if a.target == "sl2_343" else f"S_{n}")
    conv = ("permutations are 0-indexed image lists on {0,...,n-1}: "
            "generator g maps point i -> g[i]")
    def accept_lifts(tup, lift_case, deadline, alpha=None):
        _remaining_time(deadline)
        try:
            lift_solutions = recover_sl_solutions(
                a.challenge, tup, lift_case, classification, alpha=alpha)
        except ValueError as error:
            log(f"[class/sl] rejected: {error}")
            return None
        for candidate_labels, candidate_details in lift_solutions:
            _remaining_time(deadline)
            if a.exhaustive:
                certified, detail = check_complete_sl_lift(
                    a.challenge, candidate_details["generators"],
                    candidate_labels, a.henbane_sl_verify)
                if not certified:
                    log(f"[class/sl] rejected: {detail}")
                    continue
            return candidate_labels, candidate_details
        return None

    def accept_single(tup, deadline):
        payload = {"tup": tup, "labels": None, "sl_details": None}
        if a.target != "sl2_343":
            return payload
        lift = accept_lifts(tup, case, deadline)
        if lift is None:
            return None
        payload["labels"], payload["sl_details"] = lift
        return payload

    def accept_symmetric_beta(beta, deadline):
        recovered = []
        try:
            recovered, stats = recover_alpha(
                beta, couplings, lower, d=d,
                stop_after=None if a.exhaustive else 1)
            log(f"[alpha/domain] domains={stats.generator_domain_sizes} "
                f"cartesian={stats.cartesian_size}")
        except CouplingRecoveryError as error:
            log(f"[alpha/domain] unavailable: {error}")
        for alpha in recovered:
            if a.exhaustive:
                certified, detail = check_complete_symmetric_pair(
                    a.challenge, alpha, beta, n, a.henbane_symmetric_verify)
                if not certified:
                    log(f"[alpha/domain] rejected: {detail}")
                    continue
            return {"tup": beta, "alpha": alpha,
                    "labels": None, "sl_details": None}

        def accept_lower(independent, deadline):
            for alpha in symmetric_alignments(
                    independent, beta, couplings, lower,
                    stop_requested=(None if deadline is None else
                        lambda: time.monotonic() >= deadline)):
                if a.exhaustive:
                    certified, _detail = check_complete_symmetric_pair(
                        a.challenge, alpha, beta, n,
                        a.henbane_symmetric_verify)
                    if not certified:
                        continue
                return {"tup": beta, "alpha": alpha,
                        "labels": None, "sl_details": None}
            return None

        log("[alpha/align] reconstructing lowercase copy")
        return solve_tuple(
            a.challenge, "lower", lower, n, d, a,
            accept_candidate=accept_lower, deadline=deadline)

    def accept_projective_beta(beta, deadline):
        import psl2_343 as psl2

        beta_matrices = tuple(
            psl2.matrix_from_permutation(value) for value in beta)

        def accept_alpha(candidate):
            matrices = tuple(
                psl2.mcanonical(value) if len(value) == 4
                else psl2.matrix_from_permutation(value)
                for value in candidate)
            alpha = [list(psl2.permutation(value)) for value in matrices]
            if a.exhaustive:
                certified, detail = check_complete_projective_pair(
                    a.challenge, matrices, beta_matrices,
                    a.henbane_sl_verify)
                if not certified:
                    log(f"[alpha/psl] rejected: {detail}")
                    return None
            lift = accept_lifts(beta, "upper", deadline, alpha=alpha)
            if lift is None:
                return None
            labels, details = lift
            return {"tup": beta, "alpha": alpha,
                    "labels": labels, "sl_details": details}

        recovered = []
        try:
            recovered, stats = recover_alpha_psl(
                beta, couplings, lower, d=d,
                stop_after=None if a.exhaustive else a.psl_candidates)
            log(f"[alpha/psl] domains={stats.generator_domain_sizes} "
                f"cartesian={stats.cartesian_size}")
        except CouplingRecoveryError as error:
            log(f"[alpha/psl] unavailable: {error}")
        for alpha in recovered:
            payload = accept_alpha(alpha)
            if payload is not None:
                return payload

        def accept_lower(independent, deadline):
            for alpha in projective_alignments(
                    independent, beta, couplings, lower,
                    stop_requested=(None if deadline is None else
                        lambda: time.monotonic() >= deadline)):
                payload = accept_alpha(alpha)
                if payload is not None:
                    return payload
            return None

        log("[alpha/align] reconstructing lowercase quotient")
        return solve_tuple(
            a.challenge, "lower", lower, n, d, a,
            accept_candidate=accept_lower, deadline=deadline)

    if not two_copy:
        accept_candidate = accept_single
    elif a.target == "sl2_343":
        accept_candidate = accept_projective_beta
    else:
        accept_candidate = accept_symmetric_beta

    try:
        solution = solve_tuple(
            a.challenge, case, pool, n, d, a,
            accept_candidate=accept_candidate, deadline=deadline)
    except BackendFailure as error:
        log(f"[FAIL] backend failure: {error}")
        sys.exit(2)
    if solution is None:
        outcome = "exhausted" if a.exhaustive else "inconclusive"
        log(f"[FAIL] end-to-end reconstruction {outcome}")
        sys.exit(1)

    tup = solution["tup"]
    alpha = solution.get("alpha")
    labels = solution.get("labels")
    sl_details = solution.get("sl_details")
    log(f"[solve] certified; generates {target_label}")
    if sl_details is not None:
        log(f"[class/sl] rank={sl_details['rank']} "
            f"equations={sl_details['equations']} labels={len(labels)}")

    if two_copy:
        result = {"target": a.target, "n": n, "tuple": {"convention": conv,
                  "alpha_lowercase": {LO[i]: alpha[i] for i in range(d)},
                  "beta_uppercase": {UP[i]: tup[i] for i in range(d)}}}
    else:
        letters = LO[:d] if case == "lower" else UP[:d]
        result = {"target": a.target, "n": n, "tuple": {"convention": conv,
                  "generators": {letters[i]: tup[i] for i in range(d)}}}
    if labels is not None:
        result["labels"] = labels

    if a.target == "sl2_343":
        result["field_model"] = ("GF(7)[t]/(t^3-2); point indices 0..342 are "
                                 "base-7 coefficients and 343 is infinity")
    if sl_details is not None:
        result["sl2_343"] = sl_details
    if a.out:
        with open(a.out, "w") as output:
            json.dump(result, output)
        log(f"[out] wrote {a.out} (verify: python3 check_solution.py {a.challenge} {a.out})")
    else:
        print(json.dumps(result))
    log(f"[done] {os.path.basename(a.challenge)} in {time.time() - t0:.0f}s")


if __name__ == "__main__":
    main()
