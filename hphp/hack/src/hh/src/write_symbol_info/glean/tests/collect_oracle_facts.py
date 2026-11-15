"""collect_oracle_facts.py FILES_LIST OUT.json [FILE...]: index the files with the OCaml
hh_single_type_check (in $HH_OCAML_BIN) and keep a sample of the facts of each predicate."""
import json, os, subprocess, sys, tempfile, glob, collections, concurrent.futures as cf
O = os.path.join(os.environ["HH_OCAML_BIN"], "hh_single_type_check")
files = [l.strip() for l in open(sys.argv[1])] + sys.argv[3:]
def one(f):
    d = tempfile.mkdtemp()
    subprocess.run([O, "--glean-index", d, os.path.basename(f)], cwd=os.path.dirname(f), capture_output=True, timeout=120)
    out = []
    for x in glob.glob(d + "/*"):
        out += json.load(open(x))
        os.remove(x)
    os.rmdir(d)
    return out
per = collections.defaultdict(list)
seen = set()
with cf.ThreadPoolExecutor(10) as ex:
    for preds in ex.map(one, files):
        for p in preds:
            name = p["predicate"]
            for fact in p["facts"]:
                k = json.dumps(fact["key"], sort_keys=True)
                # one fact per distinct set of keys used (shape), plus a few more
                shape = json.dumps(sorted(fact["key"].keys())) if isinstance(fact["key"], dict) else type(fact["key"]).__name__
                tag = (name, shape)
                if (tag not in seen or len(per[name]) < 25) and len(per[name]) < 60:
                    seen.add(tag)
                    per[name].append(fact)
res = [{"predicate": k, "facts": v} for k, v in sorted(per.items())]
json.dump(res, open(sys.argv[2], "w"), separators=(",", ":"))
print({k: len(v) for k, v in per.items()})
