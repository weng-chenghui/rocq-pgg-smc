import os,subprocess,sys,time
HERE=os.getcwd()
LOCK=("/private/tmp/claude-501/-Users-cheng-huiweng-Projects-coq-rocq-pgg-smc"
      "/493d5ea4-6d9f-45fd-89c2-07339e63cb36/scratchpad/rocq1")
flags=[];files=[]
for raw in open("_CoqProject.one"):
    l=raw.strip()
    if not l or l.startswith("#"): continue
    if l.startswith("-arg "): flags+=[p for p in l.split() if p!="-arg"]
    elif l.startswith("-R ") or l.startswith("-Q "): flags+=l.split()
    else: files.append(l)
for rel in (sys.argv[1:] or files):
    t0=time.time()
    p=subprocess.run([LOCK,"1800","12000","rocq","compile"]+flags+["-time",rel],
                     cwd=HERE,capture_output=True,text=True)
    dt=time.time()-t0
    secs=[]
    for l in p.stdout.splitlines():
        if "secs" in l:
            try: secs.append(float(l.split("]")[1].split("secs")[0].strip()))
            except Exception: pass
    print("%-56s rc=%d wall %6.1f rocq %6.1f"%(rel,p.returncode,dt,sum(secs)))
    if p.returncode:
        print("\n".join([x for x in p.stderr.splitlines() if not x.startswith(("Warning","was ","to pgg","pgg_smc","/Users"))][-18:]))
        break
