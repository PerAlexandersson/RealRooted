import re, os, collections, hashlib
decl_re = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+)*(theorem|lemma)\s+([A-Za-z_0-9.\'!?]+)')
files=[]
for root,dirs,fs in os.walk('.'):
    if '.lake' in root or '.git' in root or '/comparator' in root: continue
    for f in fs:
        if f.endswith('.lean'): files.append(os.path.join(root,f))
bodies=collections.defaultdict(list)   # normalized full decl -> locations
proofs=collections.defaultdict(list)   # normalized proof only -> locations
for path in files:
    lines=open(path, encoding='utf-8').read().split('\n')
    starts=[i for i,l in enumerate(lines) if decl_re.match(l)]
    for k,i in enumerate(starts):
        end = starts[k+1] if k+1 < len(starts) else len(lines)
        # trim trailing blank/comment lines
        blk=lines[i:end]
        while blk and (blk[-1].strip()=='' or blk[-1].lstrip().startswith('--') or blk[-1].lstrip().startswith('/-')):
            blk.pop()
        if len(blk) < 3: continue
        name=decl_re.match(lines[i]).group(2)
        text='\n'.join(blk)
        # split statement / proof at first top-level ':='
        parts=text.split(':=',1)
        proof = parts[1] if len(parts)>1 else ''
        norm_all=re.sub(r'\s+',' ',text.replace(name,'NAME')).strip()
        norm_pf=re.sub(r'\s+',' ',proof).strip()
        bodies[norm_all].append((name,path,i+1,len(blk)))
        if len(norm_pf) > 120:
            proofs[norm_pf].append((name,path,i+1,len(blk)))
print("=== identical full declarations (name-insensitive) ===")
n=0
for k,v in sorted(bodies.items(), key=lambda kv:-len(kv[1])):
    if len(v)>1:
        n+=1
        if n<=25:
            print(f"[{len(v)}x, {v[0][3]} lines] {k[:100]}")
            for nm,p,l,_ in v: print(f"     {nm} @ {p}:{l}")
print(f"total {n} groups")
print()
print("=== identical proof bodies (>120 chars, different statements) ===")
n=0; saved=0
for k,v in sorted(proofs.items(), key=lambda kv:-(len(kv[1])*kv[1][0][3])):
    if len(v)>1:
        n+=1; saved += (len(v)-1)*v[0][3]
        if n<=25:
            print(f"[{len(v)}x, {v[0][3]} lines each] proof: {k[:90]}")
            for nm,p,l,_ in v: print(f"     {nm} @ {p}:{l}")
print(f"total {n} groups, ~{saved} duplicated lines")
