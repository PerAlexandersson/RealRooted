import re, os, collections, hashlib, sys
from lean_decl import declaration_starts, find_value_assignment, value_assignment_end
files=[]
for root,dirs,fs in os.walk('.'):
    if '.lake' in root or '.git' in root or '/comparator' in root: continue
    for f in fs:
        if f.endswith('.lean'): files.append(os.path.join(root,f))
bodies=collections.defaultdict(list)   # normalized full decl -> locations
proofs=collections.defaultdict(list)   # normalized proof only -> locations
for path in files:
    lines=open(path, encoding='utf-8').read().split('\n')
    starts=list(declaration_starts(lines))
    for k,(i,match) in enumerate(starts):
        if match.group('kind') not in ('theorem', 'lemma') or not match.group('name'):
            continue
        end = starts[k+1][0] if k+1 < len(starts) else len(lines)
        # trim trailing blank/comment lines
        blk=lines[i:end]
        while blk and (blk[-1].strip()=='' or blk[-1].lstrip().startswith('--') or blk[-1].lstrip().startswith('/-')):
            blk.pop()
        if len(blk) < 3: continue
        name=match.group('name')
        text='\n'.join(blk)
        # split statement / proof at first top-level ':='
        assignment=find_value_assignment(text)
        if assignment is None:
            print(f"warning: no declaration assignment in block: {path}:{i+1} ({name})",
                file=sys.stderr)
            continue
        proof = text[value_assignment_end(text, assignment):]
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
