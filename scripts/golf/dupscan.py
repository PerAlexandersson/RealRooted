import re, sys, os, collections
from lean_decl import declaration_starts, find_value_assignment
files=[]
for root,dirs,fs in os.walk('.'):
    if '.lake' in root or '.git' in root: continue
    for f in fs:
        if f.endswith('.lean'): files.append(os.path.join(root,f))
# collect declarations with their statement text (until := or ':= by')
decls=collections.defaultdict(list)
stmts=collections.defaultdict(list)
for path in files:
    lines=open(path, encoding='utf-8').read().split('\n')
    starts = dict(declaration_starts(lines))
    i=0
    while i < len(lines):
        m=starts.get(i)
        if m and m.group('kind') in ('theorem', 'lemma', 'def', 'abbrev') and m.group('name'):
            kind,name=m.group('kind'),m.group('name')
            # Gather a declaration, then split only at its value assignment.
            buf=[]
            j=i
            while j < len(lines) and j < i+40 and (j == i or j not in starts):
                buf.append(lines[j])
                if find_value_assignment('\n'.join(buf)) is not None: break
                j+=1
            assignment=find_value_assignment('\n'.join(buf))
            if assignment is None:
                print(f"warning: no declaration assignment within scan bound: {path}:{i+1} ({name})",
                    file=sys.stderr)
                i=j if j < len(lines) and j in starts else j+1
                continue
            text='\n'.join(buf)[:assignment]
            # normalize
            norm=re.sub(r'\s+',' ',text).strip()
            norm=re.sub(r'^(?:@\[[^\]]*\]\s*)?','',norm)
            # strip kind+name
            norm=norm[norm.index(name)+len(name):] if name in norm else norm
            decls[name].append((path,i+1))
            stmts[norm].append((name,path,i+1))
            i=j+1
        else:
            i+=1
print("=== duplicate declaration base-names (same short name in >1 file) ===")
short=collections.defaultdict(set)
for name,locs in decls.items():
    base=name.split('.')[-1]
    for p,l in locs: short[base].add((p,l,name))
cnt=0
for base,locs in sorted(short.items(), key=lambda kv:-len(kv[1])):
    if len(locs)>1 and len(set(p for p,_,_ in locs))>1:
        cnt+=1
        if cnt<=40:
            print(f"{base}: "+", ".join(f"{n} @{p}:{l}" for p,l,n in sorted(locs)))
print(f"...total {cnt} duplicated short names across files")
print()
print("=== identical statements (same type up to whitespace, >1 decl) ===")
c=0
for norm,locs in sorted(stmts.items(), key=lambda kv:-len(kv[1])):
    if len(locs)>1 and len(norm)>25:
        c+=1
        if c<=40:
            print(f"[{len(locs)}] {norm[:130]}")
            for n,p,l in locs[:6]: print(f"      {n} @ {p}:{l}")
print(f"...total {c} identical-statement groups")
