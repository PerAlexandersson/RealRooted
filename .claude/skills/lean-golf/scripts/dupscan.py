import re, sys, os, collections
decl_re = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+)*(theorem|lemma|def|abbrev)\s+([A-Za-z_0-9.\'!?]+)')
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
    i=0
    while i < len(lines):
        m=decl_re.match(lines[i])
        if m:
            kind,name=m.group(1),m.group(2)
            # gather statement up to top-level ':=' or 'by'
            buf=[]
            j=i
            while j < len(lines) and j < i+40:
                buf.append(lines[j])
                if re.search(r':=', lines[j]): break
                j+=1
            text=' '.join(buf)
            text=text.split(':=')[0]
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
