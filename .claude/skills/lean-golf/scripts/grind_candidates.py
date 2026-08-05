import re, os, collections, json
decl_re = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+)*(theorem|lemma)\s+([A-Za-z_0-9.\'!?]+)')
SAFE = {'rw','simp','simp_all','simp_arith','unfold','constructor','exact','refine','intro','intros',
        'ring','ring_nf','positivity','lia','norm_num','by_cases','field_simp','subst','push_cast',
        'linarith','nlinarith','grind','show','change','have','apply','rcases','obtain','cases','omega','gcongr','calc'}
tac_re = re.compile(r'^\s*(?:·\s*)?([a-z_]+[a-z_0-9]*)')
cands=collections.defaultdict(list)
for root,dirs,fs in os.walk('RealRooted'):
    if '.lake' in root: continue
    for f in fs:
        if not f.endswith('.lean'): continue
        path=os.path.join(root,f)
        lines=open(path,encoding='utf-8').read().split('\n')
        starts=[i for i,l in enumerate(lines) if decl_re.match(l)]
        for k,i in enumerate(starts):
            end=starts[k+1] if k+1<len(starts) else len(lines)
            blk=lines[i:end]
            while blk and (blk[-1].strip()=='' or blk[-1].lstrip().startswith('--')): blk.pop()
            by=None
            for j,l in enumerate(blk):
                if l.rstrip().endswith(':= by'): by=j; break
            if by is None: continue
            body=[l for l in blk[by+1:] if l.strip()]
            if not (2 <= len(body) <= 6): continue
            # all tactic head words must be in SAFE, and no nested structure markers we can't judge
            heads=[]
            ok=True
            for l in body:
                m=tac_re.match(l)
                if not m: ok=False; break
                heads.append(m.group(1))
            if not ok: continue
            if not all(h in SAFE for h in heads): continue
            # skip proofs that already are a single grind
            if heads==['grind']: continue
            # skip if uses `set`, `induction`, sorry
            txt='\n'.join(body)
            if 'sorry' in txt or 'induction' in txt or 'nlinarith' in txt: continue
            cands[path].append({'name':decl_re.match(blk[0]).group(2),'line':i+1,'by_line':i+by+1,
                                'end_line':i+len(blk),'nbody':len(body),'heads':heads})
tot=sum(len(v) for v in cands.values())
print(f"candidate small tactic proofs: {tot}")
for p,v in sorted(cands.items(), key=lambda kv:-len(kv[1]))[:25]:
    print(f"{len(v):4d}  {p}")
json.dump(cands, open('/tmp/claude-1000/-workspace-lean-RealRooted/01b471d8-3520-4596-971c-040f66048312/scratchpad/cands.json','w'))
