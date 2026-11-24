#!/usr/bin/env python3
"""List local declarations reachable from the 13 textbook chapter entry points."""
from pathlib import Path
import re,json
ROOT = Path(__file__).resolve().parents[1]
chapters=[('数学语言、证明器与AI辅助证明','a:language-library'),('最终成立、邻域与滤子','sec:ch03-libraries'),('趋近关系与各类极限','sec:ch04-library-guide'),('极限运算与连续性','eng:continuous'),('实数完备性','sec:ch06-code'),('导数与局部线性化','eng:derivative-library'),('微分法则与优化','eng:07-library'),('泰勒与渐近关系','eng:08-library'),('积分与基本定理','eng:09-library'),('积分方法与反常积分','eng:10-library'),('级数与函数近似','eng:11-library'),('多元极限与全微分','a12:libraries'),('多重积分与工程积分','a13:libraries')]
rows=[];summary=[]
# Follow local Lean imports, and local Rocq Require declarations from chapter entries.
def deps(lang,p):
 s=p.read_text(encoding='utf-8-sig')
 names=[]
 if lang=='lean':
  for m in re.finditer(r'^import\s+([^\n]+)',s,re.M):names+=m[1].split('--')[0].split()
 else:
  for m in re.finditer(r'(?:From\s+([\w.]+)\s+)?Require\s+(?:Import|Export)\s+([\w.\s]+)\.',s):
   names+=[(m[1]+'.' if m[1] else '')+x for x in m[2].split()]
 return [ROOT/lang/(n.replace('.','/')+('.lean' if lang=='lean' else '.v')) for n in names if (ROOT/lang/(n.replace('.','/')+('.lean' if lang=='lean' else '.v'))).exists()]
def closure(lang,p,seen=None):
 seen=set() if seen is None else seen
 if p in seen:return seen
 seen.add(p)
 for d in deps(lang,p):closure(lang,d,seen)
 return seen
allmods=set()
for ch,(title,label) in enumerate(chapters,1):
 rec={'chapter':ch,'title':title,'label':label}
 for lang,ext in [('lean','lean'),('rocq','v')]:
  p=ROOT/lang/f'Textbook/Ch{ch:02}/All.{ext}';assert p.exists()
  files=closure(lang,p);allmods|=files
  decls=[]
  for f in sorted(files):
   if f.name in ['All.lean', 'All.v']:continue
   src=f.read_text(encoding='utf-8-sig')
   pattern=r'^(?:noncomputable\s+)?(?:def|abbrev|structure|theorem|lemma|Definition|Theorem|Lemma|Structure|Record)\s+([\w\u0080-\uffff.]+)'
   ns='; '.join(re.findall(r'^(?:namespace|Module)\s+(\w+)',src,re.M))
   for m in re.finditer(pattern,src,re.M):
    rows.append((ch,lang,str(f.relative_to(ROOT)).replace('\\','/'),m[1],ns))
    decls.append((f,m[1]))
  # Names in chapter's own Foundations module first; for earlier chapters use direct imported modules.
  direct=set(deps(lang,p))
  selected=[(f,n) for f,n in decls if f in direct]
  rec[lang]={'module_count':len(files),'declarations':len(decls),'selected':[(str(f.relative_to(ROOT/lang)).replace('\\','/'),n) for f,n in selected]}
 summary.append(rec)

# Full symbol inventory is searchable and records local module namespaces separately.
header='chapter\tlanguage\tsource\tname\tnamespace_or_module\n'
(ROOT/'docs/textbook-symbols.tsv').write_text(header+''.join('\t'.join(map(str,r))+'\n' for r in rows),encoding='utf-8',newline='\n')
print("Updated docs/textbook-symbols.tsv:", len(rows), "chapter-qualified declarations")

