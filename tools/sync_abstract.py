"""Synchronize the exact arXiv abstract on all five manuscript surfaces.

Run without arguments to update, or --check to verify without writing.
Mathematics retains its TeX spelling on every surface.
"""
from pathlib import Path
import json,re,sys
ROOT=Path(__file__).resolve().parents[1]
def source():
 text=(ROOT/'paper/sections/00_front.tex').read_text(encoding='utf-8')
 match=re.search(r'\\begin\{abstract\}\s*(.*?)\s*\\end\{abstract\}',text,re.S)
 assert match,'Missing abstract';return ' '.join(match.group(1).split())
def main():
 abstract=source();assert len(abstract)<=1920
 check='--check' in sys.argv;bad=[]
 readme=ROOT/'README.md';text=readme.read_text(encoding='utf-8')
 match=re.search(r'\n\n(A quantum channel.*?)\n\nAll rates are optimal',text,re.S);assert match
 if match[1]!=abstract:
  bad.append('README.md')
  if not check:readme.write_text(text[:match.start(1)]+abstract+text[match.end(1):],encoding='utf-8',newline='\n')
 cff=ROOT/'CITATION.cff';text=cff.read_text(encoding='utf-8');match=re.search(r'^abstract: .*$',text,re.M);assert match
 try:current=json.loads(match[0].split(': ',1)[1])
 except json.JSONDecodeError:current=None
 if current!=abstract:
  bad.append('CITATION.cff')
  if not check:cff.write_text(text[:match.start()]+'abstract: '+json.dumps(abstract)+text[match.end():],encoding='utf-8',newline='\n')
 zen=ROOT/'.zenodo.json';data=json.loads(zen.read_text(encoding='utf-8'));match=re.match(r'<p>(.*?)</p>',data['description'],re.S);assert match
 if match[1]!=abstract:
  bad.append('.zenodo.json')
  if not check:
   data['description']='<p>'+abstract+'</p>'+data['description'][match.end():]
   zen.write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n',encoding='utf-8',newline='\n')
 arxiv=ROOT/'paper/abstract-arxiv.txt'
 if not arxiv.exists() or arxiv.read_text(encoding='utf-8').strip()!=abstract:
  bad.append('paper/abstract-arxiv.txt')
  if not check:arxiv.write_text(abstract+'\n',encoding='utf-8',newline='\n')
 if check and bad:raise SystemExit('Abstract mismatch: '+', '.join(bad))
 if not check:
  saved=re.search(r'^abstract: (.*)$',cff.read_text(encoding='utf-8'),re.M)
  assert json.loads(saved[1])==abstract
 print('Five abstract surfaces identical; '+str(len(abstract))+' characters (limit 1920).')
if __name__=='__main__':main()
