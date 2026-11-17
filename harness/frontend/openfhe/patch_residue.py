#!/usr/bin/env python3
"""UNTRUSTED review aid: show what the tracer patch changes in OpenFHE OTHER than observation hooks.

  cd <openfhe checkout with the patch applied and committed>
  python3 patch_residue.py b59e1f29 HEAD

For every modified file, both versions are normalised (comments and whitespace removed, string
literals replaced by a hash, `IF_TRACE(...)`/`IF_TRACE_(...)` deleted, `REGISTER_IF_TRACE(t, x)` /
`REGISTER_IF_TRACE(x)` replaced by `x`) and the remaining differences are printed. With
ENABLE_TRACER=OFF those macros expand to nothing / to `x`, so a file printed as IDENTICAL compiles to
the same code with the tracer off; the residue of the other files is listed in README "Tracer patch".
"""
import re,subprocess,sys,difflib
files=subprocess.check_output(["git","diff","--name-only","--diff-filter=M",sys.argv[1],sys.argv[2]],text=True).split()
def match(s,i):
    d=1;j=i
    while d:
        c=s[j]
        if c=="(":d+=1
        elif c==")":d-=1
        j+=1
    return j
def strip_macro(s,name,keeplast):
    out="";pos=0
    pat=re.compile(r"\b"+name+r"\(")
    while True:
        m=pat.search(s,pos)
        if not m: out+=s[pos:];break
        j=match(s,m.end())
        inner=s[m.end():j-1]
        rep=""
        if keeplast:
            dd=0;parts=[];cur=""
            for ch in inner:
                if ch in "([{":dd+=1
                if ch in ")]}":dd-=1
                if ch=="," and dd==0: parts.append(cur);cur=""
                else: cur+=ch
            parts.append(cur);rep=parts[-1]
        out+=s[pos:m.start()]+rep;pos=j
        if not keeplast and pos<len(s) and s[pos]==";": pos+=1
    return out
import hashlib
def norm(s):
    s=re.sub(r'"(?:[^"\\\n]|\\.)*"',lambda m:'"S'+hashlib.md5(m.group(0).encode()).hexdigest()[:8]+'"',s)
    s=re.sub(r"//[^\n]*","",s)
    s=re.sub(r"/\*.*?\*/","",s,flags=re.S)
    s=strip_macro(s,"REGISTER_IF_TRACE",True)
    s=strip_macro(s,"IF_TRACE_",False)
    s=strip_macro(s,"IF_TRACE",False)
    s=re.sub(r"\s+","",s)
    return [x for x in re.split(r"(?<=[;{}])",s) if x]
for f in files:
    a=subprocess.run(["git","show",f"{sys.argv[1]}:{f}"],capture_output=True,text=True).stdout
    b=subprocess.run(["git","show",f"{sys.argv[2]}:{f}"],capture_output=True,text=True).stdout
    na,nb=norm(a),norm(b)
    if na==nb: print("IDENTICAL modulo hooks/comments/whitespace:",f); continue
    print("DIFFERS:",f)
    for l in difflib.unified_diff(na,nb,lineterm="",n=1):
        print("   ",l[:300])
