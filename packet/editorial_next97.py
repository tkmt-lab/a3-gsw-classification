"""Pure editorial invariants shared by the manuscript and detached checks."""
import hashlib
import re

ENVIRONMENTS=['definition','theorem','lemma','proposition','corollary','equation','proof']

def preservation(old,new,a3=False):
    result={}
    for env in ENVIRONMENTS:
        pat=r'\\begin\{'+env+r'\}.*?\\end\{'+env+r'\}'
        before=re.findall(pat,old,re.S);after=re.findall(pat,new,re.S)
        assert before==after, 'mathematical block changed: '+env
        result[env]=len(before)
    before=re.findall(r'\\\[.*?\\\]',old,re.S)
    assert before==re.findall(r'\\\[.*?\\\]',new,re.S),'displayed mathematics changed'
    result['display_math']=len(before)
    ids=re.findall(r'\\claimid\{([^}]+)\}',old)
    assert ids==re.findall(r'\\claimid\{([^}]+)\}',new),'claim IDs/order changed'
    assert len(ids)==len(set(ids))==(57 if a3 else 18),'claim IDs'
    assert re.findall(r'\\tag\{[^}]+\}',old)==re.findall(r'\\tag\{[^}]+\}',new),'equation tags changed'
    if a3:
        start=r'\section{Objects and definitions}'
        before=old[old.index(start):old.index(r'\subsection{Kinds of evidence}')]
        after=new[new.index(start):new.index(r'\section{The classification}')]
        assert before==after,'prose definitions changed'
        locators=lambda s:set(re.findall(r'\\cite\[[^]]*\]\{[^}]+\}',s))
        assert locators(old)<=locators(new),'external citation locator changed'
        assert old.split(r'\begin{thebibliography}',1)[1]==new.split(r'\begin{thebibliography}',1)[1],'bibliography changed'
        result['prose_definition_sections']=1
        result['external_source_locators_unchanged']=True
    result.update(claim_ids=len(ids),byte_identical=True)
    return result

def lexical(text,a3=False):
    heading=r'\section*{Acknowledgements and AI-use statement}' if a3 else r'\section*{Authorship and AI assistance}'
    tail=text.split(heading,1)[1]
    ai=tail.split(r'\section*{License and contact}',1)[0] if a3 else tail.split(r'\begin{thebibliography}',1)[0]
    assert len(ai.strip().split('\n\n'))==1,'one AI-use paragraph'
    assert ai.count('Codex')==ai.count('Claude Code')==1,'AI names'
    s=text.replace(ai,'')
    patterns=dict(internal_names=r'R00[245]|\bcoordinator\b|\bClaude\b',
        trial_ids=r'\bT\d{4}\b',commit_ids=r'\b(?=[0-9a-f]{8,40}\b)(?=[0-9a-f]*[a-f])[0-9a-f]{8,40}\b',
        owner_history=r'\bowner(?:s|\x27s)?\b',delivery_terms=r'\b(?:received|receipts?|mailbox)\b')
    counts={k:len(re.findall(p,s)) for k,p in patterns.items()}
    assert not any(v for k,v in counts.items() if k!='delivery_terms'),'internal process marker in article'
    assert counts['delivery_terms']==(0 if a3 else 1),'delivery history outside protected theorem'
    if not a3:
        theorem=re.search(r'\\begin\{theorem\}.*?\\end\{theorem\}',s,re.S)[0]
        assert len(re.findall(patterns['delivery_terms'],theorem))==1
    assert text.count('VERIFICATION-RECORD.md')==1,'verification record reference count'
    assert text.index(r'\section{Introduction}')<text.index(r'\section{What is proved, and how}'),'front matter order'
    return dict(counts=counts,AI_tool_exceptions=['Codex','Claude Code'],
        protected_theorem_word_exception=[] if a3 else ['received (one occurrence in byte-preserved classification theorem)'],
        identifier_notes='Claim IDs/labels preserved. A3 AR/AT denote named belt constructions; the au_* arithmetic identifiers are fixed claim references, not workflow history.')

def syntax(s):
    stack=[]
    for m in re.finditer(r'\\(begin|end)\{([^}]+)\}',s):
        if m[1]=='begin':stack.append(m[2])
        else:assert stack and stack.pop()==m[2],'TeX environments'
    assert not stack
    labels=re.findall(r'\\label\{([^}]+)\}',s)
    assert len(labels)==len(set(labels)),'duplicate labels'
    assert set(re.findall(r'\\(?:ref|eqref)\{([^}]+)\}',s))<=set(labels),'unresolved refs'
    bib=set(re.findall(r'\\bibitem\{([^}]+)\}',s))
    assert {x.strip() for group in re.findall(r'\\cite(?:\[[^]]*\])?\{([^}]+)\}',s) for x in group.split(',')}<=bib,'unresolved citations'

def prose_words(text):
    text=re.sub(r'(?m)%.*$','',text)
    text=re.sub(r'\$.*?\$|\\\[.*?\\\]',' ',text,flags=re.S)
    text=re.sub(r'\\(?:label|claimid|ref|eqref|cite|record)\*?(?:\[[^]]*\])?\{[^}]*\}',' ',text)
    text=re.sub(r'\\[a-zA-Z]+\*?',' ',text)
    return len(re.findall(r"[A-Za-z]+(?:[-'][A-Za-z]+)*",text))
