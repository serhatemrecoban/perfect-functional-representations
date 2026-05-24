import os, re, sys, json, shutil, subprocess
from pathlib import Path

pdfs = [
    'ISIT_2026__On_perfect_functional_representations___final_manuscript_ (3).pdf',
    'On_perfect_functional_representation__Extended_version_ (4).pdf',
]


def extract_with_python(pdf):
    errs = []
    for mod in ['pypdf', 'PyPDF2', 'fitz', 'pdfplumber']:
        try:
            if mod == 'pypdf':
                from pypdf import PdfReader
                r = PdfReader(pdf)
                return '\n'.join((p.extract_text() or '') for p in r.pages), 'pypdf'
            if mod == 'PyPDF2':
                import PyPDF2
                r = PyPDF2.PdfReader(pdf)
                return '\n'.join((p.extract_text() or '') for p in r.pages), 'PyPDF2'
            if mod == 'fitz':
                import fitz
                doc = fitz.open(pdf)
                return '\n'.join(page.get_text() for page in doc), 'fitz'
            if mod == 'pdfplumber':
                import pdfplumber
                out = []
                with pdfplumber.open(pdf) as doc:
                    for page in doc.pages:
                        out.append(page.extract_text() or '')
                return '\n'.join(out), 'pdfplumber'
        except Exception as e:
            errs.append(f'{mod}: {e}')
    return None, '; '.join(errs)


def extract(pdf):
    text, method = extract_with_python(pdf)
    if text and text.strip():
        return text, method
    for exe in ['pdftotext', 'mutool']:
        path = shutil.which(exe)
        if not path:
            continue
        try:
            if exe == 'pdftotext':
                txt = Path(pdf).with_suffix('.txt')
                subprocess.run([path, '-layout', pdf, str(txt)], check=True, capture_output=True)
                return txt.read_text(encoding='utf-8', errors='ignore'), 'pdftotext'
            if exe == 'mutool':
                res = subprocess.run([path, 'draw', '-F', 'txt', '-o', '-', pdf], check=True, capture_output=True)
                return res.stdout.decode('utf-8', errors='ignore'), 'mutool'
        except Exception:
            pass
    raise RuntimeError(f'No usable extractor for {pdf}; python extract errors: {method}')


def normalize(s):
    s = s.replace('\r', '\n')
    s = re.sub(r'-\n(?=[a-z])', '', s)
    s = re.sub(r'[ \t]+', ' ', s)
    s = re.sub(r'\n{3,}', '\n\n', s)
    return s


def find_items(text):
    # Capture numbered theorem-like items until the next item/section/reference-ish block.
    pat = re.compile(r'(?ms)^\s*((Definition|Lemma|Theorem|Proposition|Corollary|Remark)\s+(\d+)\.?\s*(?:\([^\n]*?\))?\s*.*?)(?=^\s*(?:Definition|Lemma|Theorem|Proposition|Corollary|Remark)\s+\d+\.?\s|^\s*[IVX]+\.\s|^\s*\d+\.\s|^\s*APPENDIX\b|^\s*Appendix\b|^\s*REFERENCES\b|\Z)')
    items = []
    for m in pat.finditer(text):
        full = m.group(1).strip()
        kind = m.group(2)
        num = m.group(3)
        full = re.sub(r'\n+', ' ', full)
        full = re.sub(r'\s{2,}', ' ', full).strip()
        items.append((kind, int(num), full))
    return items

for pdf in pdfs:
    text, method = extract(pdf)
    norm = normalize(text)
    Path(pdf + '.extracted.txt').write_text(norm, encoding='utf-8')
    items = find_items(norm)
    print('='*120)
    print(f'PDF: {pdf}')
    print(f'Extractor: {method}')
    print(f'Found items: {len(items)}')
    wanted = [(k,n,s) for (k,n,s) in items if (k=='Lemma' and n in [1,2,3]) or (k=='Theorem' and n in [1,2])]
    others = [(k,n,s) for (k,n,s) in items if (k,n) not in {(wk,wn) for wk,wn,_ in wanted}]
    print('-- TARGET RESULTS --')
    if wanted:
        for k,n,s in wanted:
            print(f'[{k} {n}] {s}')
    else:
        print('No target results matched by regex.')
    print('-- OTHER NUMBERED ITEMS --')
    for k,n,s in others:
        print(f'[{k} {n}] {s}')
