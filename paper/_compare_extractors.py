import re, importlib.util
from pathlib import Path

pdfs = [
    'ISIT_2026__On_perfect_functional_representations___final_manuscript_ (3).pdf',
    'On_perfect_functional_representation__Extended_version_ (4).pdf',
]
mods = ['pypdf', 'PyPDF2', 'fitz', 'pdfplumber']


def extract(pdf, mod):
    if mod == 'pypdf':
        from pypdf import PdfReader
        r = PdfReader(pdf)
        return '\n'.join((p.extract_text() or '') for p in r.pages)
    if mod == 'PyPDF2':
        import PyPDF2
        r = PyPDF2.PdfReader(pdf)
        return '\n'.join((p.extract_text() or '') for p in r.pages)
    if mod == 'fitz':
        import fitz
        doc = fitz.open(pdf)
        return '\n'.join(page.get_text() for page in doc)
    if mod == 'pdfplumber':
        import pdfplumber
        out = []
        with pdfplumber.open(pdf) as doc:
            for page in doc.pages:
                out.append(page.extract_text() or '')
        return '\n'.join(out)
    raise ValueError(mod)

for pdf in pdfs:
    print('='*100)
    print('PDF', pdf)
    for mod in mods:
        if importlib.util.find_spec(mod) is None:
            print(f'--- {mod}: not installed')
            continue
        try:
            text = extract(pdf, mod)
            text = text.replace('\r', '\n')
            text = re.sub(r'-\n(?=[a-z])', '', text)
            text = re.sub(r'[ \t]+', ' ', text)
            print(f'--- {mod}: extracted {len(text)} chars')
            for label in ['Lemma 1', 'Lemma 2', 'Lemma 3', 'Theorem 1', 'Theorem 2']:
                m = re.search(rf'(?is)({re.escape(label)}\.?\s.*?)(?=\n\s*(?:Definition|Lemma|Theorem|Proposition|Corollary|Remark)\s+\d+\.?|\n\s*[IVX]+\.|\n\s*\d+\.|\Z)', text)
                if m:
                    s = re.sub(r'\s+', ' ', m.group(1)).strip()
                    print(f'{label}: {s[:1200]}')
                else:
                    print(f'{label}: NOT FOUND')
        except Exception as e:
            print(f'--- {mod}: ERROR {e}')
