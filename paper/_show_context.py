from pathlib import Path
import re
files = [
    'ISIT_2026__On_perfect_functional_representations___final_manuscript_ (3).pdf.extracted.txt',
    'On_perfect_functional_representation__Extended_version_ (4).pdf.extracted.txt',
]
labels = ['Lemma 1', 'Lemma 2', 'Lemma 3', 'Theorem 1', 'Theorem 2', 'Definition 1', 'Definition 2', 'Definition 3', 'Definition 4', 'Corollary 1', 'Lemma 4', 'Lemma 5', 'Lemma 6', 'Lemma 7', 'Remark 1', 'Remark 2']
for fn in files:
    print('='*120)
    print(fn)
    lines = Path(fn).read_text(encoding='utf-8', errors='ignore').splitlines()
    for label in labels:
        hits = [i for i,l in enumerate(lines) if label in l]
        if not hits:
            continue
        print('-'*80)
        print(label, 'first_hit_line', hits[0]+1)
        start = max(0, hits[0]-2)
        end = min(len(lines), hits[0]+18)
        for j in range(start, end):
            print(f'{j+1:04d}: {lines[j]}')
