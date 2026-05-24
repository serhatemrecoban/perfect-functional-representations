from pathlib import Path
labels = ['Lemma 1','Lemma 2','Lemma 3','Theorem 1','Theorem 2','Definition 1','Definition 2','Definition 3','Definition 4','Corollary 1','Lemma 4','Lemma 5','Lemma 6','Lemma 7','Remark 1','Remark 2']
fn = 'On_perfect_functional_representation__Extended_version_ (4).pdf.extracted.txt'
lines = Path(fn).read_text(encoding='utf-8', errors='ignore').splitlines()
print(fn)
for label in labels:
    hits = [i for i,l in enumerate(lines) if label in l]
    if not hits:
        continue
    i = hits[0]
    print('='*100)
    print(label, 'line', i+1)
    for j in range(max(0, i-2), min(len(lines), i+25)):
        print(f'{j+1:04d}: {lines[j]}')
